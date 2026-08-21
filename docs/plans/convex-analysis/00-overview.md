# Plan: Convex Analysis (Rockafellar) — root plan

Source book: R. T. Rockafellar, *Convex Analysis*, Princeton, 1970. 8 parts, 39 sections,
236 theorems + 203 corollaries + 9 lemmas (448 numbered results).

This is the root of a tree of plans. Sub-plans:

| file | backbone area | book sections |
|---|---|---|
| [`01-foundations.md`](01-foundations.md) | extended-real convex functions, functional operations | §3–§5 |
| [`02-closure-duality.md`](02-closure-duality.md) | closure, separation, conjugacy, support functions, polars | §7, §11–§15 |
| [`03-relint-recession.md`](03-relint-recession.md) | relative interiors, recession, closedness criteria, dual operations | §6, §8–§10, §16 |
| [`04-representation.md`](04-representation.md) | Carathéodory, faces, polyhedral convexity, Helly | §17–§22 |
| [`05-differential.md`](05-differential.md) | subgradients, monotonicity, differentiability, Legendre | §23–§26 |
| [`06-optimization.md`](06-optimization.md) | minimisation, convex programs, adjoints, Fenchel duality | §27–§32 |
| [`07-saddle-algebra.md`](07-saddle-algebra.md) | saddle-functions, minimax, bifunction algebra, convex processes | §33–§39 |
| [`08-surface.md`](08-surface.md) | the Rockafellar surface library | §1–§39 |

---

## 1. What is actually missing from Mathlib

Surveyed against `mathlib4 @ v4.34.0-rc1`.

**Already present, to be reused (not re-proved):**

- Convex sets, `convexHull`, segments, `Convex.add`/`smul`/`linear_image`/`linear_preimage`/`prod`,
  `ConvexCone` (`Mathlib/Geometry/Convex/Cone/*`), `Analysis/Convex/{Basic,Combination,Hull,Segment}`.
- Real-valued convexity: `ConvexOn 𝕜 s f`, Jensen, `Analysis/Convex/{Function,Jensen,Slope,Deriv}`.
- Topology of convex sets: `Analysis/Convex/{Topology,Continuous}`, `intrinsicInterior` and
  `Set.Nonempty.intrinsicInterior` (finite-dimensional).
- Separation: `Analysis/LocallyConvex/Separation.lean` — the full `geometric_hahn_banach_*` family
  in topological vector spaces / locally convex spaces, plus `iInter_halfSpaces_eq`.
- Semicontinuity: `Topology/Semicontinuity/*`, incl. `lowerSemicontinuousOn_iff_isClosed_epigraph`.
- Finite-dimensional highlights: `Analysis/Convex/{Caratheodory,Radon,KreinMilman,Extreme,Exposed}`,
  `helly_theorem'` (finite families).
- Dual-pair infrastructure: `LinearMap.polar` (absolute polar), `WeakBilin` with
  `WeakBilin.locallyConvexSpace`, `Analysis/LocallyConvex/{WeakDual,Polar,WeakSpace}`.
- `EReal` as a `CompleteLinearOrder`, `AddCommMonoid`, `IsOrderedAddMonoid`, with `Neg`, `Sub`, `Mul`.

**Absent — this is the work:**

- **Extended-real-valued convex functions** as a theory (`E → EReal`): epigraph, effective domain,
  properness, improper functions.
- Functional operations: infimal convolution, convex hull of a family of functions, right scalar
  multiplication, images/preimages under linear maps, partial addition, inverse addition.
- Closure/lsc hull *of a convex function* with Rockafellar's `-∞` convention.
- **Convex conjugates and Fenchel–Moreau.** (Mathlib has no `Fenchel`, no `convexConjugate`.)
- Support functions, one-sided polars of cones and of sets, `EReal`-valued gauges.
- Recession cones `0⁺C` and recession functions `f0⁺`; closedness criteria for linear images.
- Relative-interior *calculus* (Mathlib has the object and non-emptiness, not the calculus of §6).
- **Subgradients** `∂f`, directional derivatives, subdifferential calculus, cyclic monotonicity.
- Polyhedral convexity (Minkowski–Weyl), Legendre transformation.
- Convex programs, Lagrangians, Kuhn–Tucker vectors, dual programs, Fenchel's duality theorem.
- Saddle-functions, minimax theorems, convex bifunctions, convex processes.

Two concrete Mathlib mismatches to be careful about:

- `LinearMap.polar` is the **absolute** polar `{y | ∀ x ∈ s, ‖B x y‖ ≤ 1}`. Rockafellar's polar is the
  **one-sided** `C° = {y | ∀ x ∈ C, ⟨x,y⟩ ≤ 1}` and `K° = {y | ∀ x ∈ K, ⟨x,y⟩ ≤ 0}`. They agree for
  balanced sets only. The backbone needs the one-sided version as a separate definition.
- `gauge s x : ℝ` returns `0` when `s` does not absorb `x` (`sInf ∅ = 0` in `ℝ`). Rockafellar's gauge
  is `+∞` there. The backbone needs an `EReal`-valued gauge; Mathlib's is the restriction to
  absorbing sets.

---

## 2. Design decisions

These are the choices that determine the shape of everything downstream. Each was checked to
typecheck against Mathlib before being written down.

### D1. Convex functions are `E → EReal`, and convexity means "the epigraph is convex"

```lean
/-- The epigraph of `f`, a subset of `E × ℝ` (Rockafellar §4: `μ` ranges over `ℝ`). -/
def epi (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

/-- Rockafellar's definition of a convex function. -/
def ConvexFn (f : E → EReal) : Prop := Convex ℝ (epi f)
```

Why `EReal` and not `ℝ ∪ {+∞}`: Rockafellar admits improper functions throughout, needs `-∞` for
concave conjugates and for saddle-function closures (§30, §34), and the identity `f** = cl f` is
stated so as to hold for improper `f` precisely so that Part VII works.

Why the epigraph and not the inequality: the inequality `f(ax+by) ≤ a·f x + b·f y` runs into `∞ − ∞`
as soon as `f` takes both infinities. Rockafellar says so explicitly and defines convexity
geometrically for this reason. The epigraph definition is convention-free.

**`EReal`'s conventions match Rockafellar's wherever Rockafellar defines them.** Verified in Lean:
`⊤ + ⊥ = ⊥`, `0 * ⊤ = 0`, `r + ⊤ = ⊤`, `r + ⊥ = ⊥`, `-⊥ = ⊤`, `r - ⊤ = ⊥`, `⨆ over ∅ = ⊥`.
Rockafellar leaves `∞ − ∞` undefined and avoids it by properness hypotheses; `EReal` picks `⊥`,
which is never observed under those hypotheses. So no custom arithmetic type is needed.

**Note the `E × ℝ`, not `E × EReal`.** Mathlib's `ConvexOn.convex_epigraph` uses
`{p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}` with `β` the codomain; for `β = EReal` that is a *different*
set (it contains points with second coordinate `⊤`). The bridge lemma to Mathlib is

```lean
theorem convexOn_iff_convexFn (s : Set E) (f : E → ℝ) :
    ConvexOn ℝ s f ↔ ConvexFn (fun x => if x ∈ s then (f x : EReal) else ⊤)
```

and must be proved early; it is what lets the surface layer reuse Mathlib's real-valued results.

### D2. Concave functions get their own definitions, tied to convex ones by negation

Rockafellar mirrors every convention (`epi g` is the hypograph, `cl g` is the usc hull,
`g*(y) = inf_x {⟨x,y⟩ − g(x)}`), and warns that `g* ≠ −(−g)*` — in fact `g*(y) = −(−g)*(−y)`.
Parts VI–VIII mix the two constantly, so the backbone defines `ConcaveFn`, `hypo`, `clConcave`,
`concaveConj` outright and proves the sign-transfer lemmas, rather than forcing every statement
through `-g`. `ConcaveFn g ↔ ConvexFn (-g)` is the defining lemma, not the definition's shape.

### D3. Duality is developed for a **dual pair**, not for `ℝⁿ` and not for the dual space

```lean
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Conjugate with respect to a bilinear pairing. -/
noncomputable def conj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : F → EReal :=
  fun y => ⨆ x : E, ((B x y : ℝ) : EReal) - f x
```

The biconjugate is `conj B.flip (conj B f) : E → EReal`, so the correspondence is symmetric without
reflexivity assumptions. Instantiations: `ℝⁿ` with the inner product (Rockafellar), a normed space
with `topDualPairing`, a Hilbert space with itself, `WeakBilin B` for the weak topology.

This is the level of generality at which Fenchel–Moreau is actually *easy*: `WeakBilin B` carries a
`LocallyConvexSpace` instance in Mathlib, so `geometric_hahn_banach_closed_point` applies directly.
Everything in §12–§16 is pairing-level; nothing there needs finite dimensions.

### D4. Reorder the development: **conjugacy comes before relative interiors**

Rockafellar's order is §6 (relative interiors) → §7 (closure) → §8, §9 → §11 (separation) →
§12 (conjugacy). But the true dependencies are different:

- Theorem 12.1 ("a closed convex function is the sup of the affine functions below it") needs only
  separation, i.e. §11.
- Theorem 7.4 ("`cl f` is proper when `f` is") is proved in the book via relative interiors, but in
  any locally convex space it follows from separation alone: a proper convex lsc function has an
  affine minorant.
- Relative interiors are needed only for the **exact**, closure-free forms of the duality formulas
  (§16, §23.8, §31) — i.e. as constraint qualifications, not as foundations.

So the backbone's logical order is

> §4/§5 (algebra) → §7 (closure, via separation) → §11 → §12–§15 (conjugacy, support, polars)
> → §6 (relative interiors, finite-dim) → §8/§9 (recession) → §16 (dual operations, exact forms)

This matters practically: it front-loads the highest-value, most reusable, dimension-free material
and pushes the finite-dimensional machinery to where it is genuinely required.

### D5. Constraint qualifications are an interface, not a hypothesis pattern

Almost every "exact" duality statement in the book has the shape

> *if `ri (dom f₁) ∩ … ∩ ri (dom fₘ) ≠ ∅` then the closure operation can be dropped and the infimum
> is attained.*

(Theorems 16.3, 16.4, 16.5, 20.1, 23.8, 23.9, 31.1, 38.2, 38.4, 38.5, 39.5, 39.7 …) The `ri`
condition is one sufficient condition among several: polyhedral variants (§20), and — outside the
book — Attouch–Brezis/Rockafellar–Robinson conditions in Banach spaces. The backbone should name the
**conclusion** and prove sufficient conditions for it:

```lean
/-- `f` and `g` add exactly: the conjugate of the sum is the infimal convolution of the
conjugates, with the infimum attained. -/
structure IsExactSum (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) : Prop where
  conj_add : conj B (f + g) = infConv (conj B f) (conj B g)
  attained : ∀ y, ∃ y₁ y₂, y₁ + y₂ = y ∧ conj B (f + g) y = conj B f y₁ + conj B g y₂
```

with sufficient conditions proved separately:

- `IsExactSum.of_relint` — finite-dimensional, `ri (dom f) ∩ ri (dom g) ≠ ∅` (Rockafellar 16.4).
- `IsExactSum.of_polyhedral` — one of the two polyhedral (Rockafellar 20.1).
- `IsExactSum.of_continuousAt` — one function continuous at a point of the other's domain
  (not in Rockafellar; true in any TVS, cheap, and the condition most used in practice).

Then §23.8 (`∂(f+g) = ∂f + ∂g`), §31 (Fenchel duality) and §38 are consequences of `IsExactSum`,
each proved once. This is the README's "prefer interfaces over concrete implementations" applied to
the single most repeated hypothesis in the book. The analogous interface for images under linear
maps is `IsExactImage A f` (Theorem 16.3), whose sufficient conditions come from §9.

### D6. Homogenisation is a first-class operation

Rockafellar repeatedly passes to a cone one dimension up:

- the cone `K(C) = {(λ,x) | λ > 0, x ∈ λC} ⊆ ℝ × E` of a convex set (§2, §3, §6.8.1, §8.2, §9.6);
- the positively homogeneous convex function generated by `h` (§5), which is `cl` of a cone
  construction, and gives: gauges (§5, §15), recession functions (§8.5.2), the support function of
  a level set (§13.5), the two-step homogenisation of Theorem 14.4;
- `fλ` (right scalar multiplication), which is the `λ`-slice of that cone.

Making `hom : (E → EReal) → (ℝ × E → EReal)` a named backbone operation with its own API — rather
than re-deriving the cone by hand in each section — collapses a large amount of duplicated argument.
Concretely, `f0⁺ = (cl (hom f)) (0, ·)` and `fλ = (hom f) (λ, ·)`, and Theorem 8.5's limit formula
becomes an instance of Corollary 7.5.1 applied to `hom f`.

### D7. "Points and directions" are handled by homogenisation, not by an ad hoc definition

§17 and §18 speak of convex hulls of a set of *points and directions*, and of "generalized
`d`-dimensional simplices". Rather than introduce a sum type of points-and-directions, the backbone
works with a set `S ⊆ ℝ × E` inside the cone picture: elements with first coordinate `1` are points,
first coordinate `0` are directions. `conv S` is then the level-1 slice of `cone S`. Theorems 17.1,
18.3, 18.5, 19.1, 19.5 all become statements about cones, which is also how their proofs go.

### D8. Bifunctions are curried functions; the organizing operation is **partial conjugation**

A "convex bifunction from `E` to `X`" (§29) is by definition a function whose graph function
`E × X → EReal` is convex. There is no new type; `Bifunction E X := E → X → EReal` is a `abbrev`
and the content is in the operations. The unifying observation for Parts VI–VIII:

- Rockafellar's `⟨Fu, x*⟩ = (Fu)*(x*)` is the **partial conjugate in the second variable**;
- the Lagrangian `L(u*,x) = inf_u {⟨u*,u⟩ + (Fu)(x)}` is the **partial concave conjugate in the
  first variable**;
- `cl₁`, `cl₂` (§33–§34) are **partial closures**;
- the adjoint `F*` (§30) is the full conjugate of the graph function with a sign flip on the first
  factor.

So the backbone defines

```lean
noncomputable def partialConj₂ (B : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (f : E × X → EReal) : E × Y → EReal :=
  fun p => conj B (fun x => f (p.1, x)) p.2
```

and gets the saddle-function ↔ bifunction correspondence (§33), the Lagrangian theory (§28–§29),
adjoints and dual programs (§30) and the conjugate saddle-function theory (§37) as applications of
one operator plus Fenchel–Moreau. Rockafellar develops these four times over; the backbone should
develop them once.

### D9. Generality boundaries

| layer | assumption | what lives there |
|---|---|---|
| **A. algebraic** | `[AddCommGroup E] [Module ℝ E]` | §3, §4, §5, most of §2; conjugacy *algebra* with a pairing |
| **B. topological** | `E` a real TVS (`[TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]`) | §7 closure, lsc, part of §8, §10.1 |
| **C. locally convex** | `+ [LocallyConvexSpace ℝ E]` | §11 separation, §12–§15 Fenchel–Moreau and consequences |
| **D. finite-dimensional** | `+ [FiniteDimensional ℝ E]` (via a norm) | §6, §8 (closedness of `0⁺C`), §9, §10.2–10.9, §17–§22, §25, §26 |

`ri C ≠ ∅` for nonempty convex `C` is *false* in infinite dimensions, so §6 and everything genuinely
depending on it is layer D. Rockafellar's `ri`-flavoured constraint qualifications are handled by D5
so that the duality theorems themselves stay in layer C.

---

## 3. Module hierarchy

Backbone under `Tdaf/` mirroring Mathlib's paths (so that pieces can be upstreamed);
surface under `Tdaf/Surface/`.

```
Tdaf/
  Order/
    EReal.lean                        -- arithmetic/order lemmas EReal needs and Mathlib lacks

  Analysis/Convex/
    Epigraph.lean                     -- epi, dom, ConvexFn, Proper; Thm 4.1–4.3, 4.6; §4
    Indicator.lean                    -- indicator δ(·|C); sets ↔ functions
    Concave.lean                      -- ConcaveFn, hypo, sign-transfer API
    Homogeneous.lean                  -- positively homogeneous fns; Thm 4.7, 4.8
    Homogenize.lean                   -- hom f, fλ, cone of a convex set; §5, D6
    Operations/
      Basic.lean                      -- λ • f, f + g, sup, pointwise inf; Thm 5.1, 5.2, 5.5
      Epi.lean                        -- Thm 5.3 (function from a convex set in E × ℝ)
      InfConv.lean                    -- infimal convolution □; Thm 5.4
      Hull.lean                       -- conv {fᵢ}; Thm 5.6
      Image.lean                      -- A f, f A; Thm 5.7
      Partial.lean                    -- partial addition, inverse addition #; Thm 3.6–3.8, 5.8
    Lattice.lean                      -- complete lattice of convex functions
    Closure.lean                      -- cl f, closed convex functions; §7
    Separation.lean                   -- proper/strong separation; §11 (wraps Mathlib)
    Duality/
      Pairing.lean                    -- dual pairs, compatible topologies, weak lsc = lsc
      Conjugate.lean                  -- conj B f, Fenchel inequality, Fenchel–Moreau; §12
      Support.lean                    -- support functions; §13
      Polar.lean                      -- one-sided polar cone / polar set, EReal gauge; §14, §15
      Exact.lean                      -- IsExactSum / IsExactImage interfaces (D5)
      Ops.lean                        -- the dual-operations table; §16
    RelativeInterior.lean             -- ri calculus; §6                       [finite-dim]
    Recession/
      Cone.lean                       -- 0⁺C, lineality, rank; §8
      Function.lean                   -- f0⁺, recession/constancy/lineality of f; §8
      Closedness.lean                 -- Thm 9.1–9.8                          [finite-dim]
    Continuity.lean                   -- §10                                  [finite-dim]
    Caratheodory.lean                 -- §17 (points and directions)          [finite-dim]
    Face.lean                         -- faces, extreme/exposed points and directions; §18
    Polyhedral/
      Defs.lean                       -- polyhedral sets/functions, Minkowski–Weyl; §19
      Duality.lean                    -- polyhedral constraint qualifications; §20
    Helly.lean                        -- §21
    LinearInequalities.lean           -- §22 (elementary vectors, Tucker complementarity)
    Subgradient/
      Defs.lean                       -- f'(x;·), ∂f; §23.1–23.7
      Calculus.lean                   -- sum/chain rules; §23.8–23.10
      Monotone.lean                   -- cyclic monotonicity, maximality; §24
      Gradient.lean                   -- ∇f vs ∂f, a.e. differentiability; §25
      Legendre.lean                   -- Legendre transformation; §26
    Optimization/
      Minimum.lean                    -- §27
      Perturbation.lean               -- convex programs as bifunctions; §29
      Lagrangian.lean                 -- partial conjugation, Lagrangians; §28–§29
      Adjoint.lean                    -- adjoint bifunctions, dual programs; §30
      Fenchel.lean                    -- Fenchel's duality theorem; §31
      Maximum.lean                    -- §32
    Saddle/
      Defs.lean                       -- saddle-functions, cl₁/cl₂, equivalence classes; §33–§34
      Continuity.lean                 -- §35
      Minimax.lean                    -- saddle-points, minimax theorems; §36–§37
    Bifunction/
      Algebra.lean                    -- □, scalar mult, composition, ⟨f,g⟩; §38
      Process.lean                    -- convex processes; §39

  Surface/Rockafellar/
    Section01.lean … Section39.lean   -- one file per book section, statements verbatim
    Notation.lean                     -- δ(·|C), δ*(·|C), f0⁺, fλ, □, #, K°, C°
```

## 4. Backbone / surface split

**Backbone** gets: every definition and theorem whose statement survives generalisation, in the
weakest layer of D9 that supports it.

**Surface** gets:

- The `ℝⁿ`-specific *statements* of all 448 results, in Rockafellar's numbering and notation.
- Everything that is genuinely about coordinates: Tucker representations (§1), the Hessian criterion
  (Theorem 4.5), the nonnegative orthant, componentwise ordering, the geometric-mean and
  log-sum-exp examples (§4, §5, §8), the Tchebycheff norm (§5).
- The worked examples and conjugate tables of §12, §15, §26, §30, §31 — valuable as tests, but they
  are instances, not structure.
- **Ordinary convex programs** (§28) as an `(m+3)`-tuple `(C, f₀, …, f_m, r)`. The backbone has
  generalized convex programs (perturbation bifunctions); §28 is their most important instance and
  the place where a Kuhn–Tucker vector becomes a vector of Lagrange multipliers. The surface builds
  the bifunction of an ordinary program and derives §28 from §29–§30.
- §22's elementary-vector development, which Rockafellar himself flags as self-contained linear
  algebra used nowhere else.

The surface is expected to be thin for §2–§16 and §23–§27, and thicker for §1, §22, §28.

## 5. Order of work, and size

Estimated in "sections' worth of statements" (448 total).

| stage | modules | results | notes |
|---|---|---|---|
| 1 | `Order/EReal`, `Epigraph`, `Indicator`, `Concave`, `Homogeneous` | ~20 | foundation; no topology |
| 2 | `Operations/*`, `Homogenize`, `Lattice` | ~25 | §3, §5 |
| 3 | `Closure`, `Separation` | ~25 | first topology; layer B/C |
| 4 | `Duality/{Pairing,Conjugate}` | ~15 | **Fenchel–Moreau** — the keystone |
| 5 | `Duality/{Support,Polar}` | ~35 | §13–§15 |
| 6 | `RelativeInterior`, `Recession/*`, `Continuity` | ~60 | finite-dim machinery |
| 7 | `Duality/{Exact,Ops}` | ~20 | §16, exact duality |
| 8 | `Subgradient/*` | ~55 | §23–§26 |
| 9 | `Face`, `Polyhedral/*`, `Caratheodory`, `Helly`, `LinearInequalities` | ~75 | §17–§22 |
| 10 | `Optimization/*` | ~60 | §27–§32 |
| 11 | `Saddle/*`, `Bifunction/*` | ~60 | §33–§39 |

Stages 1–5 are the critical path: they are dimension-free, they are what Mathlib most conspicuously
lacks, and every later stage depends on them. Stage 6 is the largest block of genuinely hard,
genuinely finite-dimensional work and is the main risk (see §6 below).

## 6. Known hard points

1. **Theorem 9.1** (closedness of a linear image under a recession condition). Proof needs a nested
   sequence of compact sets; the finite-dimensional hypothesis is essential (it is the only place
   local compactness is used). Everything in §16's "closure can be omitted" clauses and §27's
   existence theorems rests on it. Plan: prove it exactly as Rockafellar does, via
   `0⁺Cε = {0} → Cε bounded → nested compacts have nonempty intersection`.
2. **Theorem 6.2** (`ri C ≠ ∅`). Mathlib already has this
   (`Set.Nonempty.intrinsicInterior`, requires `NormedAddCommGroup`/`NormedSpace`/`FiniteDimensional`).
   The rest of §6 (Theorems 6.5–6.9 and corollaries) is new and is a substantial amount of careful
   set-level work.
3. **Theorem 24.8/24.9** (cyclically monotone ⟺ subdifferential; maximality). The construction of `f`
   from a cyclically monotone `ρ` is a genuinely clever explicit supremum over cycles. Reference:
   Rockafellar, *Characterization of the subdifferentials of convex functions*, Pacific J. Math. 17
   (1966).
4. **Theorem 25.5** (a.e. differentiability). Needs a measure-zero argument on the set where a
   monotone function jumps; Mathlib has Rademacher-adjacent material
   (`Analysis/Calculus/Rademacher.lean`) that may shortcut this — worth checking before doing it by
   hand. Rockafellar's own proof goes through Theorem 25.4 and one-dimensional monotone functions.
5. **Theorem 19.1** (Minkowski–Weyl: polyhedral ⟺ finitely generated). Not in Mathlib. The standard
   proof is by Fourier–Motzkin elimination or by double polarity plus induction. This gates all of
   §19–§22 and the polyhedral refinements everywhere else.
6. **Theorem 34.4/34.5** (equivalence classes of closed saddle-functions determined by their
   kernels). The bookkeeping around four different closure operations (`cl₁`, `cl₂`, `cl₁cl₂`,
   `cl₂cl₁`) is the fussiest part of the book. Mitigation: D8 — build it on a single
   `partialConj`/`partialClosure` API with the sign symmetry made explicit.
7. **`EReal` ergonomics.** `EReal` lacks a `SMul ℝ EReal` instance and its `Sub` is
   `a + (-b)`; expect to need a small `Tdaf/Order/EReal.lean` of arithmetic lemmas
   (`sub_le_iff`, `iSup_sub`, `add_iSup` under sign conditions). Budget for this up front rather
   than accumulating ad hoc lemmas across files.

## 7. Status

Stage 1 is under way. Formalised so far, all compiling with no `sorry` and with
`#print axioms` showing only `propext`, `Classical.choice`, `Quot.sound`:

| module | contents |
|---|---|
| `Tdaf/Order/EReal.lean` | the arithmetic conventions of §4 checked against `EReal`; `le_coe_of_forall_lt`, `eq_bot_of_forall_le_coe`, `exists_real_btwn_of_lt_coe`, `exists_coe_of_ne_bot_of_lt_top` |
| `Tdaf/Analysis/Convex/Epigraph.lean` | `epi`, `dom`, `Proper`, `restrict`, `ConvexFn`; **Theorem 4.1**, **Theorem 4.2**, **Theorem 4.6** (both forms), convexity of `dom`, and the Mathlib bridge `convexOn_iff_convexFn` |
| `Tdaf/Analysis/Convex/Indicator.lean` | `indicatorFn`, `epi_indicatorFn`, `dom_indicatorFn`, `convexFn_indicatorFn`, `restrict_eq_add_indicatorFn` |

Confirmed by this first pass:

* `EReal` really is the right carrier — every one of Rockafellar's §4 conventions holds in Mathlib's
  `EReal`, and the `∞ - ∞` he leaves undefined never surfaces.
* The `E × ℝ` epigraph (rather than `E × EReal`) is the right choice, and the Mathlib bridge
  `convexOn_iff_convexFn` goes through in two lines via `ConvexOn.convex_epigraph`.
* Theorem 4.2's strict form is the right primitive: Theorem 4.1 and both halves of Theorem 4.6 are
  short consequences, and no proof in the file ever has to reason about `⊥ + ⊤`.

Next: `Concave.lean`, `Homogeneous.lean`, then `Operations/*` (stage 2).

## 8. Conventions

- Namespace: everything backbone under `Tdaf`, then Mathlib-style names
  (`Tdaf.ConvexFn`, `Tdaf.conj`, `Tdaf.subgradient`).
- Surface under namespace `Rockafellar`, with names `theorem_4_2`, `corollary_16_4_1`, etc., and a
  docstring quoting the book's statement.
- `EReal`-valued definitions carry no `'`-suffix; real-valued specialisations get `Real` in the name.
- Every backbone definition that has a Mathlib counterpart gets a bridge lemma
  (`convexOn_iff_convexFn`, `gauge_eq_toReal_egauge`, `polar_eq_of_balanced`, …), so that surface
  proofs can move freely between the two.
- Notation (`□`, `#`, `δ(·|C)`, `f0⁺`) is declared in the surface's `Notation.lean` and in scoped
  namespaces in the backbone, never globally.
