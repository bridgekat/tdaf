# Plan: Convex Analysis (Rockafellar) — root plan

Source book: R. T. Rockafellar, *Convex Analysis*, Princeton, 1970. 8 parts, 39 sections,
235 theorems + 217 corollaries + 9 lemmas (≈461 numbered results).

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

What the Mathlib survey established:

- Mathlib **does** have a minimax theorem — `Mathlib/Topology/Sion.lean` (Sion–von Neumann, with a
  saddle-point form). Reuse it for Corollary 37.6.2 rather than reproving it.
- Mathlib **does** have an `egauge`: `Mathlib/Analysis/Convex/EGauge.lean`, `ℝ≥0∞`-valued. Ours is
  renamed `gaugeFn` to avoid the clash.
- `EReal.sub_le_iff_le_add`, `le_sub_iff_add_le`, `sub_le_of_le_add` all exist already, with weaker
  disjunctive hypotheses than the versions this plan proposed to write.
- `IsCompact.convexHull` does **not** exist (only `Set.Finite.isCompact_convexHull`), so the compact
  case of Theorem 17.2 is genuinely new work.
- What is genuinely missing and is a *file*, not a handful of lemmas: `add_iSup` / `iSup_add` /
  `iSup_sub` / `mul_le_mul_left` for `EReal`. `conj` is a `⨆` of `· − f x`, so these are the
  workhorses of every conjugacy proof.
- Mathlib **does** have compatible-topology independence, in
  `Mathlib/Analysis/LocallyConvex/WeakSpace.lean`: the closure of a convex set is the same under any
  two locally convex topologies with the same continuous dual. The names are
  `Convex.toWeakSpace_closure`, `LinearMap.image_closure_of_convex` and
  `LinearEquiv.image_closure_of_convex`. No declaration in that file contains the word "compatible",
  so only a semantic search finds it — see `NOTES.md` gotcha 29.

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

### D0. Infinite dimensions cost hypotheses, not generality

The backbone works over topological vector spaces, and in that category the arrows are the
**continuous** linear maps. A discontinuous linear functional is not a morphism; a subspace that is
to behave like a finite-dimensional one has to be assumed **closed**. Both conditions are automatic
in finite dimensions, which is exactly why Rockafellar never writes them.

So when one of his statements fails here, the fix is essentially always to restore one of those two
hypotheses rather than to abandon the generalisation. Every instance found so far is of that shape:

| his statement | what it needs here |
|---|---|
| Theorem 7.4, "`cl f` is proper when `f` is" | `f` **closed** (`exists_affine_le_of_closed_proper`) |
| the branch in `cl f` | branch on `lscHull f`, i.e. on the **closed** object |
| Corollary 11.5.2, "`C ≠ ℝⁿ` lies in a half-space" | `closure C ≠ univ` |
| Corollary 11.7.3, the cone version | likewise |
| Theorem 16.3 and §30's adjoints | `A` **continuous**, and the transpose supplied as data |

This is the reading to apply to any further surprise, and it is why the discontinuous-functional
counterexample keeps recurring: it is simply the standard witness that a linear map need not be a
morphism.

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

**Caveat established by review.** `EReal` negation does *not* distribute over addition:
`-(⊥ + ⊤) = ⊤` while `(-⊥) + (-⊤) = ⊥`. Mathlib's `EReal.neg_add` carries two hypotheses. So every
sign-transfer lemma needs `≠ ⊥` / `≠ ⊤` side conditions, and they bite exactly at the improper
functions that §34 and Part VII are about. Put a single `EReal.neg_add`-shaped helper in
`Order/EReal.lean` so the conditions are uniform rather than rediscovered per file.

### D3. Duality is developed for a **dual pair**, not for `ℝⁿ` and not for the dual space

```lean
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Conjugate with respect to a bilinear pairing. -/
noncomputable def conj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : F → EReal :=
  fun y => ⨆ x : E, ((B x y : ℝ) : EReal) - f x
```

The biconjugate is `conj B.flip (conj B f) : E → EReal`, so the correspondence is symmetric without
reflexivity assumptions. Instantiations: `ℝⁿ` with the inner product (Rockafellar), a normed space
with `topDualPairing`, a Hilbert space with itself. (Not the weak topology — see below.)

**Whatever topology `E` already has.** The duality theorems hold in whatever topology `E` carries,
provided its continuous dual is the `F` side of the pairing. That is a hypothesis on the pairing,
not a change of type: `σ(E, F)` enters only as one instance among several — the coarsest compatible
topology, never the mechanism. The spelling follows Mathlib's `LinearMap.IsContPerfPair`, a
`Prop`-valued class whose second field uses the first, because our situation is the one that idiom
is for: a single pairing threaded through many results.

```lean
class IsContinuousPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Prop where
  continuous_left (B) (y : F) : Continuous fun x : E => B x y

def evalCLM (B) [IsContinuousPairing B] : F →ₗ[ℝ] StrongDual ℝ E

class IsCompatiblePairing (B) : Prop extends IsContinuousPairing B where
  surjective_eval (B) : Function.Surjective (evalCLM B)
```

The split is load-bearing, not tidiness. Statements about *closedness* of a conjugate, a support
function, a polar or a subdifferential need only the continuity half, and they are true in
topologies strictly finer than the compatible ones — take `E` Banach and `F = StrongDual ℝ E` with
its **norm** topology, where continuity holds and surjectivity fails (`E'' ⊋ E` for non-reflexive
`E`). Demanding the full class there would restrict the most standard example in the subject to the
weak-\* topology for no reason. Only Fenchel–Moreau and its consequences need surjectivity.

Both fields are trivial when `E` is paired with its **own** continuous dual, so Fenchel–Moreau holds
directly in the norm topology of a Banach space, in a Hilbert space, and in `ℝⁿ`. What the general
pairing is *for* is the freedom to let `E` and `F` be different spaces — which §30 (adjoint
bifunctions) and §33 (saddle-functions) genuinely need. It is not for the weak topology.

Everything in §12–§16 is pairing-level; nothing there needs finite dimensions.

**Two things the pairing does not give you, established by review.**

*There is no adjoint.* For `A : E →ₗ[ℝ] G` between spaces carrying arbitrary pairings, `Aᵀ` does not
exist — Mathlib's `LinearMap.adjoint` needs `RCLike` inner-product spaces and finite dimension, and
in general the transpose exists only if `A` is weakly continuous, in which case it is extra *data*.
So every statement using `Aᵀ` carries an adjoint-pair datum, in Mathlib's `LinearMap.IsAdjointPair`
shape:

```lean
variable (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F) (hA : ∀ x z, B' (A x) z = B x (A' z))
```

with constructors supplying `A'` in the inner-product and finite-dimensional instantiations. Named
once in `Duality/Pairing.lean` and threaded from there.

*Compatible-topology independence is a corollary, not a file.* The statement that `cl C` is the
same in every topology compatible with the pairing is **not** on the path to Fenchel–Moreau — that
and it is not new work:
`Mathlib/Analysis/LocallyConvex/WeakSpace.lean` has it as `Convex.toWeakSpace_closure` and
`LinearEquiv.image_closure_of_convex`. What was budgeted as `Duality/Compatible.lean` is a page of
corollaries specialising those to `epi f`, at layer C (Mathlib's version needs `RCLike 𝕜` and
`LocallyConvexSpace`, which is right — Mazur's theorem needs Hahn–Banach).

Mathlib's file also endorses the shape D3 arrived at, and says so in its docstring: *"we phrase
this in terms of linear maps between locally convex spaces, rather than creating two separate
topologies on the same space."* Its hypotheses

```lean
(he₁ : ∀ f : StrongDual 𝕜 F, Continuous (e.dualMap f))
(he₂ : ∀ f : StrongDual 𝕜 E, Continuous (e.symm.dualMap f))
```

are `IsCompatiblePairing`'s two fields in another notation: "these two topologies have the same
continuous dual",
carried as hypotheses on a map rather than bundled as a predicate on a topology.

### D4. Reorder the development: **conjugacy comes before relative interiors**

Rockafellar's order is §6 (relative interiors) → §7 (closure) → §8, §9 → §11 (separation) →
§12 (conjugacy). But the true dependencies are different:

- Theorem 12.1 ("a closed convex function is the sup of the affine functions below it") needs only
  separation, i.e. §11.
- Theorem 7.4 ("`cl f` is proper when `f` is") is **finite-dimensional and stays that way** — see
  the correction below.
- Relative interiors are needed only for the **exact**, closure-free forms of the duality formulas
  (§16, §23.8, §31) — i.e. as constraint qualifications, not as foundations.

**Why `clFn` branches on `lscHull f`.** A proper convex function need **not** have a continuous
affine minorant in a locally convex space, so Theorem 7.4 does not hold at layer C. If `g : E →ₗ[ℝ] ℝ` is a discontinuous linear functional then `ker g`
is dense, `closure (epi g) = univ`, and `lscHull g ≡ ⊥` — yet `g` is convex, finite everywhere and
proper. The consequence reached further than §7: with `f := g + δ(·|closedBall 0 1)` one gets
`conj B f ≡ ⊤` and `biconj B f ≡ ⊥ ≠ clFn f`, so a naive reading of §12 makes **Fenchel–Moreau
itself false**. Three things keep it true:

1. `clFn` branches on whether **`lscHull f`** takes `⊥`, not on whether `f` does — the standard
   Γ-regularization. This makes `biconj = clFn` unconditionally true, and for convex `f` in `ℝⁿ` it
   provably coincides with Rockafellar's definition, so surface fidelity is untouched. Proving that
   coincidence becomes a surface obligation.
2. The affine-minorant lemma is stated for **closed** proper convex `f`. In that form the argument is
   correct: the separating functional cannot be vertical because a functional `(y,0)` takes the same
   value at `(x₀,c)` and `(x₀, f x₀)`, and `x₀ ∈ dom f`.
3. Add the **dichotomy lemma** — *an lsc convex function taking `⊥` anywhere is `≡ ⊥`* — which is
   what replaces Theorem 7.2 outside finite dimensions and was missing entirely. True in any TVS.

The *ordering* conclusion below survives unchanged; only the justification did not.

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
conjugates, and the infimum is attained. -/
structure IsExactSum (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) : Prop where
  proper_left  : Proper f
  proper_right : Proper g
  exact_le : ∀ y, ∃ y₁ y₂, y₁ + y₂ = y ∧ conj B f y₁ + conj B g y₂ ≤ conj B (f + g) y
```

with `conj_add : conj B (f + g) = infConv (conj B f) (conj B g)` a *theorem* derived from
`exact_le` — the reverse inequality holds unconditionally, so stating both is redundant. Properness
is not decoration: without it the field is *unsatisfiable* when `dom f ∩ dom g = ∅`, since
`f + g ≡ ⊤` forces `conj B (f+g) ≡ ⊥` while conjugates of proper functions are never `⊥`. It also
hides an `∞ − ∞` inside `f + g`, which is the `Pi` `EReal` sum.

with sufficient conditions proved separately:

- `IsExactSum.of_relint` — finite-dimensional, `ri (dom f) ∩ ri (dom g) ≠ ∅` (Rockafellar 16.4).
- `IsExactSum.of_polyhedral` — one of the two polyhedral (Rockafellar 20.1).
- `IsExactSum.of_continuousAt` — one function continuous at a point of the other's domain
  (not in Rockafellar; true in any TVS, cheap, and the condition most used in practice).

Then §23.8 (`∂(f+g) = ∂f + ∂g`), §31 (Fenchel duality) and §38 are consequences of `IsExactSum`,
each proved once. This is the README's "prefer interfaces over concrete implementations" applied to
the single most repeated hypothesis in the book. The analogous interface for images under linear
maps is `IsExactImage` (Theorem 16.3), whose sufficient conditions come from §9 — and which carries
the adjoint-pair datum of D3, since the transpose is not a function of `A`.

**Placement (review finding C2).** `Duality/Exact.lean` holds the *interface* and its interface-only
consequences, and imports only `Duality/Conjugate` and `Operations/InfConv`. Each
`IsExactSum.of_*` is declared in the module that owns its hypothesis — `of_polyhedral` in
`Polyhedral/Duality.lean`, `of_continuousAt` in a layer-B file. `of_relint` turned out to own no
single hypothesis: it needs §6, §9 and §13 at once, so it has its own file,
`Duality/Relint.lean`, rather than living in `RelativeInterior.lean` as planned. Putting them all in `Exact.lean` would make `Polyhedral/Duality.lean` and
`Exact.lean` mutually importing, since §20's theorems *are* `IsExactSum` statements.

### D6. Homogenisation is a first-class operation

Rockafellar repeatedly passes to a cone one dimension up:

- the cone `K(C) = {(λ,x) | λ > 0, x ∈ λC} ⊆ ℝ × E` of a convex set (§2, §3, §6.8.1, §8.2, §9.6);
- the positively homogeneous convex function generated by `h` (§5), which is Theorem 5.3 applied to
  the cone generated by `epi h` — **no closure is taken**; Theorem 9.7 is precisely about when the
  closure may be interchanged. It gives: gauges (§5, §15), recession functions, the support function
  of a level set (§13.5), the two-step homogenisation of Theorem 14.4;
- `fλ` (right scalar multiplication), which is the `λ`-slice of that cone.

Making `hom : (E → EReal) → (ℝ × E → EReal)` a named backbone operation with its own API — rather
than re-deriving the cone by hand in each section — collapses a large amount of duplicated argument.
Concretely, `fλ = (hom f) (λ, ·)`, and for **closed proper** `f`, `f0⁺ = (cl (hom f)) (0, ·)` —
Corollary 8.5.2, which carries a closedness hypothesis and (unless `0 ∈ dom f`) is stated only for
`y ∈ dom f`. It is **Corollary 8.5.2**, not Theorem 8.5's `λ → ∞` limit formula, that becomes an
instance of Corollary 7.5.1 applied to `hom f`.

Note also that `hom f` is generated by the *level-1 lift* of `f` (`h (λ,x) = f x` if `λ = 1`, `⊤`
otherwise), not by `f` itself; the two operators are different and both occur in §5.

The advertised payoff — Corollary 8.5.2 as an instance of Corollary 7.5.1 applied to `hom f` — does
**not** close; see §9 below and the layer audit in `Recession/Function.lean`. Of what
`Homogenize.lean` builds, only `smulRight` has a consumer so far; `levelOneLift`, `hom`, `homCone`,
`homEpiCone` and `smulRightHom` await D7's points-and-directions form of Theorem 17.1 and the cone
half of Theorem 19.1 ([sub-plan 4](04-representation.md)). If §17–§19 turn out not to need them,
delete them rather than keep them on the strength of D6.

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

**What makes this work, and was missing (review finding B4).** The full conjugate on `U × X` needs a
pairing on `U × X` built from `Bu` and `Bx` *with a sign flip on the first factor*. Before any
`Optimization/` code, `Duality/Pairing.lean` must supply

```lean
def prodPairing (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    (U × X) →ₗ[ℝ] (V × Y) →ₗ[ℝ] ℝ
def negFst (B : (U × X) →ₗ[ℝ] (V × Y) →ₗ[ℝ] ℝ) : (U × X) →ₗ[ℝ] (V × Y) →ₗ[ℝ] ℝ
theorem conj_prodPairing : conj (prodPairing Bu Bx) = partialConj₁ Bu ∘ partialConj₂ Bx
```

and D8 must fix, in one table, the convention for each of the five operators — because there are
four different sign conventions in play and Rockafellar writes none of them down together:

| operator | variable | convex or concave | pairing sign |
|---|---|---|---|
| bracket, §33 | second | convex conjugate | `Bx` |
| Lagrangian, §28–29 | first | concave conjugate | `Bu` |
| adjoint `F*`, §30 | both | convex | `negFst (prodPairing Bu Bx)` |
| `cl₁`, §33–34 | first | concave closure | — |
| `cl₂`, §33–34 | second | convex closure | — |

All the `EReal` side conditions of D8 live in `conj_prodPairing`; it needs `a + ⨆ = ⨆ (a + ·)` for
real `a`, which is on the `Order/EReal.lean` list.

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

Everything under `Analysis/Convex/` lives in `namespace Tdaf.ConvexAnalysis`, so that a sibling
library — numerical linear algebra, per the repository `README.md` — may have its own `dom`, `conj`,
`restrict` and `Proper`. `Order/EReal.lean` stays in `Tdaf.EReal`: its lemmas are general-purpose
`EReal` facts with no convexity in them. Names in these plans are written as they appear *inside*
the topic namespace.

```
Tdaf/
  Order/
    EReal.lean                        -- arithmetic/order lemmas EReal needs and Mathlib lacks

  Analysis/Convex/
    Epigraph.lean                     -- epi, dom, ConvexFn, Proper; Thm 4.1–4.3, 4.6; §4
    Indicator.lean                    -- indicator δ(·|C); sets ↔ functions
    Concave.lean                      -- ConcaveFn, hypo, sign-transfer API
    Homogeneous.lean                  -- positively homogeneous fns; Thm 4.7, 4.8
    Homogenize.lean                   -- (after Operations/: needs ofEpi, smulRight) hom f, fλ, cone of a convex set; §5, D6
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
      Pairing.lean                    -- dual pairs, adjoint pairs, prodPairing/negFst
      Conjugate.lean                  -- conj B f, Fenchel inequality, Fenchel–Moreau; §12
      ConcaveConj.lean                -- concaveConj, the sign dictionary (D2); §12 mirrored, §30
      Support.lean                    -- support functions; §13
      Polar.lean                      -- one-sided polar cone / polar set, gaugeFn; §14, §15
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
| 5 | `Recession/{Cone,Function}` (defs, layer A/B), `Duality/{Support,Polar}` | ~45 | §13–§15; 13.3–13.5 need `f0⁺` |
| 6 | `RelativeInterior`, `Recession/Closedness`, `Continuity` | ~50 | finite-dim machinery |
| 7 | `Duality/{Exact,Ops}` | ~20 | §16, exact duality |
| 8 | `Subgradient/*` | ~55 | §23–§26 |
| 9 | `Face`, `Polyhedral/*`, `Caratheodory`, `Helly`, `LinearInequalities` | ~75 | §17–§22 |
| 10 | `Optimization/*` | ~60 | §27–§32 |
| 11 | `Saddle/*`, `Bifunction/*` | ~60 | §33–§39 |

`Order/EReal.lean` in stage 1 is a **file**, not a handful of lemmas: `add_iSup`, `iSup_add`,
`iSup_sub`, `mul_le_mul_left` for `EReal` exist nowhere in Mathlib, each needs `⊥`/`⊤` side
conditions, and `conj` is a `⨆` of `· − f x`, so every conjugacy proof consumes them.
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
   proof is by Fourier–Motzkin elimination or by double polarity plus induction — but note these
   are *different* proofs of the two directions, and that the crux is a third theorem: double
   polarity gives `K = K°°` only for **closed** cones, so "finitely generated ⇒ polyhedral" needs
   **"a finitely generated cone is closed"** first (Carathéodory-for-cones plus compactness).
   Homogenising to the non-cone case additionally needs `C ≠ ∅`. This gates all of §19–§22 and
   the polyhedral refinements everywhere else.
6. **Theorem 34.4/34.5** (equivalence classes of closed saddle-functions determined by their
   kernels). The bookkeeping around four different closure operations (`cl₁`, `cl₂`, `cl₁cl₂`,
   `cl₂cl₁`) is the fussiest part of the book. Mitigation: D8 — build it on a single
   `partialConj`/`partialClosure` API with the sign symmetry made explicit.
7. **`EReal` ergonomics.** `EReal` lacks a `SMul ℝ EReal` instance, its `Sub` is `a + (-b)`, and
   negation does not distribute over addition. `iSup_sub` / `add_iSup` / `iSup_add` are absent from
   Mathlib entirely. Budget `Tdaf/Order/EReal.lean` as real work up front.
8. **The dual of `E × ℝ`.** Mathlib does not decompose a continuous functional on `E × ℝ` into a
   horizontal part and a vertical coefficient; that is `exists_unique_dual_prod`, built by
   restricting along `ContinuousLinearMap.inl`/`inr`. §12 needs it twice and §13 again.
9. **§34's equivalence classes.** `dom₁`/`dom₂` for saddle-functions must be defined before anything
   in §34 can be stated at all; see sub-plan 7.

## 7. Status

The library compiles with no `sorry`, no warnings, and `#print axioms` showing only `propext`,
`Classical.choice`, `Quot.sound`. Progress is tracked by **section**; the stage table of §5 is only
the original size estimate.

| section | state |
|---|---|
| §2–§5 | done |
| §6 | done except Cor 6.8.1 and Thm 6.9; **Thm 6.7 done** (`Convex.relint_preimage`) |
| §7 | done except the `ri` half of Thm 7.6; **Thm 7.5 now has its `ri` form** (`ConvexFn.tendsto_lscHull_along_segment_relint`) |
| §8 | done (8.1–8.8) |
| §9 | **Thms 9.1–9.5 and Cors 9.1.1–9.1.3 done** (`Recession/Closedness.lean`); Thms 9.6–9.8 and Cors 9.2.1–9.2.2 not started — they need the convex cone generated by a set, and are scheduled with §15 |
| §10 | **Thm 10.1 done** (`Continuity.lean`, with the `ri`-to-`interior` chart Mathlib leaves as a `proof_wanted`); Thms 10.2–10.6 not started |
| §11–§13 | done, including **Thm 13.3** (`Recession/Conjugate.lean`, which is where §13 and §8 meet) |
| §14 | done up to Thm 14.5; §15 not started |
| §16 | **done** — `Duality/Exact.lean` (the D5 interfaces, the exact rows), `Duality/Ops.lean` (**Thms 16.1, 16.3, 16.4, 16.5**, unconditional rows plus `clFn` forms) and `Duality/Relint.lean` (**the `of_relint` constructors**, which populate both interfaces). Lemma 16.2 and Cor 16.2.1 are subsumed: they were the `ri`-to-recession bridge, and that bridge is now Thm 13.3 plus §6.4 inside the constructors |
| §17–§22 | not started |
| §23 | 23.1, 23.2, 23.3, 23.5 and corollaries done; 23.8, 23.9 and Cor 23.8.1 done (`Subgradient/Calculus.lean`); **23.4, 23.6, 23.7 not stated**; 23.10 blocked on `PolyhedralFn` (§19) |
| §24–§39 | not started, except `concaveConj` and its §12 mirror (`Duality/ConcaveConj.lean`), which §30–§31 need |

**The D5 interfaces are populated.** `Duality/Relint.lean` now proves `IsExactImage.of_relint`
(Theorem 16.3) and `IsExactSum.of_relint` (Theorem 16.4), so §16's exact rows, §23.8, §23.9 and
Cor 23.8.1 all have supplied instances and the whole chain §9 → §13 → §16 → §23 is closed. The two
constructors are pure assemblies: Thm 9.2 (images) or Cor 9.1.1 (sums), plus Thm 13.3 to turn a
recession hypothesis about `f*` into one about `dom f`, plus `eq_of_isMaxOn_of_mem_relint` /
`eq_zero_of_nonpos_of_mem_relint` from §6 to turn that into Rockafellar's `ri` condition.

**§9 is complete through Theorem 9.5.** Theorem 6.7 turned out to be its last missing
prerequisite — Theorem 9.5's closure formula is Theorem 6.7 applied to `epi g` — and the `ri` form
of Theorem 7.5 its second, since a sum of functions is no set operation on epigraphs and Theorem
9.3 has to be proved by segment limits. Theorems 9.6–9.8 are left with §15: they are the only §9
results that need the *convex cone generated by a set*, which nothing defines yet, and nothing in
§16, §23 or §27 asks for them.

Next, in dependency order: the rest of §10 (Cor 10.1.1, Thms 10.2–10.6, and
`IsExactSum.of_continuousAt`, the *other* sufficient condition for the D5 interfaces — valid in any
TVS and not needing finite dimensions). After that, §§17–22 — which also supply `of_polyhedral` —
and §§24–26.

| module | contents |
|---|---|
| `Tdaf/Order/EReal.lean` | §4's arithmetic conventions checked against `EReal`; order/negation/`⨆` helpers |
| `Analysis/Convex/Epigraph.lean` | `epi`, `dom`, `Proper`, `restrict`, `ConvexFn`; **Thms 4.1, 4.2, 4.6**; `dom_eq_fst_image_epi`; the Mathlib bridge |
| `Analysis/Convex/Indicator.lean` | `indicatorFn` and its epigraph/domain/convexity |
| `Analysis/Convex/Concave.lean` | `hypo`, `ConcaveFn`, `domConcave`, `ProperConcave`, `restrictConcave`; the §30 mirrors of 4.1/4.2/4.6; `concaveOn_iff_concaveFn` |
| `Analysis/Convex/Homogeneous.lean` | `PosHomogeneous`; Thm 2.6 for cones; **Thms 4.7, 4.8**, Cors 4.7.1–4.7.2 |
| `Analysis/Convex/Operations/Epi.lean` | `ofEpi`, `IsEpiLike` and its closure properties; **Thm 5.3** |
| `Analysis/Convex/Operations/Basic.lean` | `epi_iSup`; **Thms 5.1, 5.2, 5.5**; scalar multiples, restriction |
| `Operations/InfConv.lean` | `□` (**Thm 5.4**), the `AddCommMonoid` on `InfConvFn E` |
| `Operations/Hull.lean` | `convFn`, `convHullFn` (**Thm 5.6**, proved), the `GaloisCoinsertion` onto convex functions |
| `Operations/Image.lean` | `mapLin`/`compLin` (**Thm 5.7**), their `GaloisConnection`, partial minimisation |
| `Homogenize.lean` | `smulRight`, `levelOneLift`, `hom`, `homCone`, `homEpiCone` (D6) |
| `Closure.lean` | `lscHull`, `clFn`, `ClosedFn`, `ClosedProperConvexFn` (**§7** at layer B/C), incl. the Fenchel–Moreau keystone |
| `Lattice.lean` | the convex functions as a `CompleteLattice` (§5) |
| `Separation.lean` | §11 at layer C, plus the reusable non-vertical separation lemma |
| `Continuity.lean` | **Thm 10.1** — continuity on `ri (dom f)`, plus the linear chart that reduces `ri` to `interior` |
| `Recession/Cone.lean` | §8's set half, layered A/B/D |
| `Recession/Closedness.lean` | **Thms 9.1–9.5, Cors 9.1.1–9.1.3** — when a linear image is closed, and the closure of a sum, a supremum and a composition |
| `Recession/Conjugate.lean` | **Thm 13.3** — `(f*)0⁺ = δ*(· \| dom f)`, and `constancySpace_conj` |
| `Duality/Pairing.lean` | dual pairs, adjoint pairs, product pairings, the dual of `E × ℝ` |
| `Duality/Conjugate.lean` | **Theorems 12.1 and 12.2 — Fenchel–Moreau** |
| `Duality/Exact.lean` | `IsExactSum`/`IsExactImage` (D5); the unconditional halves of **Thms 16.3, 16.4** and the exact halves derived from the interfaces |
| `Duality/ConcaveConj.lean` | `concaveConj` (D2), the sign dictionary, §12 mirrored for concave functions |
| `Duality/Ops.lean` | the §16 dual-operations table — **Thms 16.1, 16.3, 16.4, 16.5**, unconditional halves plus the `clFn` forms |
| `Duality/Relint.lean` | **the `of_relint` constructors** — Rockafellar's own constraint qualification for **Thms 16.3 and 16.4**; the only file that *produces* a D5 interface |
| `RelativeInterior.lean` | §6, and **every result stages 2–3 deferred to it** |
| `Recession/Function.lean` | §8's function half — Theorems 8.5–8.8 |
| `Duality/Support.lean` | §13, with `supportEquiv` for the one-to-one correspondence |
| `Duality/Polar.lean` | §14 up to Theorem 14.5, polarity as a `GaloisConnection` |
| `Subgradient/Defs.lean` | §23 — the first subgradient anywhere in the Lean ecosystem |
| `Subgradient/Calculus.lean` | **Thms 23.8, 23.9**, Cor 23.8.1 — the sum and image rules, against the D5 interfaces |

None of `RelativeInterior.lean`'s outstanding results blocks anything. `Duality/Compatible.lean`,
budgeted as a file in §3, is a page of corollaries over Mathlib's `WeakSpace.lean`.

## 8. Open questions

* Whether Rockafellar ever uses an `∞ − ∞` convention locally in §16/§30 (some treatments take
  `∞ − ∞ = ∞` there). `EReal` picks `⊥`. This decides whether D5's side conditions are cosmetic.
* Whether `IsExactSum.of_continuousAt` is as cheap in a bare TVS as D5 assumes — a short spike would
  settle it.
* Whether `Mathlib/Analysis/Convex/Approximation.lean` and `Mathlib/Topology/Sion.lean` overlap §10
  and §35–§36 beyond the minimax theorem itself.
* **Upstreaming `Tdaf/Order/EReal.lean`.** Its thirty lemmas are general-purpose `EReal` facts with
  no convexity in them, and they are the clearest Mathlib gap this project found. There is no
  policy for them yet. Until there is: name each one as Mathlib would, so that a later upstream
  replaces it by deletion, and keep in mind that inside `namespace Tdaf` a local `EReal.foo` would
  silently shadow a future Mathlib `EReal.foo` (gotcha 34).

## 9. Corrections to Rockafellar and to this plan

Each of these was established while formalizing, and each is a statement about the mathematics
rather than about the book's exposition. Design decision D0 explains the recurring shape.

* `EReal` is the right carrier — every §4 convention holds in Mathlib's `EReal`, and the `∞ − ∞`
  Rockafellar leaves undefined never surfaces under the properness hypotheses.
* The `E × ℝ` epigraph (not `E × EReal`) is right, and `convexOn_iff_convexFn` goes through in two
  lines via `ConvexOn.convex_epigraph`.
* Theorem 4.2's strict form is the right primitive: 4.1, both halves of 4.6, and their concave
  mirrors are short consequences, and no proof ever has to reason about `⊥ + ⊤`.
* **`epi (ofEpi F) = F` needs a hypothesis** (`IsEpiLike`), and closedness alone does not supply it
  (`{(0,0)}` is closed and is not an epigraph). Consequently the §5 "operation = `ofEpi` of a set"
  identities are `rfl`, and the content-bearing epigraph identities are conditional.
* **Corollary 4.7.1 and Theorem 4.8's basis clause are false as literally written**, for the trivial
  reason that the book's `λ₁,…,λₘ` assumes `m ≥ 1`; the formalisation adds `Nonempty`.
* **Theorem 5.2 needs `∀ x, f x ≠ ⊥`, not properness**, and it is not droppable.
* **Theorem 5.1 needs `φ ⊤ = ⊤` explicitly**, and is stated more generally than the book (`φ` may
  take `⊥`).
* **D2's "generate the concave API by `simp`"** does not work: the natural simp set loops.
* **The dichotomy lemma must say "no finite values", not "identically `⊥`".** On `ℝ`, the function
  that is `⊥` at the origin and `⊤` elsewhere is convex and lower semicontinuous and takes `⊥`
  without being constant. Rockafellar's Corollary 7.2.1 says exactly "can have no finite values",
  and that is what generalises; the stronger "identically `⊥`" is false.
* **`□` is not associative by set `add_assoc`.** Since `epi (f □ g) ⊇ epi f + epi g` strictly, the
  outer convolution is not taken against the sum one started with; `epi_ofEpi_add_subset` is the
  bridge, and is needed whenever two `ofEpi`-defined operations compose.
* **The homogenisation cone is not the epigraph.** `homCone f` meets `λ = 0` only at the origin,
  while an epigraph contains the whole vertical ray: `epi (hom f) = homCone f ∪ {0} ×ˢ Ici 0`. D6's
  wording invited the wrong assumption. Also `hom` and `smulRight` need `dom f ≠ ∅` in several
  places that the plan never flagged.
* **Fenchel's inequality as §2.4 stated it is false.** `⟨x,y⟩ ≤ f x + f* y` fails at improper `f`,
  because `⊤ + ⊥ = ⊥`. The unconditional content is `⟨x,y⟩ - f x ≤ f* y`; the named inequality
  carries properness, which is Rockafellar's own wording.
* **Corollaries 11.5.2 and 11.7.3 are false at layer C** — the third instance of the
  discontinuous-functional counterexample. `C ≠ univ` does not give a closed half-space; the
  hypothesis is `closure C ≠ univ`.
* **Theorems 11.2 and 11.6 are not finite-dimensional**, contrary to §2.2; 11.6's full `iff` holds
  at layer C with `(interior C).Nonempty` for `ri C ≠ ∅`.
* **§3.2's layer table was too strong in five places.** Closedness of `0⁺ C`, Theorem 8.2,
  Theorem 8.3 and Corollaries 8.3.2–8.3.4 are all **layer B**; the lineality space and the
  direct-sum decomposition are **layer A**. Only Theorem 8.4 and Corollary 8.4.1 are layer D.
* **§2.4's proof plan omitted a case**: the vertical coefficient can be negative, zero *or
  positive*, and ruling out the third needs upward closedness of the epigraph.
* **`epi_recessionFn` needs no hypothesis at all**, not `ClosedFn f` as §3.3 specified. The stated
  reason — that `0⁺(epi f)` has closed vertical sections only when `epi f` is closed — is simply
  false: upward closure is monotonicity of `ν ↦ μ + aν`, and closure from below follows from
  `f(x + a•y) ≤ μ + aρ` for every `ρ > ν`. Most of §8 moves from layer D to layer A with it, and
  **Theorem 8.6 is layer A**, not layer D.
* **D6's `hom f` route does not reach Corollary 8.5.2**, and not for a technical reason: `hom f` is
  the wrong object. Rockafellar's `g` satisfies `(cl g)(0, y) = f0⁺(y)` whereas
  `hom f (0, y) = δ(y ∣ 0)`, and bridging needs `cl (hom f)`, hence the `cl K = K ∪ {0} × 0⁺C`
  formula that `Recession/Cone.lean` deliberately omits. The direct route is shorter even where the
  infrastructure exists. D6's payoff is real but lies downstream in §13.5 and §14.4, not inside §8.
* **Theorem 23.5 needs neither convexity nor properness** for conditions (a)–(c); only the passage
  to the additive equality (d) needs `Proper`, for the `⊤ + ⊥ = ⊥` reason. §5.1 overstated it.
* **Corollary 23.5.4 needs no closedness and no topology.** Rockafellar routes it through
  `δ(· ∣ K)* = δ(· ∣ K°)`, which needs `K` closed; putting `z = 0` and `z = x + x` into the
  subgradient inequality proves it for an arbitrary `PointedCone ℝ E`.
* **Corollary 13.2.2 is false as transcribed** — another D0 case. Rockafellar gets "finite ⇒ closed"
  from Corollary 7.4.2, which fails in infinite dimensions: a discontinuous linear functional is
  finite, convex, positively homogeneous and not a support function. `ClosedFn` must be assumed.
* **Theorem 14.1 needs `K.Nonempty`** (`∅° = F`, and `F°` is the pairing's kernel, not `∅`), and
  gives `cl K` rather than `K`. **Theorem 14.5 needs `0 ∈ C`**. §2.6's table said neither. Neither
  weakens to "surjectivity of the pairing, but not continuity": that is not expressible, because
  `surjective_eval` is a field of `IsCompatiblePairing`, whose statement goes through `evalCLM B`
  and so presupposes `IsContinuousPairing B`. `polarSet_polarSet` carries `[IsCompatiblePairing B]`
  and uses both halves — `geometric_hahn_banach_closed_point` for the topology, `exists_pairing_eq`
  for the surjectivity.
* **`concaveConj` belongs under `Duality/`, not in `Concave.lean`.** §6.4 of
  [sub-plan 6](06-optimization.md) assigned it to `Concave.lean`, but the concave conjugate needs a
  pairing, and `Concave.lean` is a layer-A file importing only `Epigraph.lean`. Putting it there
  would drag separation and Hahn–Banach into every future use of `hypo` or `ConcaveFn`. It is
  `Duality/ConcaveConj.lean`, which imports `Concave.lean` and `Duality/Conjugate.lean`.
* **Fenchel's inequality for *concave* functions needs no properness**, unlike its convex mirror.
  `⟨x, y⟩ ≤ f x + f* y` fails at improper `f` because the right-hand side collapses to
  `⊤ + ⊥ = ⊥`; the concave form `g x + g*(y) ≤ ⟨x, y⟩` puts that same collapse on the *smaller*
  side, where `⊥` is harmless. Sign transfer reverses the order but not the arithmetic, and
  `⊤ + ⊥ = ⊥` is not self-dual — so D2's "every statement mirrors" needs checking case by case, not
  assuming.
* **The `IsExactSum` interface is self-policing.** Properness of the two summands plus attainment
  already forces `Proper (f + g)` (`IsExactSum.proper_add`), so the interface is unsatisfiable when
  the effective domains miss each other. D5 predicted the unsatisfiability of the *equality* form;
  the structure form turns it into a usable lemma instead.
* **`Duality/Exact.lean` imports `Operations/Image.lean` as well.** §3.6 of
  [sub-plan 3](03-relint-recession.md) listed only `Duality/Conjugate` and `Operations/InfConv`, but
  `IsExactImage` is stated with `mapLin`/`compLin`.
* **`∂δ(· ∣ C) x = N_C(x)` is false off `C`**: with the pointed-cone definition `0 ∈ N_C(x)` always,
  while `∂δ(· ∣ C) x = ∅` for `x ∉ C ≠ ∅`. The identity carries `x ∈ C`, as Rockafellar's usage does.
* **§16's conditional rows are stateable without a constraint qualification after all.** §3.7 of
  [sub-plan 3](03-relint-recession.md) planned two forms per row — unconditional, and exact under
  `IsExactSum`/`IsExactImage`. Rockafellar's own form is a third: closed convex inputs and a `clFn`
  on the dual side, which is *more general* than the exact form and costs three lines each
  (`conj_add_eq_clFn_infConv`, `conj_iSup_eq_clFn_convFn`, `conj_compLin_eq_clFn_mapLin`). Every
  row of the table now has three forms.
* **§23's calculus is layer A.** §5.2 of [sub-plan 5](05-differential.md) placed the subgradient
  calculus after the §23 duality, expecting to need topology. It does not: Theorem 23.5
  (`mem_subgradient_iff_add_conj_le`, unconditional) reduces both Theorems 23.8 and 23.9 to
  arithmetic on one inequality, and neither proof mentions an epigraph, a directional derivative or
  a separating hyperplane. The only real content is `Tdaf.EReal.le_coe_of_add_le_coe_add`, for
  splitting one joint Fenchel equality into two.
* **The two D5 interfaces are now fully exploited *and* populated.** §16's exact rows and
  §23.8/23.9 are proved against `IsExactSum`/`IsExactImage`, and `Duality/Relint.lean` supplies
  both by Rockafellar's own constraint qualification. `of_continuousAt` (§10) and `of_polyhedral`
  (§20) remain as alternative constructors, but nothing is blocked on them.
* **`IsExactImage` as first stated forced `A'` to be surjective, and had to be fixed.** The field
  read `∀ y : F, ∃ z : H, A' z = y ∧ g* z ≤ (g A)* y`, which demands a point of the fibre
  `A' ⁻¹ {y}` at *every* `y` — so the interface was unsatisfiable whenever `A'` missed a point,
  e.g. for `A = 0` between nonzero spaces, where Theorem 16.3's conclusion nevertheless holds
  (both sides are `+∞` off `range A'`, by `mapLin_of_notMem_range`). The field now carries the
  guard `(g A)* y < ⊤`, which is exactly what Theorem 9.2 delivers and exactly what every consumer
  has available: `IsExactImage.subgradient_compLin` gets it from `g (A x) ≠ ⊥`, and
  `exists_conj_compLin_eq` takes it as a hypothesis. `IsExactSum` has no such problem — every `y`
  admits the splitting `y + 0` — so its field is unchanged.
* **Lemma 16.2 and Corollary 16.2.1 never needed to be stated.** §6 of this plan and §3.7 of
  [sub-plan 3](03-relint-recession.md) treated them as the missing `ri`-to-recession bridge that
  `IsExactSum.of_relint` would consume. In the event the bridge is **Theorem 13.3** — `(f*)0⁺` is
  the support function of `dom f` — composed with §6's `eq_of_isMaxOn_of_mem_relint`. Two
  cancelling recession directions of `epi f*` and `epi g*` force the linear function `⟨·, z⟩` to
  attain its bound over `dom f` at the common relative interior point, hence to be constant. That
  is four lines inside the constructor, and no separate lemma survives.
* **`IsExactSum.of_relint` comes from Corollary 9.1.1, not from a separable-sum construction.**
  The textbook derivation of Theorem 16.4 from Theorem 16.3 goes through `h(x₁, x₂) = f(x₁) + g(x₂)`
  on `E × E` and the diagonal map, which would need a product pairing, an `IsCompatiblePairing`
  instance for it, and closedness of a separable sum. Applying **Corollary 9.1.1** directly to
  `epi f*` and `epi g*` avoids all three: the sum of the two epigraphs is closed, hence
  (`IsEpiLike.of_isClosed`) an epigraph, namely that of `f* □ g*`, and a point of that sum *is*
  the splitting `exact_le` asks for. Separable sums and product pairings are still wanted for §16's
  separable case and §38, but they are not on the critical path.
