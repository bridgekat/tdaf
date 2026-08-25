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
  **Done**, and it was cheap: the open-set form of Hahn–Banach needs no local convexity.

Then §23.8 (`∂(f+g) = ∂f + ∂g`), §31 (Fenchel duality) and §38 are consequences of `IsExactSum`,
each proved once. This is the README's "prefer interfaces over concrete implementations" applied to
the single most repeated hypothesis in the book. The analogous interface for images under linear
maps is `IsExactImage` (Theorem 16.3), whose sufficient conditions come from §9 — and which carries
the adjoint-pair datum of D3, since the transpose is not a function of `A`.

**Placement (review finding C2).** `Duality/Exact.lean` holds the *interface* and its interface-only
consequences, and imports only `Duality/Conjugate` and `Operations/InfConv`. Each
`IsExactSum.of_*` is declared in the module that owns its hypothesis — `of_polyhedral` in
`Polyhedral/Duality.lean`, `of_continuousAt` in `Duality/Continuity.lean` (layer B, as planned). `of_relint` turned out to own no
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

### D10. **The backbone is not tied to Rockafellar**

*Convex Analysis* is the source of the material and the order of work; it is **not** part of the
backbone's interface. A second textbook on the same topic, or a research paper, must be able to sit
on top of this library without the seams showing. Concretely:

* **Names are mathematical, not bibliographic.** `polarCone_polarCone`, `fenchel_duality`,
  `alternative_linear_system`, `subgradient_maximalMonotone` — never `thm_14_1`, and never a name
  whose only justification is that the book puts two facts in one numbered statement. Where the
  book's terminology is idiosyncratic, prefer the term the wider literature uses and note the
  book's word in the docstring: `maximin`/`minimax` rather than "the saddle-value pair",
  `ConvexProcess` rather than "positively homogeneous multifunction".
* **Statements are the natural general ones**, per D9 — which is already the reason a Rockafellar
  theorem often splits into several backbone lemmas with different hypotheses. When the book's
  statement bundles clauses that have different natural homes, split them; when the book's
  hypotheses are stronger than the proof needs, weaken them. Every such divergence is recorded as a
  correction in `NOTES.md`.
* **Module docstrings lead with the mathematics.** "Gauges, polars of convex functions, and
  obverses — four correspondences, each an involution on a characterised class" is a docstring;
  "Rockafellar's §15" is a *reference*, and belongs in the `## References` section at the bottom
  together with the theorem numbers. Per-declaration doc comments may and should cite
  "**Rockafellar, Theorem 23.4**" — that is a citation for the reader, not a dependency — but the
  statement above it has to read as mathematics on its own.
* **File and namespace layout follows the mathematics.** `Saddle/Continuity.lean`,
  `Bifunction/Algebra.lean`, `Polyhedral/Separation.lean` are named for their content; nothing is
  named for a chapter, and nothing is organized "one module per §" except where the section happens
  to be a coherent topic.
* **Book-specific packaging goes to the surface.** A theorem stated exactly as the book states it,
  in `ℝⁿ`, with the book's numbering and bundling, is a *surface* result whose proof is a
  specialization of backbone lemmas. That is what the surface layer is for.

This is a design goal, not yet a finished refactor: parts of the existing docstrings and a few
names still read as §-by-§ commentary, and a pass over them is scheduled after the first surface
library exists — the surface is what will show which backbone interfaces are actually load-bearing.
New work should not add to the debt.

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
      Closed.lean                     -- closedness of f A (layer B companion to Image); Thm 5.7, §7
      Partial.lean                    -- partial addition, inverse addition #; Thm 3.6–3.8, 5.8
    Lattice.lean                      -- complete lattice of convex functions
    Closure.lean                      -- cl f, closed convex functions; §7
    Separation.lean                   -- proper/strong separation; §11 (wraps Mathlib)
    Duality/
      Pairing.lean                    -- dual pairs, adjoint pairs, prodPairing/negFst
      InnerPairing.lean               -- symmetric positive definite self-pairings; §31, §37
      Conjugate.lean                  -- conj B f, Fenchel inequality, Fenchel–Moreau; §12
      ConcaveConj.lean                -- concaveConj, the sign dictionary (D2); §12 mirrored, §30
      Support.lean                    -- support functions; §13
      Polar.lean                      -- one-sided polar cone / set; partial affine fns; §12, §14
      Barrier.lean                    -- barrier cone vs recession cone; Cor 14.2.1
      Exact.lean                      -- IsExactSum / IsExactImage interfaces (D5)
      Continuity.lean                 -- IsExactSum.of_continuousAt (D5, layer B)
      Ops.lean                        -- the dual-operations table; §16
    RelativeInterior.lean             -- ri calculus; §6                       [finite-dim]
    Recession/
      Cone.lean                       -- 0⁺C, lineality, rank; §8
      Function.lean                   -- f0⁺, recession/constancy/lineality of f; §8
      Closedness.lean                 -- Thm 9.1–9.8                          [finite-dim]
    Caratheodory.lean                 -- §17; Thm 17.2 (directions still to come)  [finite-dim]
    Continuity.lean                   -- §10.1, 10.4, 10.5                    [finite-dim]
    Simplicial.lean                   -- simplices, locally simplicial sets; §10.2, 10.3
    Face.lean                         -- §18 Thms 18.1, 18.2, 18.4/18.5 bounded  [finite-dim]
    Polyhedral/
      Cone.lean                       -- polyhedral / finitely generated cones; Minkowski–Weyl
      Defs.lean                       -- polyhedral / finitely generated sets; §19 Thm 19.1
      Ops.lean                        -- the polyhedral calculus; §19 Thms 19.3, 19.5-19.7
      Function.lean                   -- PolyhedralFn; §19 for fns (Thm 19.4, Cor 19.3.4)
      Conjugate.lean                  -- **Thm 19.2**: the conjugate of a polyhedral function
      Duality.lean                    -- polyhedral constraint qualifications; §20 Thm 20.1
      Separation.lean                 -- §20 Thm 20.2 and Cor 20.2.1
      Closedness.lean                 -- §20 Thm 20.3 and Cor 20.3.1
      Simplicial.lean                 -- §20 Thms 20.4, 20.5
    Helly.lean                        -- §21 Thms 21.1, 21.2, 21.3, 21.6, Cors 21.3.1-2, 21.6.1-2
    HellyRefined.lean                 -- §21 Thms 21.4, 21.5, the polyhedral/affine-tail refinements
    LinearInequalities.lean           -- §22 (elementary vectors, Tucker complementarity)
    Subgradient/
      Defs.lean                       -- f'(x;·), ∂f; §23.1–23.5
      Calculus.lean                   -- sum/chain rules; §23.8, 23.9
      Existence.lean                  -- ∂f x ≠ ∅ (and when it is ∅); §23.3, 23.4, 23.10   [finite-dim]
      Monotone.lean                   -- §24 Thms 24.4, 24.8, 24.9
      OneDim.lean                     -- §24 Thms 24.1, 24.3, 24.2 (uniqueness)   [on ℝ]
      Primitive.lean                  -- §24 Thm 24.2 (existence), complete non-decreasing curves
      Integral.lean                   -- §24 Cor 24.2.1, f as the integral of f'
      Rademacher.lean                 -- §25 Thm 25.5, a.e. differentiability; Cor 25.5.1
      GradientLimit.lean              -- §25 Thm 25.7, convergence of gradients
      Reconstruction.lean             -- §25 Thm 25.6, the subdifferential from the gradients
      Convergence.lean                -- §24 Thms 24.5, 24.6
      Bounded.lean                    -- §24 Thm 24.7
      Gradient.lean                   -- ∇f vs ∂f; §25 Thms 25.1, 25.2
      Uniqueness.lean                 -- §25 Thm 25.1's converse, Cors 25.1.2-25.1.3
      Differentiability.lean          -- §25 Thms 25.3, 25.4 (continuity and density)
      Legendre.lean                   -- Legendre transformation; §26 Thm 26.4
      EssentiallySmooth.lean          -- §26 Thm 26.1
      BoundaryDirDeriv.lean           -- §26 Lemma 26.2
      StrictlyConvex.lean             -- §26 Thm 26.3, Cor 26.3.1
      Preservation.lean               -- §26 Cors 26.3.2, 26.3.3
      LegendreType.lean               -- §26 Cor 26.4.1, Thms 26.5, 26.6
      Cofinite.lean                   -- §26 Lemma 26.7
    Optimization/
      Minimum.lean                    -- §27 Thm 27.1 (all but (e)), 27.2, 27.3 + Cor 27.3.1, 27.4
      Perturbation.lean               -- convex programs as bifunctions; §29
      Lagrangian.lean                 -- partial conjugation, Lagrangians; §28–§29
      Adjoint.lean                    -- adjoint bifunctions, dual programs; §30
      Fenchel.lean                    -- Fenchel duality; §31 Thms 31.1, 31.3, 31.4
      Moreau.lean                     -- the quadratic and its envelope; §31 Thm 31.5
      Prox.lean                       -- prox, Cors 31.5.1, 31.5.2                [finite-dim]
      MoreauGradient.lean             -- §31 Thm 31.5, the gradient formulas
      Maximum.lean                    -- §32 Thms 32.1-32.4, Cors 32.3.1-32.3.4
    Saddle/
      Defs.lean                       -- saddle-functions, cl₁/cl₂, the bracket; §33
      Closure.lean                    -- lower/upper closures; §34 Thm 34.1
      Correspondence.lean             -- saddle-functions ↔ bifunctions; §33 Thm 33.3
      Equiv.lean                      -- equivalence classes, kernels; §34 Thms 34.2–34.5
      Continuity.lean                 -- §35 Thms 35.1-35.5
      Differential.lean               -- §35 Thms 35.6-35.8
      Minimax.lean                    -- saddle-points, minimax theorems; §36–§37
      Monotone.lean                   -- partial inversion; §37 Cors 37.5.1, 37.5.2
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
3. ~~**Theorem 24.8/24.9** (cyclically monotone ⟺ subdifferential; maximality).~~ **Done.** The
   construction of `f` from a cyclically monotone `ρ` is a genuinely clever explicit supremum over
   cycles, and it is `cyclicPotential B ρ s`. The maximality half turned out *not* to need the
   one-dimensional theory of 24.1–24.3: `∂f ⊆ ∂g → g = f + const` follows from Theorem 23.5 plus
   the conjugate-side repetition. Reference: Rockafellar, *Characterization of the subdifferentials
   of convex functions*, Pacific J. Math. 17 (1966).
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
| §6 | **done**, Cor 6.8.1 and Thm 6.9 included (`Convex.relint_cone_prodMk_one`, `Convex.relint_convexHull_union`) — both stated about the explicit cone `insert 0 {p | 0 < p.1 ∧ p.2 ∈ p.1 • C}` so that `RelativeInterior.lean` need not import `Recession/ConeHull.lean`; Thm 6.9 for two sets, the step to `m` being a bare induction |
| §7 | **done**, Thm 7.6 and Cor 7.6.1 included; **Thm 7.5 now has its `ri` form** (`ConvexFn.tendsto_lscHull_along_segment_relint`). Thm 7.6's `ri` formula needs no properness, and Cor 7.6.1's two formulas need one hypothesis each rather than both. It is proved with no `AffineSubspace` machinery: intersecting `epi f` with the *slab* `univ ×ˢ Iic α` instead of the book's horizontal hyperplane avoids Cor 6.5.1 entirely |
| §8 | done (8.1–8.8) |
| §9 | **Complete** — Thms 9.1–9.5, Cors 9.1.1–9.1.3 and **Cor 9.2.2** (`Recession/Closedness.lean`), and Thms 9.6–9.8 with Cors 9.6.1 and 9.8.1 (`Recession/ConeHull.lean`, which also carries Thm 8.2 in cone form and `posHomGen`). Cor 9.2.1 and the `m`-fold forms of 9.8/9.8.1 are deferred as contentless inductions; Cor 9.7.1 belongs to §15; Cor 9.8.2 is superseded by `Caratheodory.lean`; Cor 9.8.3 needs `convHullFn` for a finite family |
| §10 | **Complete** — `Continuity.lean` (10.1 with the `ri`-to-`interior` chart Mathlib leaves as a `proof_wanted`, Cor 10.1.1, 10.4 with the Lipschitz constant `2M/ε` exhibited, 10.5 with Cors 10.5.1–10.5.2), `Simplicial.lean` (10.2, 10.3, with `IsSimplex`/`LocallySimplicial`) and `Convergence.lean` (10.6–10.9 with Cor 10.8.1, each in an `interior` and a `ri` form, families indexed by an arbitrary type) |
| §11–§13 | **done**, including **Thm 13.3** (`Recession/Conjugate.lean`, which is where §13 and §8 meet) and **Thms 13.4, 13.5, Cors 13.3.1 and 13.5.1** (`Duality/Level.lean`). Theorem 13.5's second assertion, `cl (posHomGen g) = δ*(· | {x | g* x ≤ 0})`, carries **no hypothesis at all**; the first assertion is it applied to `f*` plus Fenchel–Moreau. Cor 13.3.1 is `Cofinite` with `cofinite_iff_dom_conj_eq_univ`. §13.6 (ε-subgradients) is §23.6's business. **Thm 12.3 is now done too** (`Duality/Conjugate.lean`), row by row — translation (`conj_comp_sub`), tilt (`conj_add_pairing`), constant (`conj_add_const`) and an invertible substitution (`conj_comp_linearEquiv`), with `conj_comp_affine` for the book's combined formula. All four rows are **layer A and hypothesis-free**: they hold for an arbitrary `h : E → EReal`, improper ones included, because the quantities being slid across `⟨x, y⟩ - h x` are *real* and cannot produce `∞ - ∞`. The scaling rows of the same table are Thm 16.1, already done. **The partial-affine formula is now done too** (`partialAffineFn`, `conj_partialAffineFn`, in `Duality/Polar.lean` — it needs `polarCone`, so it cannot sit with the rest of Thm 12.3): `δ(· \| L + a) + ⟨·, a*⟩ + α` conjugates to `δ(· \| L^⊥ + a*) + ⟨a, ·⟩ + α*`, the **same** construction read through the polar pairing. What is left of §12 is the Tucker-representation form, which is coordinate bookkeeping on `Rᴺ` and belongs to the surface |
| §14–§15 | **done, Theorem 15.3 included** — §14 through Thm 14.5 in `Duality/Polar.lean` with **Cor 14.2.1** (`Duality/Barrier.lean`, proved directly from Thm 13.1) and **Thm 14.2 with Cor 14.2.2** (`Recession/Conjugate.lean`: `recessionConeFn_conj` is Thm 13.3 at the zero level set and needs no closedness at all, `recessionConeFn_eq_polarCone_dom_conj` is that fed `f** = f`, and the bounded-level-set criterion runs on a new dictionary lemma `zero_mem_interior_iff_polarCone_eq_zero` and on **Cor 6.4.1**, `Convex.mem_interior_iff_absorbs`, which was missing from Mathlib too), and **Thms 14.6, 14.7 and all of §15** in `Duality/Gauge.lean`: `gaugeFn`, `IsGauge`, `IsNorm`, `polarGauge`, `polarFn`, `obverse`, and the three correspondences as `Equiv`s (`gaugeEquiv`, `polarGaugeEquiv`, `polarFnEquiv`). **Cor 14.6.1 is done too**, in `Duality/Gauge.lean` — it has to be there rather than in `Duality/Polar.lean`, since it consumes `polarCone_linealitySpace`, and the `finrank` API it was said to need is six lines of rank–nullity (`polarSubmodule`, `finrank_add_finrank_polarSubmodule`); its third relation, `rank C° = rank C`, is the difference of the other two and is recorded as a remark rather than a theorem. **Thm 15.3's first assertion and conjugacy formula and Cors 15.3.1–15.3.2 are done** in `Duality/GaugeLike.lean`, which also carries **Thm 12.4** — the monotone conjugate of a nondecreasing lsc convex function on `[0, +∞]`, stated as a genuine involution by truncating it off the half-line. **Thm 15.3 is now complete**: `IsGaugeLike` and `IsGaugeLike.exists_eq_monotoneComp` give the converse, gauge-like closed proper convex ⇒ `g ∘ k`, and `closedProperConvexFn_and_isGaugeLike_iff` is the book’s biconditional. The recorded blocker — convexity of the reconstructed `g` — was not the obstacle: the whole proof runs on "every sublevel set of `f` above `inf f` is a sublevel set of the gauge of one of them", after which `f` is a nondecreasing function of that gauge, and `g` is `f` along a ray (or, when the sublevel sets are a single cone, a step function). The converse needs no pairing at all. The second assertion, `f*` gauge-like, is `isGaugeLike_conj_monotoneComp`, on a new `exists_lt_monotoneConj`: conjugacy *exchanges* Rockafellar’s two side conditions on `g` |
| §16 | **done** — `Duality/Exact.lean` (the D5 interfaces, the exact rows), `Duality/Ops.lean` (**Thms 16.1, 16.3, 16.4, 16.5**, unconditional rows plus `clFn` forms) and `Duality/Relint.lean` (**the `of_relint` constructors**, which populate both interfaces). Lemma 16.2 and Cor 16.2.1 are subsumed: they were the `ri`-to-recession bridge, and that bridge is now Thm 13.3 plus §6.4 inside the constructors |
| §17–§22 | **§17 except Thm 17.3, all of §19, all of §20, all of §21, and §22 through Thm 22.3 done** — `Caratheodory.lean` (**Thm 17.1** for points with a fixed index *and* for points and directions, Carathéodory for cones, **Thm 17.2**, Cor 17.2.1), `Polyhedral/Cone.lean` (Minkowski–Weyl for cones, both halves, plus closedness of a finitely generated cone), `Polyhedral/Defs.lean` (`Polyhedral`, `FinitelyGenerated`, the homogenisation dictionary, **Thm 19.1**, Cor 19.1.1), `Polyhedral/Ops.lean` (**Thms 19.3, 19.5, 19.6, 19.7**, Cor 19.7.1), `Polyhedral/Function.lean` (`PolyhedralFn`, **Thm 19.4**, Cor 19.3.4), `Polyhedral/Conjugate.lean` (**Thm 19.2**), `Polyhedral/Duality.lean` (**Thm 20.1**), `Polyhedral/Separation.lean` (**Thm 20.2**, Cor 20.2.1), `Polyhedral/Closedness.lean` (**Thm 20.3**, Cor 20.3.1) `Polyhedral/Simplicial.lean` (Thm 20.4, **Thm 20.5**), `Helly.lean` (**Thms 21.1, 21.2, 21.3, 21.6**, Cors 21.3.1, 21.3.2, 21.6.1, 21.6.2), `HellyRefined.lean` (**Thms 21.4, 21.5**), `LinearInequalities.lean` (Farkas as Cor 22.3.1, **Thm 22.1** Gale, **Thm 22.2** Motzkin, **Thm 22.3**) and `Face.lean` (**Thms 18.1, 18.2**, Cors 18.1.1–18.1.3, plus **Thm 18.4** and **Thm 18.5/Cor 18.5.1** — Minkowski's theorem — in the bounded case, and Cor 18.5.3); §22 is done through Thm 22.3 — and Thm 22.1 did **not** have to wait for Thm 21.4, since Farkas gives it directly from `polarCone_polarCone` on a finitely generated hence closed cone; §17's **Cors 17.1.1, 17.1.2, 17.1.3 and 17.1.5 are done**, **Thm 17.3 is done** — and it is *false* as the book states it, needing `0 ∉ S*`, while its stated hypothesis `x* ≠ 0` is unnecessary; Cor 9.6.1, which this plan named as its blocker, was already in the project as `isClosed_coe_hull_of_isBounded`, and **Cors 17.1.4 and 17.1.6 are false as the book states them** (on `ℝ¹` with `f₁ y = -y`, `f₂ y = y` the generated function is `-∞` everywhere while every admissible representation gives `±1`) so they are not stated in any form; §18's **Thms 18.3, 18.4, 18.5 and Straszewicz's 18.6** are done (`HullDirections.lean` with `convexHullPD` and `isLeast_convexHullPD`, `Representation.lean` with `ContainsNoLine`, `IsExtremeDirection`, `IsAffineHalf`), and **18.7, 18.8 and Cor 18.7.1 are done too** (`Exposed.lean`, `Tangent.lean`), which needed exposed *directions* but **no dimension bookkeeping whatever** — `exists_forall_sub_le_mul_sub` replaces the book's extension of an `(n-2)`-dimensional affine set by a one-dimensional difference-quotient argument, and Thm 18.8 is proved through the polar rather than behind 18.7, at the cost of needing reflexivity outside `ℝⁿ`; and §21's **Thm 21.3 with Cors 21.3.1–21.3.2 is done** — its last step needs neither Thm 16.4 nor Thm 16.1, only Fenchel's inequality summed termwise, and Cor 21.3.1's tolerance has to be halved because `EReal` is not cancellative. **Thms 21.4 and 21.5 are now done** (`HellyRefined.lean`), and the obstruction this row used to name is **gone**: `IsExactSum.of_relint` (Thm 16.4) and `IsExactSum.of_polyhedral` (Thm 20.1) carry the book's hypotheses — *proper convex*, no closedness — the closed cases surviving as `…_closed`, and the removal is **Thm 9.3** in the conjugate form `conj_add_eq_conj_clFn_add_clFn` (`Duality/Relint.lean`) — *not* the book's own `cl (f + g) = cl f + cl g`, which was already present as `clFn_add` and is too strong for §20. Cor 19.1.2 for *functions* is `Polyhedral/Homogeneous.lean` (`epi (posHomGen f)` is the cone generated by the points of `epi f` together with `(0,1)`, whenever `epi f` is `conv P` plus the vertical ray — with a general direction set the identity is false), together with Thm 19.5 on the generator side (`Polyhedral/Recession.lean`, `0⁺(A '' C) = A '' 0⁺C` for polyhedral `C`). The bridge to `k₀` is `conj_affineFn` — `fᵢ* = δ(· ∣ aᵢ) + αᵢ`, which needs **`B.SeparatingRight`**, not `IsCompatiblePairing` — and `kⱼ* = δ(· ∣ Cⱼ)` is Thm 13.5 (`conj_posHomGen`, no hypotheses) after Thm 16.5. The epigraph-sum description of `conv {k₀, k₁}` was never needed: 21.4 uses only `k 0 ≤ k₀(-z) + k₁ z`, so `apply_zero_eq_bot_of_le_of_le` takes an arbitrary positively homogeneous convex `k` below both halves. Rockafellar's reduction to nonempty `I₀` and `I₁` is also unnecessary, since `posHomGen h 0 ≤ 0` always puts `0` in `dom kⱼ`. Thm 21.5 is pure re-indexing on top of 21.4 |
| §23 | **done** — 23.1, 23.2, 23.3, 23.5 and corollaries (`Subgradient/Defs.lean`); 23.8, 23.9 and Cor 23.8.1 (`Subgradient/Calculus.lean`); 23.4 and 23.10 (`Subgradient/Existence.lean`); **23.6** with `epsSubgradient` (`Subgradient/Approx.lean`, on Thm 13.5 and Thm 9.7 applied to `h + ε`); **23.7 and Cor 23.7.1** (`Subgradient/Existence.lean`, on the `ri` half of Thm 7.6 and Cor 9.6.1). Neither of the last two needs `f` closed, and properness is not a separate hypothesis — it follows from `∂f x ≠ ∅`, which *is* in the book and cannot be dropped. Cor 23.7.1 is stated for `Bornology.IsBounded (∂f x)` rather than the book's `x ∈ int (dom f)`: `bddAbove_subgradient_iff_mem_interior_dom` gives only the pairing form of boundedness, and upgrading it is a separate finite-dimensional lemma |
| §24 | **Thms 24.1–24.9 all done**, with Cor 24.5.1. Five modules: `Monotone.lean` (cyclic monotonicity — `IsCyclicallyMonotone`, `cyclicPotential`, and Thm 24.9 in both directions), `OneDim.lean` (`rightDeriv`/`leftDeriv`, and Thm 24.3 as "maximal monotone relations on `ℝ` = `∂f` of closed proper convex `f`"), `Primitive.lean` (Thm 24.2's existence clause), `Convergence.lean` (Thms 24.5–24.6) and `Bounded.lean` (Thm 24.7). **The plan was wrong about §24 three times.** Thm 24.9's uniqueness clause does not need 24.1–24.3 at all, and inverting that unlocked the rest; Thm 24.2's existence clause needs **no integral**, because the primitive is pinned down by its graph and Thm 24.3 produces it; and Thm 24.6's second assertion needs neither an `EReal`-valued Cor 10.8.1 (the points are eventually *interior*) nor a new Cor 23.5.3 (the library already had it). **Cor 24.2.1 is now done too** (`Integral.lean`): `f y - f x = ∫ₓʸ f'₊ = ∫ₓʸ f'₋`, by
`intervalIntegral.integral_eq_sub_of_hasDeriv_right` — which asks for exactly what convexity gives,
continuity on the closed interval, a right derivative inside it, and monotonicity of that
derivative — plus the bridge `rightDeriv_eq_coe_derivWithin` between the project's `EReal` infimum
of difference quotients and Mathlib's `derivWithin _ (Ioi t) t`, and the countability of the jump
set of `f'₊` for the left-derivative half. Missing: only Rockafellar's integral formula for the
primitive of an arbitrary nondecreasing `φ`, which is an improper integral |
| §25 | **§25 is complete: Thms 25.1–25.7 in full**, with Cors 25.1.1–25.1.3 and 25.5.1. `Gradient.lean` holds the Fréchet theory: `∂f x = {∇f x}` and `f'(x; v) = ⟨v, ∇f x⟩` at a point of differentiability, plus the algebraic converse `subgradient_eq_singleton_of_dirDeriv_eq`. **The sufficiency half of Thm 25.2 needs no compactness**: a cross-polytope decomposition (`z` is a convex combination of `n` points at the *same* distance from `x` along basis directions) does Gâteaux ⇒ Fréchet quantitatively, with no continuity of `f` and no Thm 7.2/4.8/23.2, and it makes Rockafellar's `2n`-partial-derivative strengthening the *primitive* statement. `Differentiability.lean` holds Thms 25.3 and 25.4 on the line, where countability of the non-differentiability set is `Monotone.countable_not_continuousAt` applied to `rightDeriv`. Thms 25.5–25.7 and Thm 25.4's measure-zero clause need Rademacher and Haar measure, which the project does not have; **Cors 25.1.2–25.1.3 are done in both forms** — the subgradient form (`mem_exposedPoints_epi_conj_iff`, `mem_exposedPoints_supportSet_iff`) needs **no §18 at all**, being a direct supporting-hyperplane argument on `epi f*` plus Thm 23.5, though it does need `ClosedFn`, which the book does not assume. **Thm 25.1's converse half** is `Uniqueness.lean`: the step the book passes over is that a unique subgradient puts `x` in the *interior* of `dom f`, which is `∂f x + N_{dom f}(x) ⊆ ∂f x` together with "a convex set in finite dimensions is a neighbourhood of every point whose normal cone is trivial" (Cor 11.6.1 through the pairing). Thm 23.4's own interiority clause is no shortcut — it already assumes `x ∈ ri (dom f)`. With the interior in hand `f'(x; ·)` is finite everywhere, hence continuous and closed, which removes the `cl` from Thm 23.2 |
| §26 | **done** (`Subgradient/Legendre.lean`, `EssentiallySmooth.lean`, `BoundaryDirDeriv.lean`, `StrictlyConvex.lean`, `Preservation.lean`, `LegendreType.lean`, `Cofinite.lean`): the Legendre conjugate is `f*` on `D = ∇f(C)` (26.4); `∂f` single-valued ⟺ essentially smooth (26.1), with condition (c) replaceable by the directional-derivative collapse `f'(x + λ(a−x); a−x) ↓ −∞` (**Lemma 26.2**); `f*` essentially smooth ⟺ `f` essentially strictly convex (26.3); `∂f` one-to-one ⟺ `f` of Legendre type (26.3.1); essential smoothness survives `□` and linear images under the §16 exactness interfaces (**Cors 26.3.2, 26.3.3**); `D = dom ∂f*` so `ri (dom f*) ⊆ D ⊆ dom f*` (26.4.1); `∇f : int (dom f) → int (dom f*)` is a bijection with `∇f* = (∇f)⁻¹` (26.5); `∇f` a bijection of `E` onto itself ⟺ `f` strictly convex with `dom f* = E` (26.6); and a finite differentiable convex `f` is co-finite ⟺ `‖∇f xᵢ‖ → ∞` whenever `‖xᵢ‖ → ∞` (**Lemma 26.7**) |
| §27 | **Thms 27.1(a), 27.1(b), 27.2, 27.4 and the non-polyhedral case of Thm 27.3 done** (`Optimization/Minimum.lean`): `argmin`, `inf f = -f*(0)` (no hypotheses), the minimum set as `∂f*(0)`, existence, compactness and ε–δ well-posedness of the minimum set for a closed proper convex function with no direction of recession, Cors 27.2.1–27.2.2, minimisation over a closed convex set sharing no direction of recession with `f` (Cor 27.3.3 included), and the optimality condition `0 ∈ ∂h x + N_C(x)` in both halves. **Thm 27.1 is now done except for (e)** — (f) from Thm 14.2 (`recessionCone_setOf_le_eq_polarCone_dom_conj`), (i) from Cor 13.3.4(a) in both sentences (`zero_mem_closure_dom_conj_iff`, `zero_notMem_closure_dom_conj_iff`, `Duality/Level.lean`), (d) from Cor 14.2.2 rather than from Cor 13.3.4 as the book has it, (g) from Cor 13.2.1 with no shifted-function API, (h) from Thm 23.6 for `f*` at the origin, and (c) from Thm 23.3's second half, now in `Subgradient/Existence.lean`. (e) cannot be *stated* without a reflexive pairing: `∂f*(0)` a singleton is a statement about `E**`. **Cor 27.3.2 is done and does not need Helly** — `argmin_nonempty_of_polyhedralFn` reads it off the finitely generated epigraph, which is also what unblocks Thm 29.2's optimal-solution clause; **Thm 27.3 is now done in full** — general case *and* polyhedral refinement — and neither needs Helly: `exists_linearProj` projects along the constancy space of the objective, which is what Rockafellar's Theorem 21.5 detour was buying. The general case is also strengthened to the constancy/linearity recession hypothesis (`exists_forall_le_of_inter_subset_constancySpace_inter_linealitySpace`), which is strictly weaker than the `0⁺h ∩ 0⁺C = {0}` previously assumed. **Cor 27.3.1 is now done too** (`exists_forall_le_of_polyhedral_of_recessionConeFn_subset_linealitySpaceFn`): its hypothesis is that every direction of recession of `h` is one in which `h` is *affine* (`0⁺h ⊆ lin h`), and the lower bound on `C` is what forces the slope along such a direction to vanish, turning it into a direction of constancy (`mem_constancySpace_of_mem_linealitySpaceFn`, layer A, in `Recession/Function.lean`); the polyhedral refinement then applies unchanged. §27 is complete except for (e) |
| §31 | **Thms 31.1, 31.3, 31.4 and 31.5 done** (`Optimization/Fenchel.lean`, `Optimization/Moreau.lean`): `inf (f - g) = sup (g* - f*)` under `IsExactSum B f (-g)` with the supremum attained (condition (a)), the same equality with the *infimum* attained under exact addition of the conjugates (condition (b)), the Kuhn–Tucker conditions `y ∈ ∂f x`, `-y ∈ ∂(-g) x` characterising joint optimality (Thm 31.3 and Cor 31.3.1, with `A = id`), the conic case `inf_K f = -inf_{K*} f*` with its optimality conditions `y ∈ ∂f x`, `x ∈ K`, `y ∈ K*`, `⟨x, y⟩ = 0` (Thm 31.4), and **Moreau's theorem** `(f □ w) + (f* □ w) = w` in an arbitrary real Hilbert space, with both envelopes finite and the splitting `z = x + y` characterised by `y ∈ ∂f x` (Thm 31.5). Weak duality `concaveConj_sub_conj_le_sub` turned out to need no hypothesis at all. **Thm 31.2 is done** (`fenchel_duality_comp`), and it needed none of the `EReal` splitting lemma this row used to demand: going through the *concave* face of Thm 16.3 — `concaveConj_compLin` — turns the dual value at `y` into a supremum over the fibre `A'⁻¹{y}`, after which the only arithmetic left is `(⨆ i, u i) - c = ⨆ i, (u i - c)` for `c ≠ ⊥`, which `IsExactSum.conj_left_ne_bot` supplies. **Thm 31.3 and Cor 31.3.1 now hold for a general `A`** — but by a different route than this row predicted: Theorem 31.3 itself consumes nothing from Theorem 31.2, only the `IsAdjointPair` datum, and it needs neither `f` nor `g` closed; it is Cor 31.3.1's attainment clause alone that calls `concaveConj_compLin`, and its properness hypothesis on `-g` has to come from `IsExactImage.proper` rather than `IsExactSum.proper_right`. **Cor 31.2.1 is done** in both of Rockafellar's conditions, once the collapse of the dual value from `F` to `H` was factored out of Thm 31.2 as `iSup_concaveConj_compLin_sub_conj`; **Cor 31.4.2** (a subspace, where `K* = K°` is the annihilator and the orthogonality condition is automatic) is done; and **Thm 31.5's gradient formulas** `x = ∇(f* □ w) z`, `x* = ∇(f □ w) z` are done in `Optimization/MoreauGradient.lean`, by showing `∂(f □ w) z` is a singleton and applying Thm 25.1's converse — Thm 26.3, which this row used to demand, is not needed. **`Optimization/Moreau.lean` and `Optimization/Prox.lean` now run on an arbitrary symmetric positive definite self-pairing `B`** rather than on `innerₗ E` (`Duality/InnerPairing.lean`): `quadFn B z = ½ B z z`, `prox B f z`, and nonexpansiveness measured in the norm `B` induces, with `dist_prox_prox_le` recovering the inner-product statement. This is what makes **Cors 37.5.1 and 37.5.2** instantiable on `U × X`, which carries the supremum norm and is not an `InnerProductSpace`. Dropping the inner product also dropped `CompleteSpace`: `IsCompatiblePairing B` is Riesz representation stated as a hypothesis. **Cor 31.4.3 is done** (`Optimization/ConeDuality.lean`): for `h` finite and co-finite and `K` a nonempty convex cone, `inf_{x∈K} {h(z+x) - ⟨z*,x⟩} + inf_{x*∈K*} {h*(z*+x*) - ⟨z,x*⟩} = ⟨z,z*⟩` with both infima finite and attained. It needed Thm 31.4's **attainment clauses**, which were missing from the file: under condition (a) attainment of the dual infimum is `IsExactSum.exact_le` read at the origin and needs no separation argument at all; under (b) it is that same statement on the dual pair, closed by the bipolar `K** = K` and Fenchel–Moreau. Closedness of `K` is used only there — the identity, the finiteness of both infima and the dual attainment need only a nonempty convex cone. Left in §31: Cor 31.4.1, the orthant instance, which belongs to the surface layer |
| §32 | **Thms 32.1, 32.2, 32.3 and 32.4 done**, with Cors 32.1.1, 32.2.1, 32.3.1, 32.3.2 (both clauses), 32.3.4 and 32.4.1 (`Optimization/Maximum.lean`): the maximum principle — a convex function attaining its supremum over `C` at a *relative interior* point is constant on `C` — every maximiser lying in a face of `C` on which `f` is constant, `sup over conv S = sup over S` with no new maximisers created, the same statement over the extreme points of a compact convex set, and `∂f x ⊆ N_C(x)` at a maximiser with the subgradient non-zero as soon as `f` is non-constant. Thm 32.3 is Theorem 18.5 plus "a convex function bounded above on a half-line is non-increasing along it"; Cor 32.2.1 needs Thm 18.4 in hull form and the hypothesis `¬ IsAffineHalf C`; the "supremum attained" clause of Cor 32.3.2 needs Thm 10.1 *and* `C ⊆ ri (dom f)`, without which it is false. **Cor 32.3.3 is done** (`exists_isMaxOn_of_polyhedral_of_bddAboveOnRays`): its hypothesis, "no half-line in `C` on which `f` is unbounded above", is the predicate `BddAboveOnRays`, and the lineality space of `C` is quotiented out with `eq_add_inter_of_isCompl` — `C = L + (C ∩ N)` for any complement `N`, no inner product needed. §32 is complete |
| §29 | **Theorem 29.1 done in full** (`Optimization/Perturbation.lean`): `Bifun`, `graphFn`, `ConvexBifun`, the perturbation function `infBifun` with `dom (inf F) = dom F`, `Consistent` / `StronglyConsistent` / `StrictlyConsistent`, and `KuhnTucker` **defined as Rockafellar defines it** — `⨅ u {⟨u, v⟩ + inf F u}` finite and equal to `inf F 0` — so that `mem_kuhnTucker_iff_neg_mem_subgradient` (`v ∈ KT ↔ -v ∈ ∂(inf F)(0)`) is a proved theorem and not an `Iff.rfl`. `KuhnTucker B F = -(∂(inf F)(0))` then gives convexity, closedness and — through Theorem 23.4 — nonemptiness under strong consistency (the first half of Cor 29.1.4). The Lagrangian description (`Optimization/Lagrangian.lean`) identifies `L(·, x)` with a **concave conjugate** on the nose, which is the whole of design decision D8; `iInf_lagrangian` and weak duality follow. **Cors 29.1.1–29.1.6 and Thm 29.2 are done**: the derivative clause of Cor 29.1.1 is the support function of `-(KT)` rather than of `KT` — the sign flip in `kuhnTucker_eq_neg_subgradient` propagates — and Thm 29.2 runs on `PolyhedralBifun` together with Cor 19.3.1 (`polyhedralFn_mapLin`). Cor 29.1.4's compactness clause still needs the boundedness half of Thm 23.4, and Thm 29.2's optimal-solution clause needs Cor 27.3.2 — which is done, and does *not* need Helly, contrary to what this row used to say. **Thm 29.3 is done**, in `Saddle/Minimax.lean` where §36 lives (`isSaddlePoint_lagrangian_iff`); **Thm 29.4 is done** in `Optimization/Adjoint.lean` (`clBifun_apply_eq_clFn`, `infBifun_clBifun_eq`, the two `domBifun` inclusions) — it never needed Thm 37.6, only Thms 6.4, 6.6 and 7.5. Cor 29.4.1 is not done |
| §30 | **Theorem 30.1's computation and concavity clause, Theorem 30.2 and Corollary 30.2.2 done** (`Optimization/Adjoint.lean`): `adjointBifun`, the identity `(F* y)(v) = -f*(-v, y)` reading the adjoint as the conjugate of the graph function at a reflected point, concavity of `F*` with **no hypothesis on `F`**, the dual objective `F* 0 = concaveConj Bu (-inf F)`, weak duality `sup F* 0 ≤ inf F 0`, and the Kuhn–Tucker vectors as the dual-optimal `v` closing the duality gap (the normality-free half of Thm 30.5). Closedness of `F*` is `closedFn_conj` carried along the linear reflection `adjointSwap` by `closedFn_compLin` (`Operations/Closed.lean`, a new layer-B companion to `Operations/Image.lean` holding the inner-composition lemma for lower semicontinuity that Mathlib lacks). **Theorem 30.1 is now complete**: `concaveAdjointBifun` (the adjoint of a concave bifunction), `clBifun`/`ClosedBifun` (`cl F` taken on the graph function) and `concaveAdjointBifun_adjointBifun_eq_clBifun`, i.e. `F** = cl F`, whose proof is the reindexing of one supremum along the surjection `adjointSwap` followed by Fenchel–Moreau on `U × X` — available because `Duality/Pairing.lean` now derives `IsCompatiblePairing (prodPairing Bu Bx)` from the factors. `adjointBifun_clBifun` (`(cl F)* = F*`) is the lemma §34 runs on. `ImageClosedBifun` — closedness of every slice `F u`, strictly weaker than `ClosedBifun` — is the predicate §33's correspondence runs on, since the bracket never sees the joint closure. **Corollaries 30.2.2, Theorems 30.3, 30.4 (a)(b)(c) and Theorem 30.5 are done** (`Optimization/Normal.lean`): `Normal`, the concave mirrors `supBifun` / `domConcaveBifun` / `ConcaveConsistent` / `ConcaveStronglyConsistent` / `ConcaveNormal`, both closure formulas of Cor 30.2.2, the three equivalent conditions of Thm 30.3, strong consistency of `(P)` or of `(P*)` and existence of a Kuhn–Tucker vector as sufficient conditions, and the identification of the Kuhn–Tucker vectors with the optimal solutions of `(P*)`. The whole file rests on one lemma, `clFn_zero_eq_iSup_iInf` — Fenchel–Moreau read at the origin. **Cors 30.2.1 and 30.2.3 and Thm 30.4 (d)–(f) are done too**: both halves of Cor 30.2.1 come out of one lemma, `forall_conj_eq_top_iff`; Cor 30.2.3 runs on `clFn_eq_liminf_or`, which `Closure.lean` now carries — and Rockafellar's exception clause, "except where the left side is `-∞` and the right `+∞`", is exactly that lemma's second branch, so the exception is real rather than an artefact; Thm 30.4 (d) needs `ConcaveKuhnTucker` and (e)–(f) need `ConcavePolyhedralBifun` beside §29's `PolyhedralBifun`. Thm 30.4 (g)–(j) route through Thm 27.1(d)/(f) and Cor 13.3.4, all of which are **now done**, leaving only `int (dom (F 0)*) = int (domConcave F*)`, a Cor 7.4.1-type result |
| §33 | **Theorem 33.1 done in both directions**, with Corollary 33.1.1 and §34's effective domains (`Saddle/Defs.lean`): `ConcaveConvexFn` / `ConvexConcaveFn` / `SaddleFn`, `dom₁` and `dom₂` (**universal**, as the book has them — the plan's existential version would have made them non-convex), the partial conjugate `partialConj₂` and the partial closures `partialCl₁` / `partialCl₂`, and Rockafellar's bracket `⟨Fu, y⟩ = conj Bx (F u)`, which is concave-convex and convex-closed with *no* hypothesis on `F` beyond convexity for the one concavity clause. The converse — `bifunOfSaddle` is a convex bifunction whose bracket is `cl₂ K` — is `convexFn_iSup` plus Fenchel–Moreau. `adjointBifun_eq_concaveConj_bracket` links §30 to §33 — the adjoint is the concave conjugate, in `u`, of the bracket — and with concave Fenchel–Moreau that gives **Theorem 33.2's first equation** `⟨u, F*y⟩ = cl₁ ⟨Fu, y⟩` (`concaveConj_adjointBifun_eq_partialCl₁`). **Theorem 33.2 is done in both equations**: the first is concave Fenchel–Moreau in `u`, the second is convex Fenchel–Moreau in `y` applied to the *concave* bifunction `F*` (`bracket_concaveAdjointBifun_eq_partialCl₂`) composed with `F** = cl F`, exactly as the book derives it. **Theorem 33.3 and Corollary 33.3.1 are done** (`Saddle/Correspondence.lean`): the bracket of a closed convex bifunction is lower closed, and conversely every lower closed concave-convex `K` is the bracket of exactly one closed convex bifunction, uniqueness coming from `eq_of_bracket_eq` — two image-closed convex bifunctions with the same bracket are equal, since `F u = ⟨Fu, ·⟩*`. `ImageClosedBifun` (`Optimization/Adjoint.lean`) is the predicate that makes the "exactly one" true: the bracket sees only the slice-wise closure of `F`, never the joint one. **Cors 33.1.2, 33.2.1, 33.3.2 and 33.3.3 are done**: `bifunSaddleEquiv` and `lowerUpperClosedEquiv` (`Saddle/Correspondence.lean`) package the correspondence and the `cl₁`/`cl₂` bijection as `Equiv`s — the latter's round trips are the *definitions* of `LowerClosedFn` and `UpperClosedFn`, so its only content is that each operator lands in the other class; `bracket_eq_concaveBracket_adjointBifun_of_mem_relint` and `exists_unique_bifun_of_simpleExt` (`Saddle/Kernel.lean`) are Cors 33.2.1 and 33.3.3, the first one lemma past Thm 33.2 once `domConcave_bracket` says the concave domain of `u ↦ ⟨Fu, y⟩` is `dom F` for *every* `y`, the second Cor 33.3.1 applied to the closure pair `partialCl₁_lowerSimpleExt` / `partialCl₂_upperSimpleExt` that §34 already proves. **Cors 33.1.3 and 33.2.2 are done** (`Saddle/Correspondence.lean`, `Saddle/Kernel.lean`) once `PolyhedralBifun` arrived with Thm 29.2. The prerequisite list here was incomplete: besides Thm 19.2 and Cor 19.3.1, Cor 33.2.2's second half needs polyhedrality of the *adjoint* bifunction — Thm 19.2 at `prodPairing` plus stability of `PolyhedralFn` under `compLin` — and the concave mirror of `PolyhedralFn.clFn_eq_of_mem_dom`, neither of which appeared anywhere in the plan. The book asserts the dual-side sharpening without proving it. The exceptional pair is always `⟨Fu, y⟩ = -∞` with `⟨u, F*y⟩ = +∞`, unconditionally |
| §34 | **Theorem 34.1 is done** (`Saddle/Closure.lean`): `lowerCl`/`upperCl` (`cl₂ cl₁ K` and `cl₁ cl₂ K`), the three closedness notions `LowerClosedFn`/`UpperClosedFn`/`FullyClosedFn` with `fullyClosedFn_iff` (fully closed ⟺ lower *and* upper closed), the swap involution `saddleSwap` that exchanges `cl₁` with `cl₂`, and both halves of Theorem 34.1 — the upper closure is upper closed, the lower closure is lower closed. **Theorem 34.2 is done** (`Saddle/Equiv.lean`): `SaddleEquiv` (`cl₁` and `cl₂` agree), `ClosedSaddleFn` (both closures are equivalent to `K`), the order interval `saddleClass K̲ K̄`, and the theorem itself — on the interval of a closure pair both partial closures are *constant*, equal to the two ends, so the interval lies in one equivalence class and all of its members are closed; conversely a closed concave-convex `K` determines a unique closed convex bifunction whose brackets are `cl₂ K` and `cl₁ K`, and `K` lies in the interval they span. **Thm 34.2's `ri` and `dom` clauses, Cors 34.2.1–34.2.4, and Thms 34.3–34.5 with Cor 34.5.1 are done** (`Saddle/Kernel.lean`): `domSaddle`, `ProperSaddleFn`, the structural characterisation `closedSaddleFn_iff_saddleStructure` (Thm 34.3), the **kernel** — a *total* function, `K` on `ri (dom₁ K) ×ˢ ri (dom₂ K)` and `⊤` off it, so that Thm 34.4 is one equation rather than a rectangle equality plus a transport — with `saddleEquiv_iff_kernel_eq` (Thm 34.4), `SimpleSaddleFn` and `exists_unique_saddleEquiv_class_of_kernel` (Thm 34.5), and the simple extensions `lowerSimpleExt` / `upperSimpleExt` with `exists_unique_saddleEquiv_class_of_finite` (Cor 34.5.1) and `mem_saddleClass_simpleExt_iff` (Cor 34.2.4). Theorem 34.1 is **reproved without duality** there (`lowerCl_idem` is four lines from monotonicity and idempotence of `cl₁`/`cl₂`), which makes it layer B rather than layer C. Cor 34.2.1's `dom L = dom K` clause needs no closedness, and Cor 34.2.4 needs neither Cor 33.3.3 nor joint continuity — separate continuity in each variable on the closed `C`, `D` suffices |
| §28, §35–§39 | **§28 is done** (`Optimization/Program.lean`): `feasibleSet`, `programLagrangian`, `optimalValue`, `IsKuhnTuckerVector`, **Theorem 28.2** under Slater's condition and Corollaries 28.2.1, 28.2.2, plus the equality-constrained variant. It needs no `ineqBifun`, and it was never blocked — Theorem 21.2 as formalized keeps the affine constraints in a second index type, which is the mixed form §28 wants. **§35's continuity and convergence half is done — Thms 35.1–35.5** (`Saddle/Continuity.lean`): `ConcaveConvexOn`, Theorem 35.2 for a family indexed by an arbitrary type, Theorem 35.1 in both its Lipschitz and its continuity clause, **Theorem 35.3** (joint continuity in a locally compact parameter), **Theorem 35.4** and **Theorem 35.5** (Arzelà–Ascoli for saddle-functions), together with `exists_isCompact_mem_nhdsWithin_relint` and `exists_isCompact_collar_relint` — `ri C` is locally compact, and a compact subset of it has a compact *relative collar*, which is what replaces `IsCompact.exists_cthickening_subset_open` in every `ri` proof. **§35's differential half is done too — Thms 35.6–35.8 with Cors 35.7.1 and 35.8.1** (`Saddle/Differential.lean`): `dirDerivReal` with a real-valued §23 API around it, `subgradientFst`/`subgradientSnd`/`subgradientSaddle` bridged to the §23 subdifferentials of the slices, and `HasSaddleGradientAt`. Theorem 35.8's converse comes from Cor 35.7.1 rather than from Thm 35.4's rescalings, and Thm 35.7 needs one step the book calls immediate — *continuous* convergence along a moving sequence, `tendsto_eval_prod_of_tendsto`. **Thms 35.9 and 35.10 are done** (`Saddle/Rademacher.lean`): local Lipschitzness from Theorem 35.1 on a ball feeds Mathlib's Rademacher for the a.e. and density clauses, and Corollary 35.7.1 / Theorem 35.7 with the subdifferentials collapsed by Theorem 35.8 give the continuity of `∇K` and the convergence of gradients, uniformly on compacts. **§36 is done in full and §37 through Cor 37.1.1** (`Saddle/Minimax.lean`): `IsSaddlePoint`, `maximin`/`minimax`, `HasSaddleValue` — which is *only* the equality of the two iterated extrema, finiteness staying a separate conclusion, or Cor 36.3.1 would be vacuous — Lemmas 36.1 and 36.2, Theorem 36.3 with Cor 36.3.1, Theorem 36.4, the Lagrangian `saddleLagrangian` of a closed convex bifunction with Theorem 36.5, and Kuhn–Tucker in the form of Theorem 36.6; then `inverseBifun` (`F_*`), the two conjugate saddle-functions `K̲*`/`K̄*`, **Theorem 37.1** in both equations and **Cor 37.1.1**. **Thm 29.3 and Cor 30.5.1 come out of it** — both were recorded as blocked on §36. Cors 37.1.2–37.1.3 need the biadjoint identity `(F_*^*)^* = F_*` and Thm 37.2 needs Thm 6.8; **all of §37 is now done** (`Saddle/{Conjugate,Subgradient,Existence,Monotone}.lean`), including the unbounded minimax theorem, Thm 37.5's four equivalent conditions, and both clauses of Cor 37.5.1 with Cor 37.5.2 — the last two by instantiating Cors 31.5.1 and 31.5.2 at `prodPairing (innerₗ U) (innerₗ X)`, which is what generalizing `Optimization/Prox.lean` over a self-pairing bought. Only Cor 37.5.2's "in particular" clause for a differentiable `K` is left. **Part VIII is largely done**: `Bifunction/Algebra.lean` carries §38's convex algebra — `infConvBifun`, `smulRightBifun`, `imageBifun`, `compBifun`, `invBifun`, `lowerAdjointBifun`, and the inner product `fenchelSup`/`fenchelInf` — with Thms 38.1, 38.3, 38.4, 38.5, Lemma 38.6, Cor 38.7.1 and **Thm 38.7**, the identity that moves adjoints across the inner product; weak duality for `⟨f, g⟩` turns out to be unconditional, which is what makes every attainment claim a single inequality, and Rockafellar's `⟨f, g⟩` is *not* §31's Fenchel setup — it pairs a convex `f` on `E` with a concave `g` on the paired space, so Lemma 38.6 cannot be derived from `fenchel_duality`. `Bifunction/Process.lean` carries §39's `ConvexProcess` as a `PointedCone ℝ (U × X)`, with Thms 39.1, 39.2 and **Cor 39.7.1** — which is Thm 9.1 rather than a specialization of Thm 39.7, so the barrier-cone prerequisite drops out of the plan — and the §38↔§39 dictionary through `indicatorBifun`. §39's orientation remark is load-bearing: `adjointProcess` and `coadjointProcess` must be separate definitions, or `A** = cl A` is false. **Thms 38.2, 38.3 and 38.5's adjoint formulas are done, with Cors 38.4.1 and 38.5.1**; what is left of §38 is **Cor 38.2.1** — infimal convolution in the *first* bifunction variable — and **Cor 38.7.2**, which Rockafellar derives from it. **§39 is done through Thm 39.8**: Thms 39.3 and 39.4 in `Bifunction/ProcessDuality.lean` (they are Thms 33.1–33.3 and Cor 33.2.1 read at the indicator bifunction of a process), Thms 39.5, 39.6 and 39.8's adjoint formulas, and both halves of Thm 39.7. The *closed* halves of Thms 39.5 and 39.8, and the infimum-oriented mirrors of Thms 39.3/39.5/39.8, remain; the closed halves specialize Cor 38.2.1. `concaveConj` and its §12 mirror (`Duality/ConcaveConj.lean`) are in place and are what §§29–31 run on |

**The D5 interfaces are populated.** `Duality/Relint.lean` now proves `IsExactImage.of_relint`
(Theorem 16.3) and `IsExactSum.of_relint` (Theorem 16.4), so §16's exact rows, §23.8, §23.9 and
Cor 23.8.1 all have supplied instances and the whole chain §9 → §13 → §16 → §23 is closed. The two
constructors are pure assemblies: Thm 9.2 (images) or Cor 9.1.1 (sums), plus Thm 13.3 to turn a
recession hypothesis about `f*` into one about `dom f`, plus `eq_of_isMaxOn_of_mem_relint` /
`eq_zero_of_nonpos_of_mem_relint` from §6 to turn that into Rockafellar's `ri` condition.

**§9 is complete.** Theorem 6.7 turned out to be Theorem 9.5's last missing prerequisite — its
closure formula is Theorem 6.7 applied to `epi g` — and the `ri` form of Theorem 7.5 its second,
since a sum of functions is no set operation on epigraphs and Theorem 9.3 has to be proved by
segment limits. Theorems 9.6–9.8 then needed the *convex cone generated by a set*, and it turned
out nothing had to be defined: `PointedCone.hull ℝ` **is** that cone, and
`PointedCone ℝ E = Submodule ℝ≥0 E` supplies monotonicity, idempotence, `Submodule.span_induction`
and the Galois insertion for free. The one genuinely missing bridge was Rockafellar's description
`{0} ∪ ⋃_{t>0} tC` of the hull of a *convex* set (`coe_hull_of_convex`), and every result in
`Recession/ConeHull.lean` runs through it.

**§5's generating operator has one canonical definition, and it is in `Recession/ConeHull.lean`.**
`posHomGen f = ofEpi (PointedCone.hull ℝ (epi f))` — the greatest positively homogeneous *convex*
minorant of `f` that is nonpositive at the origin, with convexity and maximality carrying no
hypothesis on `f`. `Duality/Level.lean` holds the ray description
`posHomGenCone f = {0} ∪ ⋃_{a>0} a • epi f`, the identification `posHomGenCone_eq_coe_hull` for
convex `f`, and every formula Rockafellar states against it. The two were independently developed
by two agents and collided at the top-level import; the episode is recorded as gotcha 74 in
`NOTES.md`.

**§10 is complete through Theorem 10.5.** Two things it did not cost. Theorem 10.4 needed no new
analysis: `exists_chart_retraction` packages the Theorem 10.1 chart with a *continuous linear*
retraction, and a bounded linear map transports Lipschitz constants as readily as it transports
continuity, so the `ri` form is the `interior` form read through the chart. And Theorem 10.2 needed
no triangulation: Rockafellar reduces it to the case of a vertex by triangulating the simplex
around `x`, a step he calls "intuitively obvious" and does not prove, but the weight identity
`w = (1 - e) mu + e ((w - (1 - e) mu) / e)` handles an arbitrary point of the simplex directly —
see the module docstring of `Simplicial.lean`. Theorems 10.6–10.9 are the equi-Lipschitz and
convergence results, and §24 has since consumed them — though less of them than expected: Thm 24.7
needs only Thm 10.4, and Thm 24.6's first assertion needs only Thm 10.1, because replacing the
vanishing step of a difference quotient by a fixed larger one moves the continuity to *interior*
points — and that same observation retired §24's one remaining request, an `EReal`-valued
Cor 10.8.1: under Theorem 24.6's own hypotheses the approaching points are eventually interior, so
the existing form, which consumes finite convex functions on an open set, applies verbatim. §10 has
no outstanding consumers left in §24.

**`IsExactSum.of_continuousAt` is proved** (`Duality/Continuity.lean`), so the D5 interfaces now
have two independent suppliers: Rockafellar's `ri` condition in finite dimensions, and continuity
of one summand in an arbitrary real TVS. The open question of §8 is answered — it *is* cheap. Two
convex sets in `E × ℝ` do the work: the strict epigraph of `f`, whose interior is nonempty exactly
because `f` is continuous at `x₀`, and the hypograph of the concave `x ↦ ⟨x, y⟩ - a - g x`. They
are disjoint precisely when the conjugate inequality to be proved fails, and
`geometric_hahn_banach_open` separates them without any local convexity, because one of them is
open. The remaining step —extending the strict estimate from the interior to the whole strict
epigraph — is `Convex.closure_interior_eq_closure_of_nonempty_interior`.

**Theorem 19.1 — Minkowski–Weyl — is proved**, and with it the gate to §19–§22 is open. It cost
two files and no Carathéodory. Weyl's half (finitely generated ⇒ polyhedral) is Fourier–Motzkin,
run once, in the form "adding a ray to a polyhedral cone leaves it polyhedral"; it is purely
algebraic. Closedness of a finitely generated cone — which Rockafellar proves from Carathéodory as
a *prerequisite* — then falls out for free, because a polyhedral cone is a finite intersection of
closed half-spaces. Minkowski's half is then separation in the dual, using
`geometric_hahn_banach_closed_point` and reflexivity, with no polar calculus and no choice of
pairing. The set-level theorem is the cone theorem plus one homogenisation identity,
`slice_hull_union`: the level-one slice of the cone generated by `{1} × P ∪ {0} × D` is
`conv P + cone D`.

**The polyhedral calculus is in.** Each operation is proved on whichever side of Theorem 19.1
makes it trivial: intersections and affine preimages on the *inequality* side (concatenate the
systems, compose the functionals), images and sums on the *generator* side (push the generators
forward, add the point sets and unite the direction sets). The first pair needs no
finite-dimensionality at all. `PolyhedralFn f` is `Polyhedral (epi f)`, and the calculus
immediately gives that `dom f` and every sublevel set are polyhedral, and that the indicator of a
polyhedral set is a polyhedral function — which is what will let the §20 qualifications apply to
constraint *sets*.

§19 is now complete. Theorems 19.6 and 19.7 — the closed convex hull of a union, and the closed
convex cone generated by a set — are each stated as a conjunction (finitely generated, *and* equal
to the plain construction plus the recession cones), which is what makes Rockafellar's `0⁺`
substitution convention unnecessary; each is proved by a three-set sandwich against the finitely
generated set built from the pooled generators. See `04-representation.md` §4.3.

**§17's point case is done too**, and it filled a real Mathlib gap: `IsCompact.isCompact_convexHull`
(Mathlib has only `Set.Finite.isCompact_convexHull`). The step Mathlib was missing is the *fixed
index*: Carathéodory gives an affinely independent subset of at most `n + 1` points, and padding it
out to exactly `n + 1` — repeating one point with weight zero — turns `convexHull ℝ S` into the
image of `stdSimplex ℝ (Fin (n+1)) ×ˢ Sⁿ⁺¹` under a continuous map, after which compactness is one
line and Theorem 17.2 (`cl (conv S) = conv (cl S)` for bounded `S`) is two.

**§17's points-and-directions form is done too**, and it needed a *conical* Carathéodory
(`exists_linearIndepOn_of_mem_coneHull`) which Mathlib does not have — Rockafellar's own proof
reduces Theorem 17.1 to exactly that statement in `R^{n+1}`. Corollaries 17.1.1–17.1.6 are left with
Theorem 13.5, since the "different `Cᵢ`" coalescing they need buys nothing while Theorem 21.3 is
blocked.

**§18's facial structure is done**, and it corrected a guess in sub-plan 4: Rockafellar's *face* is
**not** Mathlib's `IsExtreme ℝ C C'` even for convex `C` — `{0, 1}` is extreme in `[0, 1]` but is
not convex, hence not a face — so `IsFace` is a structure extending `IsExtreme ℝ` with a convexity
field. Theorems 18.1 and 18.2 are Rockafellar's, and the bounded case of Theorems 18.4 and 18.5
gives **Minkowski's theorem**, `conv (ext C) = C` for compact convex `C`, which is genuinely
stronger than Mathlib's Krein–Milman (`closure_convexHull_extremePoints`) and is not in Mathlib.
The unbounded half of §18 waits on a definition of `conv S` for a set `S` of points *and*
directions; see the "What is not here" section of `Face.lean`.

**§24 is done except for Rockafellar's integral formula for the primitive.**
`IsCyclicallyMonotone` is stated with cycles as `List (E × F)` rather than `Fin (m+1)`-indexed
families, which makes every proof a list induction and keeps Rockafellar's potential manifestly a
supremum of `affineFn`s. Nothing like it exists in Mathlib — there is no monotone-operator theory
there at all. Theorem 24.3 is stated as *the maximal monotone relations on `ℝ` are exactly the
`∂f` of closed proper convex `f`*, maximal monotone relations being the maximal chains of `ℝ × ℝ`
for the coordinatewise order — which is what Rockafellar's "complete non-decreasing curves" are.
Two corrections with consequences. **Theorem 24.9's uniqueness clause needs neither 24.1–24.3 nor
one-dimensional restriction**, only Theorem 23.5 and the same argument on the conjugate side, and
`increment_eq_of_subgradientRel_subset` needs neither convexity nor closedness of `g`. And
**Theorem 24.2's existence clause needs no integration theory**: what the primitive has to be is
determined by its graph, `monotoneCurve φ` is that graph as a complete non-decreasing curve, and
Theorem 24.3 — proved through cyclic monotonicity, hence not circular — hands back a closed proper
convex `f` realising it. Only the *formula* `f(x) = ∫ₐˣ φ` and Corollary 24.2.1 still need an
integral, and nothing downstream asks for them.

**§25's Theorem 25.1 is done**, and it forced a decision about what "differentiable" means for an
`EReal`-valued function: `HasFDerivAt` needs a normed target, so differentiability of `f` at `x` is
expressed by a local real representative — `f =ᶠ[𝓝 x] fun z => (g z : EReal)` together with
`HasFDerivAt g f' x`. That is exactly Rockafellar's hypothesis (his `∇f x` presupposes `f x`
finite), it yields Corollary 25.1.1 as two one-line consequences, and it is the form §26 needs, where
the functions of interest are `+∞` off an open set. The proof never touches `dirDeriv`: the
one-sided limit of the difference quotient along a ray gives both halves, and the uniqueness half
uses neither convexity nor properness.

**§26 turned out not to be self-contained**, contrary to sub-plan 5's guess. Theorem 26.1
("`∂f` single-valued ⟺ `f` essentially smooth") needs Theorem 25.6 in one direction and the
sufficiency half of Theorem 25.2 in the other, and Theorems 26.3, 26.5 and 26.6 all route through
it. **Theorem 26.4** does not, and was done first: `f*(∇f x) = ⟨x, ∇f x⟩ - f x`, which is exactly
"the Legendre conjugate is the restriction of `f*` to the range of `∇f`", together with its
well-definedness.

Once Theorem 25.6 arrived, the rest followed quickly, because §26 is almost entirely bookkeeping on
top of two facts: for an essentially smooth `f`, gradient and subgradient are the same relation
(`hasGradientAt_toDual_iff_mem_subgradient`), and `∂f* = (∂f)⁻¹` (Corollary 23.5.1). Theorem 26.5's
duality is then Corollary 26.3.1 applied on both sides, with `and_comm` doing the actual work:
`LegendreType f` says `∂f` is single-valued and injective, and inverting `∂` swaps the two.

**§27 is as complete as the upstream gaps allow.** `Optimization/Minimum.lean` carries `argmin`,
Theorem 27.1(a) (`inf f = -f*(0)`, which needs no hypothesis at all), Theorem 27.1(b)
(`argmin f = ∂f*(0)`, Fenchel–Moreau plus Theorem 23.5), Theorem 27.2 in all three of its
assertions — existence, compactness, and ε–δ well-posedness — with Corollaries 27.2.1 and 27.2.2,
and **Theorem 27.4**, the optimality condition `0 ∈ ∂h x + N_C(x)`, whose sufficiency half needs no
hypothesis and whose necessity half is stated against `IsExactSum` so that Rockafellar's `ri` and
polyhedral hypotheses both instantiate it.

**Theorem 27.3's non-polyhedral case came free from Theorem 9.3.** `recessionFn_add` already gave
`(h + δ(·|C))0⁺ = h0⁺ + δ(·|0⁺C)`, and because an indicator's recession function only takes the
values `0` and `⊤`, the recession cone of the sum splits as `0⁺h ∩ 0⁺C` — a split that fails for
sums in general. Corollary 27.3.3's non-polyhedral half then follows by Corollary 8.3.3 and
Theorem 8.7. The polyhedral refinement does **not** need Helly, contrary to Rockafellar's derivation
from Theorem 21.5: the directions of constancy of the objective form a subspace, and projecting `E`
along it leaves the objective unchanged while collapsing the common recession cone to `{0}`, which
is the general case. Polyhedrality of the constraint set enters only through
`Polyhedral.recessionCone_image` — a linear map commutes with `0⁺` on a polyhedral set and, in
general, on no other kind. The same projection strengthens the general case to Rockafellar's
constancy/linearity recession hypothesis.

**§31's Theorem 31.1 came out of §27.1(a) and §16.4 with no separation argument.** Rockafellar
proves Fenchel's duality theorem by separating the epigraph of `f` from the hypograph of `g + α`.
In this development the separation has already happened once, inside Theorem 16.4, so the theorem
reduces to `inf h = -h*(0)` applied to `h = f + (-g)` plus the sign dictionary
`neg_concaveConj`. Rockafellar's four hypotheses — (a), (b) and their two polyhedral weakenings —
are all instances of `IsExactSum`, so one proof covers them; condition (b) is literally condition
(a) applied to the pair `(f*, g*)` over `B.flip`, with Fenchel–Moreau collapsing the biconjugates,
and that is what turns attainment of the supremum into attainment of the infimum. Weak duality is
unconditional: both `∞ - ∞` collisions land on the side that makes the dual value `-∞`.

**Theorems 31.4 and 31.5 both skipped Theorem 31.1 and went to its source.** Rockafellar derives
the conic duality of Theorem 31.4 from Fenchel's theorem at `g = -δ(· | K)`, and Moreau's Theorem
31.5 from Fenchel's theorem at `g = -w(z - ·)`. In both cases the concave detour is avoidable:
`δ(· | K)` and `w(z - ·)` are ordinary convex functions, so the argument that proves Theorem 31.1
— Theorem 27.1(a) applied to the sum, then `IsExactSum.conj_add_apply` at the origin — applies
directly, and the sign flip `y ↦ -y` that the splitting produces is exactly what turns `K°` into
Rockafellar's `K*`, and `⟨z, y⟩ + w y` into `w(z - y) - w z`. Moreau's theorem therefore needs
neither finite dimensions nor `ri`: `w(z - ·)` is continuous everywhere, so
`IsExactSum.of_continuousAt` supplies the constraint qualification in any real Hilbert space. The
one thing the shortcut costs is that the final cancellation needs the dual value to be a real
number, which is why `Optimization/Moreau.lean` carries `infConv_quadFn_ne_top` and its three
companions.

**§32 cost almost nothing, because §18 had already paid for it.** The maximum principle is
Theorem 6.4's prolongation lemma (`exists_one_lt_smul_mem_of_mem_relint`) plus one application of
`ConvexFn.epi_combo`: prolonging past the maximiser writes it as a proper convex combination of a
cheaper point and a point of `C`, which puts `f z` strictly below itself. Corollary 32.1.1 is then
Theorem 18.2 (`exists_isFace_mem_relint`) with the maximum principle applied to the face. Theorem
32.2 does not need a Carathéodory decomposition at all — the sublevel set `{z | f z ≤ α}` is convex
and contains `S`, so it contains `conv S`, and the *strict* sublevel set handles the attainment
clause the same way; both halves live over `Module ℝ E` with no topology. Corollary 32.3.2 for
compact `C` is Minkowski's theorem fed to Theorem 32.2. Theorem 32.4 was expected to route through
Theorem 23.7 (`∂f x ⊆ N_lev(x)`) and instead came out in three lines, because the subgradient
inequality and maximality sandwich the pairing term between `f x` and `f x`. Theorem 32.3 and Corollary 32.2.1 were later
completed against the *unbounded* half of §18 (`Representation.lean`): the only analytic ingredient
beyond Theorems 18.4–18.5 is that a convex function bounded above on a half-line is non-increasing
along it. The attainment clause of Corollary 32.3.2 needs Theorem 10.1 *and* `C ⊆ ri (dom f)` — it
is false for a merely compact `C ⊆ dom f`. Corollaries 32.3.1 and 32.3.4 turned out to be already
proved, only unlabelled — the session that wrote the file had no copy of the book. **Corollary
32.3.3** closed §32: naming its hypothesis `BddAboveOnRays f C` — `f` bounded above on every
half-line of `C`, which through the degenerate rays also says `C ⊆ dom f` — generalises the
existing chain without a new idea, because the hull-domination lemma only ever used its uniform
bound on the one half-line it constructs. The lineality space is quotiented out by
`eq_add_inter_of_isCompl`, which gives `C = L + (C ∩ N)` for *any* complement `N` of `L`, so
Rockafellar's `L^⊥` and its inner product are not needed; the maximiser is an extreme point of
`C ∩ N` and depends on `N`, which is why the corollary claims attainment and nothing more.

**The bifunction chain (§§29–30) confirmed D8 and cost three short files.** `Bifun U X` is a
curried `U → X → EReal` and `ConvexBifun` is convexity of its graph function, so Theorem 29.1's
convexity clause is `convexFn_iInf_right` — Theorem 5.7 at a projection — with no new argument, and
`dom (inf F) = dom F` is `dom_iInf_right`. The one place the plan had flagged a risk was the
definition of `KuhnTucker`: defining it by the inequality would have made Theorem 29.1 an
`Iff.rfl`. The book (line ≈11740) defines it as "`⨅ u {⟨u, v⟩ + inf F u}` finite and equal to
`inf F 0`", the file follows that, and the inequality form drops out because evaluating the
infimum at `u = 0` already bounds it by `inf F 0`. The payoff is `KuhnTucker B F = -(∂(inf F)(0))`
as sets, after which convexity, closedness and nonemptiness under strong consistency transfer from
`Subgradient/{Defs,Existence}.lean` through `Set` negation.

**The Lagrangian and the adjoint are both conjugates, and neither needed a reflected pairing.**
`lagrangian B F v x = concaveConj B (fun u => -(F u x)) v` holds on the nose — `a - (-b) = a + b`
is the entire proof — so concavity in the price variable is `concaveFn_concaveConj` applied
pointwise, with no hypothesis on `F` at all. For §30 the plan expected `negFst (prodPairing Bu Bx)`
to carry Rockafellar's sign flip; reading `⟨u, -v⟩ + ⟨x, y⟩` as the pairing of `(u, x)` with
`(-v, y)` is cheaper, because it keeps `conj` for the *plain* `prodPairing` and lets
`convexFn_conj` plus `convexFn_compLin` prove Theorem 30.1's concavity clause in three lines. What
both files really needed was `Tdaf.EReal.iInf_add_coe` — a *real* constant passes through an
infimum on `EReal` — which is what makes `⨅ x L(v, x) = ⨅ u {⟨u, v⟩ + inf F u}` and Theorem 30.2
rewrites rather than proofs. Closedness of `F*` is the one clause left half-done: it is
`closedFn_conj` transported along a linear reflection, but `Operations/Image.lean` has
`convexFn_compLin` and no `ClosedFn` counterpart, so it is recorded as missing rather than faked.

**One missing lemma was blocking two sections, and it was three lines.** Mathlib has
`Continuous.comp_lowerSemicontinuous` — the *outer* composition — but not the inner one, `g ∘ φ`
lower semicontinuous for `g` lower semicontinuous and `φ` continuous, which is immediate from
`lowerSemicontinuous_iff_isOpen_preimage`. `Operations/Closed.lean` now carries it together with
`closedFn_compLin`, the closedness half of Theorem 5.7, and that finishes Theorem 30.1 apart from
`F** = cl F` and makes Theorem 33.2's first equation a two-line consequence of the §30 ↔ §33
bridge. `Operations/Image.lean` stays layer A; the topological facts live in the new file.

**Theorem 30.1's biconjugation is a reindexing, and the product instance is what unlocked it.**
`F*` is a conjugate at the reflected point `adjointSwap q = (-v, y)`, and `F**` is the concave
adjoint of that at the same reflection; the two reflections do not cancel by a sign lemma but by
`Function.Surjective.iSup_comp` — `adjointSwap` is onto, so the supremum over `Y × V` *is* the
supremum over `V × Y` that the biconjugate takes. What was actually missing was Fenchel–Moreau on
`U × X`: `Duality/Pairing.lean` had no product instance, so `IsCompatiblePairing (prodPairing …)`
would have had to be a hypothesis. It is now derived from the factors
(`instIsCompatiblePairingProd`), the surjectivity half being the splitting
`g (u, x) = g (u, 0) + g (0, x)` of a continuous functional on a product.

**§34's Theorem 34.1 needed one two-line lemma and one involution.** The closure operations
terminate because *the adjoint does not see the closure*: `(cl F)* = F*`, which is `conj_clFn` on
the graph function. With that, `cl₁ cl₂ K` is `⟨u, F* y⟩` for `F = bifunOfSaddle Bx K`, closing it
convexly gives `⟨(cl F) u, y⟩`, and closing *that* concavely gives `⟨u, (cl F)* y⟩ = ⟨u, F* y⟩`
again. The lower half is the upper half applied to `saddleSwap K = -K` with the arguments
exchanged, an involution which turns `cl₁` into `cl₂`; the price is that the swapped pairings are
`Bx.flip` and `Bu.flip`, so §34's lower half asks for compatibility on both sides of both pairings
and `Duality/Pairing.lean` gained `instIsCompatiblePairingFlipFlip` to match.

**§33 confirmed D8 and corrected it.** The plan's composition law
`conj (prodPairing Bu Bx) = partialConj₁ Bu ∘ partialConj₂ Bx` is false: the left side is a
supremum over `U × X` and the right is a sup-of-inf. The true law routes through the *concave*
conjugate — `adjointBifun Bu Bx F y v = concaveConj Bu (⟨F·, y⟩) v` — and that single identity is
what ties §30's adjoint to §33's bracket and turns Theorem 33.2 into a `biconcaveConj` statement.
The rest of Theorem 33.1 is `conj` applied uniformly in a parameter: convexity and closedness of
`⟨Fu, ·⟩` need no hypothesis on `F` at all, and concavity in `u` is Theorem 5.7 at a projection.
The one book-level correction is `dom₁`/`dom₂`: Rockafellar's are intersections
(`K(u, v) > -∞` for *all* `v`), not the unions the plan had recorded, and only the intersections
are convex. Along the way `clConcave` — the concave closure `-(cl (-g))` that
`Duality/ConcaveConj.lean` had promised "when §34 arrives" — was defined there and concave
Fenchel–Moreau restated against it.

**The §33 correspondence is a uniqueness statement about *slices*, and Theorem 34.2 is an order
argument.** What makes "closed convex bifunctions ↔ lower closed concave-convex functions" a
bijection is `F u = ⟨Fu, ·⟩*` — Theorem 33.1's inversion formula — which recovers `F` from its
bracket as soon as each slice `F u` is closed. That is strictly weaker than closedness of `F`
itself, so `ImageClosedBifun` was added alongside `ClosedBifun`, with `ClosedBifun.imageClosedBifun`
one way and no converse. Theorem 34.2 then needs no new duality at all: once Theorem 33.2 is read
as saying the two brackets of a closed convex bifunction are a *closure pair* `cl₁ K̲ = K̄`,
`cl₂ K̄ = K̲` (`partialCl₁_bracket`, `partialCl₂_concaveBracket_adjoint`), monotonicity of the
partial closures squeezes `cl₂ K` between `cl₂ K̲ = K̲` and `cl₂ K̄ = K̲` for every `K` in the
interval. Both closures are therefore constant on the interval, which is simultaneously the
"one equivalence class" clause, the "every member is closed" clause and the identification of the
two ends as the lower and upper closed representatives.

Next, in dependency order: the rest of §34 (`Saddle/Equiv.lean`: kernels, `dom K = dom F × dom F*`,
Thms 34.3–34.5), which rests only on `ri`; then §§35–39
(`Saddle/{Continuity,Minimax}`, `Bifunction/*`), which unblock Thms 28.3 and 31.2 — Thm 29.3 and Cor 30.5.1 came out of §36 already, and Thm 29.4 turned out never to have needed §36 or §37 at all.
Corollaries 33.1.3 and 33.2.2 want polyhedral bifunctions. §15 plus Thms 9.6–9.8 and §22 remain the Part-III/IV
gaps, and §28's `ineqBifun` waits on mixed inequality/equality alternatives in `Helly.lean`. Theorem 13.5 unblocked the rest of §17's corollaries, all of §21.3–21.5 (now done),
the polyhedral half of Theorem 27.3 and Theorem 27.1(g) at once; §24.5–24.7 are now done, so what
Theorems 10.6–10.9 still unblock is, through Theorems 25.5–25.6, the rest of §25 and §26.

| module | contents |
|---|---|
| `Tdaf/Order/EReal.lean` | §4's arithmetic conventions checked against `EReal`; order/negation/`⨆` helpers |
| `Analysis/Convex/Epigraph.lean` | `epi`, `dom`, `Proper`, `restrict`, `ConvexFn`; **Thms 4.1, 4.2, 4.6**; `dom_eq_fst_image_epi`; the Mathlib bridge |
| `Analysis/Convex/Indicator.lean` | `indicatorFn` and its epigraph/domain/convexity/translation |
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
| `Continuity.lean` | **Thms 10.1, 10.4, 10.5** and Cors 10.1.1, 10.5.1–10.5.2 — continuity on `ri (dom f)`, Lipschitz continuity on compact subsets of it, and the uniform-continuity criterion "`f0⁺` finite"; plus the linear chart (with its continuous retraction) that reduces `ri` to `interior` |
| `Caratheodory.lean` | **Thms 17.1 (points), 17.2** — Carathéodory with a fixed index, and compactness of the convex hull of a compact set |
| `Polyhedral/Cone.lean` | `PolyhedralCone`, `FinitelyGeneratedCone`, **Minkowski–Weyl for cones**, and closedness of both |
| `Polyhedral/Defs.lean` | `Polyhedral`, `FinitelyGenerated`, `coneOver`, the homogenisation dictionary, **Thm 19.1** and Cor 19.1.1 |
| `Polyhedral/Ops.lean` | the polyhedral calculus — intersection, affine preimage, product, image, sum, difference, dilation (**Thm 19.3**), the recession cone (**Thm 19.5**) and strong separation (**Cor 19.3.3**) |
| `Polyhedral/Function.lean` | `PolyhedralFn`; closedness, the polyhedral effective domain and sublevel sets, the indicator of a polyhedral set, sums (**Thm 19.4**) and infimal convolutions (Cor 19.3.4) |
| `Polyhedral/Conjugate.lean` | **Thm 19.2** — the conjugate of a polyhedral function is polyhedral, read off the epigraph |
| `Polyhedral/Duality.lean` | **Thm 20.1** and the polyhedral pair case — `IsExactSum.of_polyhedral{,_pair}` |
| `Polyhedral/Separation.lean` | **Thm 20.2** and **Cor 20.2.1** — proper separation from a polyhedral set, and its support-function form |
| `Polyhedral/Closedness.lean` | **Thm 20.3** and **Cor 20.3.1** — `C₁ + C₂` closed, and strong separation, under a one-sided recession hypothesis |
| `Polyhedral/Simplicial.lean` | **Thms 20.4 and 20.5** — polyhedral approximation from inside `int D`, and local simpliciality (which discharges Thm 10.2's hypothesis for polyhedral sets) |
| `Face.lean` | `IsFace` (Rockafellar's face = Mathlib's `IsExtreme ℝ` **plus** convexity), **Thms 18.1 and 18.2**, Cors 18.1.1–18.1.3, and — for compact `C` — **Thm 18.4** and **Minkowski's theorem** `convexHull ℝ (C.extremePoints ℝ) = C` (Cor 18.5.1), which Mathlib does not have |
| `Helly.lean` | **Thms 21.1, 21.2** — the theorems of the alternative that §§27–28 run on — plus **Thm 21.3** with Cors 21.3.1–21.3.2, **Thm 21.6** (Mathlib's `Convex.helly_theorem'`) and Cors 21.6.1, 21.6.2 |
| `HellyRefined.lean` | **Thms 21.4, 21.5** — Theorem 21.3 and Helly's theorem with the recession hypothesis weakened to "finitely many members affine (resp. polyhedral), the rest constant (resp. linear) in every common direction of recession" |
| `Duality/Barrier.lean` | **Cor 14.2.1** — the polar of the barrier cone is the recession cone |
| `Simplicial.lean` | `IsSimplex`, `LocallySimplicial`, **Thms 10.2 and 10.3** — upper semicontinuity relative to a locally simplicial set, and the extension of a convex function from `ri C` to `C` |
| `Recession/Cone.lean` | §8's set half, layered A/B/D |
| `Recession/Closedness.lean` | **Thms 9.1–9.5, Cors 9.1.1–9.1.3** — when a linear image is closed, and the closure of a sum, a supremum and a composition |
| `Recession/Conjugate.lean` | **Thm 13.3** — `(f*)0⁺ = δ*(· \| dom f)`, and `constancySpace_conj` |
| `Duality/Pairing.lean` | dual pairs, adjoint pairs, product pairings, the dual of `E × ℝ` |
| `Duality/Conjugate.lean` | **Theorems 12.1 and 12.2 — Fenchel–Moreau**; **Thm 12.3**, the four elementary conjugacy rows and the combined formula, all layer A |
| `Duality/Exact.lean` | `IsExactSum`/`IsExactImage` (D5); the unconditional halves of **Thms 16.3, 16.4** and the exact halves derived from the interfaces |
| `Duality/Continuity.lean` | `IsExactSum.of_continuousAt` — the constraint qualification that survives into infinite dimensions; `ConvexFn.convex_strictEpi` |
| `Duality/ConcaveConj.lean` | `concaveConj` (D2), the sign dictionary, §12 mirrored for concave functions, and `clConcave` — the **concave closure** — with `biconcaveConj_eq_clConcave` |
| `Duality/Ops.lean` | the §16 dual-operations table — **Thms 16.1, 16.3, 16.4, 16.5**, unconditional halves plus the `clFn` forms |
| `Duality/Relint.lean` | **the `of_relint` constructors** — Rockafellar's own constraint qualification for **Thms 16.3 and 16.4**; the only file that *produces* a D5 interface |
| `RelativeInterior.lean` | §6, and **every result stages 2–3 deferred to it** |
| `Recession/Function.lean` | §8's function half — Theorems 8.5–8.8 |
| `Duality/Support.lean` | §13, with `supportEquiv` for the one-to-one correspondence |
| `Duality/Polar.lean` | §14 up to Theorem 14.5, polarity as a `GaloisConnection`, and the **conjugate of a partial affine function** (§12, the display before Thm 12.3), which has to be here because its dual datum is a polar |
| `Duality/Gauge.lean` | §15 — `gaugeFn`, `IsGauge`, `IsNorm`, `polarGauge`, `polarFn`, `obverse`, the three correspondences as `Equiv`s, and **Thms 14.6, 14.7, Cor 14.6.1** |
| `Duality/GaugeLike.lean` | **Thm 12.4** in one dimension and **Thm 15.3** in full, with Cors 15.3.1–15.3.2: the monotone conjugate on the half-line, and the gauge-like closed proper convex functions as the composites `g ∘ k` |
| `Duality/InnerPairing.lean` | `IsInnerPairing` / `IsContinuousInnerPairing` — a space paired with **itself** by a symmetric positive definite form, with `pairingNorm`, Cauchy–Schwarz, polarization (so `IsContinuousPairing` and its flip come for free) and the product instance `prodPairing (innerₗ U) (innerₗ X)` that §37 runs on |
| `Subgradient/Defs.lean` | §23 — the first subgradient anywhere in the Lean ecosystem |
| `Subgradient/Monotone.lean` | §24 — cyclic monotonicity and **Theorems 24.8 and 24.9**, the characterisation of subdifferentials. Mathlib has no monotone-operator theory |
| `Subgradient/OneDim.lean` | §24 — `rightDeriv`/`leftDeriv` on `ℝ` and **Theorem 24.3**: the maximal monotone relations on `ℝ` are exactly the subdifferentials |
| `Subgradient/Primitive.lean` | §24 — **Theorem 24.2**: complete non-decreasing curves, and the primitive of a monotone `φ` recovered from its graph rather than from an integral |
| `Subgradient/Integral.lean` | §24 — **Corollary 24.2.1**: a convex function of one variable is the integral of either of its one-sided derivatives |
| `Subgradient/Rademacher.lean` | §25 — **Theorem 25.5**: a convex function is differentiable almost everywhere, and densely, on the interior of its effective domain, and `∇f` is continuous there; **Corollary 25.5.1**; **Theorem 25.4**'s measure-zero clause |
| `Subgradient/GradientLimit.lean` | §25 — **Theorem 25.7**: gradients of convex functions converging pointwise on an open convex set converge, uniformly on compact subsets |
| `Subgradient/Reconstruction.lean` | §25 — **Theorem 25.6**: `∂f x = cl (conv S(x)) + N_{dom f}(x)`, the subdifferential at an arbitrary point assembled from limits of gradients and normal directions |
| `Subgradient/Convergence.lean` | §24 — **Theorems 24.5 and 24.6**: what `∂f` and `f'(x; ·)` do along a converging sequence |
| `Subgradient/Bounded.lean` | §24 — **Theorem 24.7**: `∂f` carries compact subsets of `int (dom f)` to compact sets |
| `Subgradient/Calculus.lean` | **Thms 23.8, 23.9**, Cor 23.8.1 — the sum and image rules, against the D5 interfaces |
| `Subgradient/Existence.lean` | **Thms 23.4 and 23.10** — `∂f x ≠ ∅` on `ri (dom f)` and on `dom f` for polyhedral `f`, with `f'(x; ·) = δ*(· | ∂f x)` on the nose |
| `Subgradient/Gradient.lean` | **Thm 25.1**, Cor 25.1.1, and the necessity half of **Thm 25.2** — `∂f x = {∇f x}` and `f'(x; v) = ⟨v, ∇f x⟩` where a convex `f` is differentiable; `HasGradientAt` for `EReal`-valued functions |
| `Subgradient/Legendre.lean` | **Thm 26.4** — the Legendre conjugate is `f*` restricted to the range of `∇f`, and `⟨x, y⟩ - f x` does not depend on the choice of `x ∈ (∇f)⁻¹ y` |
| `Subgradient/EssentiallySmooth.lean` | **Thm 26.1** — `EssentiallySmooth`, and `∂f` single-valued everywhere ⟺ `f` essentially smooth, with `dom ∂f = int (dom f)` |
| `Subgradient/StrictlyConvex.lean` | **Thm 26.3**, **Cor 26.3.1** — `StrictConvexOnFn`, `domSubgradient`, `EssentiallyStrictlyConvex`; `f*` essentially smooth ⟺ `f` essentially strictly convex, and `∂f` one-to-one ⟺ `f` essentially smooth and strictly convex on `int (dom f)` |
| `Subgradient/BoundaryDirDeriv.lean` | **Lemma 26.2** — condition (c) of essential smoothness in directional-derivative form; the restriction of a closed proper convex function to a line based at a point *outside* `dom f`, and its right derivative at `0` |
| `Subgradient/Preservation.lean` | **Cors 26.3.2 and 26.3.3** — essential smoothness survives infimal convolution and linear images, stated against `IsExactSum`/`IsExactImage` with the book's `ri` forms as corollaries; the two layer-A transfer lemmas `StrictConvexOnFn.add_convexFn` and `StrictConvexOnFn.compLin` |
| `Subgradient/Cofinite.lean` | **Lemma 26.7** — a finite differentiable convex function is co-finite exactly when `‖∇f‖` blows up at infinity; the range of `∇f` is clopen when it does |
| `Subgradient/LegendreType.lean` | **Cor 26.4.1**, **Thms 26.5 and 26.6** — `gradientRange` (`D`, in vector form), `LegendreType`; `D = dom ∂f*` hence `ri (dom f*) ⊆ D ⊆ dom f*`; `f` of Legendre type ⟺ `f*` is, and `∇f : int (dom f) → int (dom f*)` is a bijection with `∇f* = (∇f)⁻¹`; for finite differentiable `f`, `∇f` is a bijection of `E` onto itself ⟺ `f` is strictly convex with `dom f* = E` |
| `Saddle/Defs.lean` | §33 — `ConcaveConvexFn`, `SaddleFn`, `dom₁`/`dom₂`, `partialConj₂`, `partialCl₁`/`partialCl₂`, the brackets `⟨Fu, y⟩` and `⟨u, G y⟩`, **Thm 33.1** in both directions (the bracket is a concave-convex convex-closed function, `cl (Fu) = ⟨Fu, ·⟩*`, and every such function is a bracket) and **Thm 33.2** in both equations |
| `Saddle/Closure.lean` | §34 — `lowerCl`/`upperCl`, `LowerClosedFn`/`UpperClosedFn`/`FullyClosedFn`, the swap involution, and **Thm 34.1**: each closure is idempotent |
| `Saddle/Correspondence.lean` | §33 — **Thm 33.3** and **Cor 33.3.1**: closed convex bifunctions correspond one-to-one to lower closed concave-convex functions, and to closure pairs `(K̲, K̄)`; `eq_of_bracket_eq` is the uniqueness half |
| `Saddle/Monotone.lean` | §37 — `partialInvertEquiv` (the **partial inversion** of Thm 37.5) with the transfer of maximal monotonicity across it, **Cor 37.5.1**'s homeomorphism clause `((u, y), (v, x)) ↦ (u - v, x + y)` and **Cor 37.5.2** (`ρ` is maximal monotone) |
| `Saddle/Equiv.lean` | §34 — `SaddleEquiv`, `ClosedSaddleFn`, the order interval `Ω`, and **Thm 34.2**: on a closure pair's interval the partial closures are constant, so it is one class of closed saddle-functions, and it is the class of a unique closed convex bifunction |
| `Operations/Closed.lean` | the closedness half of **Thm 5.7** — `ClosedFn g → Continuous A → ClosedFn (compLin g A)` — resting on the inner-composition lemma for lower semicontinuity that Mathlib does not have |
| `Optimization/Perturbation.lean` | §29 — `Bifun`, `graphFn`, `ConvexBifun`, the perturbation function `infBifun`, the three consistency predicates, and **Thm 29.1**: `inf F` is convex with `dom (inf F) = dom F`, and `v ∈ KuhnTucker B F ↔ -v ∈ ∂(inf F)(0)` |
| `Optimization/Lagrangian.lean` | §§28–29 — `lagrangian`, and the identification that makes D8 work: `L(·, x)` **is** the concave conjugate of `-F(·)(x)`, so `⨅ x L(v, x) = ⨅ u {⟨u, v⟩ + inf F u}`, weak duality and concavity in the price variable are all conjugate facts |
| `Optimization/Adjoint.lean` | §30 — `adjointBifun` as the conjugate of the graph function at a reflected point, the concave adjoint, `clBifun`, all of **Thm 30.1** including `F** = cl F`, **Thm 30.2** (the dual objective is the *concave* conjugate of `-inf F`) and **Cor 30.2.2** (weak duality) |
| `Optimization/Fenchel.lean` | §31 — **Thm 31.1 (Fenchel's duality theorem)** in both of Rockafellar's forms, against `IsExactSum`; the conic case **Thm 31.4** with its optimality conditions; weak duality with no hypothesis; **Thm 31.3**, the Kuhn–Tucker conditions |
| `Optimization/ConeDuality.lean` | §31 — **Cor 31.4.3**, the duality between a finite co-finite `h` and `h*` over a closed convex cone, parametrised by `(z, z*)`; both infima finite and attained |
| `Optimization/Moreau.lean` | §31 — `quadFn B` (`w z = ½ B z z`), its self-conjugacy, and **Thm 31.5 (Moreau)** `(f □ w) + (f* □ w) = w` for any symmetric positive definite self-pairing `B`, with both envelopes finite and the Kuhn–Tucker characterisation of the splitting |
| `Optimization/Prox.lean` | §31 — `moreauObj B f z`, `prox B f z`, **Thm 31.5's** attainment and uniqueness (`z = prox (z | f) + prox (z | f*)`), **Cor 31.5.1** (`subgradientRelHomeomorph`) and **Cor 31.5.2** (`∂f` is maximal monotone) |
| `Optimization/MoreauGradient.lean` | §31 — **Thm 31.5**, the gradient formulas: `∂(f □ w) z` is the single point `prox (z | f*)`, so `∇(f □ w) z = z - prox (z | f)` and `∇(f* □ w) z = prox (z | f)` |
| `Optimization/Maximum.lean` | §32 in full — **Thm 32.1** (the maximum principle), Cor 32.1.1 (every maximiser lies in a face on which `f` is constant), **Thm 32.2** (`conv` raises neither the supremum of a convex function nor its maximiser set), **Thm 32.3** with Cors 32.3.1–32.3.4 (`BddAboveOnRays` for its half-line hypothesis; 32.3.3 quotients out the lineality space of `C`), and **Thm 32.4** with Cor 32.4.1 (a subgradient at a maximiser is normal to `C`) |
| `Optimization/Minimum.lean` | §27 — `argmin`, `inf f = -f*(0)`, `argmin f = ∂f*(0)`, existence and well-posedness under a recession hypothesis (**Thm 27.2**, Cors 27.2.1–27.2.2), minimisation over a closed convex set (**Thm 27.3**, non-polyhedral, and Cor 27.3.3), and **Thm 27.4** (`0 ∈ ∂h x + N_C(x)`), the most cited result of the book |

None of `RelativeInterior.lean`'s outstanding results blocks anything. `Duality/Compatible.lean`,
budgeted as a file in §3, is a page of corollaries over Mathlib's `WeakSpace.lean`.

## 8. Open questions

* Whether Rockafellar ever uses an `∞ − ∞` convention locally in §16/§30 (some treatments take
  `∞ − ∞ = ∞` there). `EReal` picks `⊥`. This decides whether D5's side conditions are cosmetic.
* ~~Whether `IsExactSum.of_continuousAt` is as cheap in a bare TVS as D5 assumes.~~ **Settled: yes.**
  `Duality/Continuity.lean` is ninety lines over `geometric_hahn_banach_open`, at layer B, with no
  local convexity and no `ri`.
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
  §23.8/23.9 are proved against `IsExactSum`/`IsExactImage`, `Duality/Relint.lean` supplies both by
  Rockafellar's own constraint qualification, and `Duality/Continuity.lean` supplies the sum
  interface again from continuity alone. `of_polyhedral`
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

* **§28 was never blocked by `Helly.lean`.** This plan and `06-optimization.md` both recorded that
  Slater's theorem (Theorem 28.2) waited on theorems of the alternative for *mixed*
  inequality/equality systems. `alternative_of_convex_system_affine` already has them: the affine
  constraints live in a **second index type**, which is exactly the mixed form, and an equality
  splits into two affine inequalities (`Sum.elim a fun k => -(a k)`) as Rockafellar himself does it.
  `Optimization/Program.lean` is the result, and it needs no `ineqBifun`: the theorem is about the
  constraint functions, not about a packaging of them.
* **Corollary 30.2.2's first formula needs no closedness of `F`.** Rockafellar states the corollary
  for closed convex bifunctions. `(cl (inf F))(0) = sup F* 0` is Fenchel–Moreau applied to `inf F`
  alone, so `ConvexBifun F` suffices, and consequently Theorem 30.3's equivalence (a) ⟺ (c) — no
  duality gap ⟺ normality — holds for every convex bifunction. `ClosedBifun F` is needed only where
  `F** = cl F` has to be turned back into `F`, i.e. the second formula and clause (b).
* **Theorem 30.4(c) is weak duality, not Theorem 23.5.** A Kuhn–Tucker vector is by definition a
  point where the dual objective attains `inf F 0`, and `sup F* 0 ≤ inf F 0` always; so the dual
  optimal value is `inf F 0` and Theorem 30.3 gives normality. The book's subgradient route would
  have cost finite-dimensionality that the statement does not need.
