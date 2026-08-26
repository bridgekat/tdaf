/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Support
import Tdaf.Analysis.Convex.Optimization.Maximum
import Tdaf.Analysis.Convex.Subgradient.Existence
import Tdaf.Surface.Common.Euclidean

/-!
# Rockafellar, §32: The Maximum of a Convex Function

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §32, pp. 342–348: maximising a convex
function, which behaves nothing like minimising one. The maximum principle (Theorem 32.1) says
that a relative interior maximiser forces constancy, so the maximum lives on the relative
boundary — on a face, and ultimately at an extreme point (Theorem 32.3 and its four corollaries).
Theorem 32.4 reads the same fact through subgradients: at a maximiser every subgradient is a
non-zero normal vector.

All eleven numbered results of the section are here — Theorems 32.1, 32.2, 32.3 and 32.4, and
Corollaries 32.1.1, 32.2.1, 32.3.1, 32.3.2, 32.3.3, 32.3.4 and 32.4.1 — together with both of the
section's examples and the six unnumbered remarks that carry mathematical content (13953,
13971, 13981, 14013, 14015 and 14061).

## Contents

| label | declaration |
|---|---|
| Theorem 32.1 (13927) | `theorem_32_1`, `theorem_32_1_const` |
| §32 remark, 13953 | `theorem_32_1_affineSubspace`, `theorem_32_1_affineSubspace_of_le` |
| Corollary 32.1.1 (13949) | `maximumSet`, `mem_maximumSet`, `corollary_32_1_1` |
| Theorem 32.2 (13957) | `theorem_32_2`, `theorem_32_2_attained` |
| Corollary 32.2.1 (13967) | `corollary_32_2_1`, `corollary_32_2_1_attained` |
| §32 remark, 13971 | `theorem_32_2_extremePoints_add_coneHull` |
| Theorem 32.3 (13973) | `NoUnboundedHalfLine`, `bddAboveOnRays_iff`, `theorem_32_3`,
  `theorem_32_3_attained`, `theorem_32_3_containsNoLine` |
| §32 remark, 13981 | `theorem_32_3_const_on_lineality` |
| Corollary 32.3.1 (13995) | `corollary_32_3_1` |
| Corollary 32.3.2 (13999) | `corollary_32_3_2`, `corollary_32_3_2_finite`,
  `corollary_32_3_2_iSup` |
| Corollary 32.3.3 (14005) | `corollary_32_3_3` |
| Corollary 32.3.4 (14009) | `corollary_32_3_4`, `corollary_32_3_4_finite` |
| §32 remark, 14013 | `linearSystem`, `polyhedral_linearSystem`, `corollary_32_3_4_affine`,
  `corollary_32_3_4_linearSystem` |
| §32 remark, 14015 | `corollary_32_3_2_not_attained_of_subset_dom`,
  `corollary_32_3_2_not_bddAbove_of_subset_dom` |
| §32 example, 14017–14035 | `parabolicSet`, `mem_parabolicSet`, `parabolicFn`,
  `parabolicFn_of_mem`, `parabolicFn_of_notMem`, `supportFn_parabolicSet`,
  `convexFn_parabolicFn`, `closedFn_parabolicFn`, `proper_parabolicFn`, `parabolicCap`,
  `zero_mem_parabolicCap`, `isClosed_parabolicCap`, `isBounded_parabolicCap`,
  `convex_parabolicCap`, `parabolicCap_subset_dom`, `parabolicFn_lt_one_of_mem_parabolicCap`,
  `parabolicFn_capPoint`, `parabolicCap_not_attained` |
| §32 example, 14037–14043 | `quarticCap`, `zero_mem_quarticCap`, `isClosed_quarticCap`,
  `isBounded_quarticCap`, `convex_quarticCap`, `quarticCap_subset_dom`,
  `quarticCap_not_bddAbove` |
| Theorem 32.4 (14047) | `theorem_32_4_proper`, `theorem_32_4_nonempty`, `theorem_32_4_normal`,
  `theorem_32_4_ne_zero` |
| Corollary 32.4.1 (14057) | `corollary_32_4_1` |
| §32 remark, 14061 | `normalCone_closedBall`, `theorem_32_4_ball` |

## The section's definitions

* `Rockafellar.maximumSet f C` — Rockafellar's `W`, "the set of points (if any) where the supremum
  of `f` relative to `C` is attained" (13949). Corollary 32.1.1 is then the literal set equation
  `W = ⋃₀ {C' | IsFace C C' ∧ C' ⊆ W}`, which is what "`W` is a union of faces of `C`" says.
* `Rockafellar.NoUnboundedHalfLine f C` — the book's standing hypothesis of Theorem 32.3, "there
  are no half-lines in `C` on which `f` is unbounded above" (13973), quantified over genuine
  half-lines (`v ≠ 0`). `bddAboveOnRays_iff` is the bridge to the backbone's `BddAboveOnRays`,
  which folds the book's *other* standing hypothesis `C ⊆ dom f` into the same predicate by
  allowing the degenerate direction `v = 0`; the two agree exactly when `C ⊆ dom f`, and that is
  how the bridge is stated. Every §32 statement here therefore carries Rockafellar's two
  hypotheses separately, as he writes them.
* `Rockafellar.linearSystem a α` — the solution set of a finite system of weak linear
  inequalities `⟨x, aᵢ⟩ ≤ αᵢ`, `i < m`. `polyhedral_linearSystem` is the bridge to `Polyhedral`;
  it exists so that `corollary_32_3_4_linearSystem` can be the book's own sentence at 14013,
  "the problem of maximizing an affine function over the set of solutions to a finite system of
  weak linear inequalities", rather than a restatement of it.
* `Rockafellar.parabolicSet`, `Rockafellar.parabolicFn`, `Rockafellar.parabolicCap`,
  `Rockafellar.quarticCap` — the section's two examples, transcribed as Lean definitions. See
  "The two examples" below.

## Where the book's hypotheses had to change

**Corollary 32.3.2's finiteness clause needs `f` proper, and the book does not say so.** "Then the
supremum of `f` relative to `C` is finite" (13999) is false for the improper convex function
`f ≡ −∞`: its domain is all of `ℝⁿ`, so `ri (dom f) = ℝⁿ` contains every compact convex `C`, and
the supremum is `−∞`. Rockafellar's own proof appeals to Theorem 10.1 for continuity relative to
`C` and then to compactness, and neither step rules the value out. `corollary_32_3_2_finite` and
`corollary_32_3_2` therefore carry `Proper f`. Nothing else in the section needs it: the
*attainment* clause is true for an improper `f` as well, since the supremum `−∞` is attained
everywhere, but it is not what the backbone's `exists_mem_extremePoints_isMaxOn_of_isCompact`
proves.

**Theorem 32.1 does not need `C` convex.** The book says "let `C` be a convex set contained in
`dom f`"; the proof uses only that a relative interior point of `C` can be prolonged past itself
inside `C`, which is true of any set. `theorem_32_1` is stated without the convexity hypothesis,
which is a strengthening, not a divergence — Corollary 32.1.1, which does need it (Theorem 18.2),
takes it.

**Corollary 32.3.3 is the book's statement, and the divergence recorded in the Part plan is in
Theorem 32.3 instead.** `part6.md` says "Cor 32.3.3 diverges from the book deliberately: the
backbone quotients the lineality space by an *arbitrary* complement rather than `L⊥`". The
backbone's `exists_isMaxOn_of_polyhedral_of_bddAboveOnRays` in fact concludes exactly what the
book concludes — bare attainment, `∃ z ∈ C, ∀ w ∈ C, f w ≤ f z` — and the arbitrary complement
never reaches the statement: it is chosen inside the proof by `Submodule.exists_isCompl`.
`corollary_32_3_3` here is therefore a one-line specialisation with no divergence at all. What
*does* diverge is **Theorem 32.3**, whose book form indexes the supremum by the extreme points of
`C ∩ L⊥`; `Maximum.lean`'s own `## What is not here` says so, and gives the reason — fixing `L⊥`
in the statement would force an inner product on a development that is otherwise free of one.
**The surface has the inner product, so it restores the book's form**: `theorem_32_3` and
`theorem_32_3_attained` are stated with `C ∩ (linealitySubmodule C)ᗮ`, exactly as printed at
13979. The backbone statement is still the more general one — it holds for any complement of the
lineality space, on any finite-dimensional normed space — and a reader checking alignment should
read the two together rather than treating either as the correction of the other.

**Corollary 32.4.1 does not go through Theorem 32.2.** Rockafellar passes to `C = conv S` so that
Theorem 32.4 can be applied to a convex set. The backbone's Theorem 32.4
(`mem_normalCone_of_mem_subgradient_of_isMaxOn`) asks nothing about `C`, so `corollary_32_4_1`
applies it to `S` directly and the convex hull never appears. The book's route is not wrong, only
longer.

**"`f` is finite but not constant on `C`" is spelled out.** Theorem 32.4's hypothesis becomes
`hfin : ∀ z ∈ C, f z ≠ ⊥ ∧ f z ≠ ⊤` together with a witness `z₀ ∈ C` with `f z₀ ≠ f x`; a set on
which `f` is not constant supplies such a witness at any of its points, and it is what the
non-vanishing clause actually consumes. Properness is *derived* rather than assumed, exactly as
the book derives it from Theorem 7.2 (`theorem_32_4_proper`).

## The two examples

Lines 14015–14043. Rockafellar's point is that `C ⊆ ri (dom f)` in Corollary 32.3.2 cannot be
weakened to `C ⊆ dom f`, *even for closed `f`*, and that both conclusions fail: the supremum may
fail to be attained, and it may fail to be finite. Both examples use the same function

```
f(ξ₁, ξ₂) = ξ₁²/ξ₂ − ξ₂ if ξ₂ > 0,   0 if ξ₁ = ξ₂ = 0,   +∞ otherwise
```

which is `parabolicFn`. Lean's `x / 0 = 0` makes the first line of the formula compute the second
one as well, so the definition is a single `⨅ _ : p, …` over the domain predicate
`0 ≤ ξ₂ ∧ (ξ₂ = 0 → ξ₁ = 0)`.

**`f` is convex, closed and proper because it is a support function**, which is the verification
the book suggests in its own parenthesis at 14023: `supportFn_parabolicSet` proves
`δ*(· | K) = f` for `K = {(ξ₁, ξ₂) | ξ₁² + 4ξ₂ + 4 ≤ 0}`, and `convexFn_supportFn`,
`closedFn_supportFn` and `proper_supportFn` then cost one line each. Computing the support
function is four cases: the parabola's tangent point `(2ξ₁/ξ₂, −ξ₁²/ξ₂² − 1)` attains the
supremum when `ξ₂ > 0`, the origin gives `0`, and the two remaining cases are unbounded along the
parabola and along the downward vertical respectively.

* **The first example** takes `C = parabolicCap = {(ξ₁, ξ₂) | ξ₁² ≤ ξ₂ ≤ 1}`: non-empty, closed,
  bounded, convex, inside `dom f`, with `f < 1` throughout
  (`parabolicFn_lt_one_of_mem_parabolicCap`) and `f (t, t²) = 1 − t²` on the boundary parabola
  (`parabolicFn_capPoint`). So the supremum is
  `1` and is not attained: `parabolicCap_not_attained`.
* **The second example** replaces `C` by `D = quarticCap = {(ξ₁, ξ₂) | ξ₁⁴ ≤ ξ₂ ≤ 1}`, where
  `f (t, t⁴) = t⁻² − t⁴ → +∞`: `quarticCap_not_bddAbove`.

Both are then used to refute, in Lean, the weakened corollary itself — the alignment checklist's
*stated and refuted* category. `corollary_32_3_2_not_attained_of_subset_dom` and
`corollary_32_3_2_not_bddAbove_of_subset_dom` state Corollary 32.3.2 with `C ⊆ ri (dom f)`
replaced by `C ⊆ dom f`, with `ClosedFn` and `Proper` added to make the refutation as strong as
the book's remark, and prove the negation.

The convexity of the two caps is the only shared computation, and it is `convex_cap` fed with the
convexity inequality for `t ↦ t²` (`sq_combo_le`) and for `t ↦ t⁴` (`quartic_combo_le`, which is
`sq_combo_le` squared).

## What is not here

**The opening illustration (13921–13923)** — maximising `|x − a|` over a triangle in `ℝ²`, whose
maximum can only be at a vertex while local maxima occur at all three — is *omitted with a
reason*: it is a remark about the difference between local and global maxima, and the content it
illustrates is Corollary 32.3.2, which is here. Nothing in the section depends on it.

**No local-maximum theory.** The section's opening paragraph observes that local maxima are
plentiful and that no local criterion distinguishes the global one. Rockafellar states no theorem
about this and the surface states none either.

## Backbone gaps

None of these blocks a numbered result; each cost a `private` lemma here.

**Theorem 32.3 in a form the surface can specialise.** `Maximum.lean` proves the two ends of
Theorem 32.3 — the `ContainsNoLine` case and Corollary 32.3.3 — but not the statement in between,
so restoring the book's `C ∩ L⊥` form meant re-running the lineality-space decomposition here
(`exists_mem_inter_eq_of_isCompl`, `containsNoLine_inter_of_isCompl`,
`iSup_extremePoints_inter_of_isCompl`, about forty lines, all copied from the proof of
`exists_isMaxOn_of_polyhedral_of_bddAboveOnRays`). What is wanted, in
`Tdaf/Analysis/Convex/Optimization/Maximum.lean`:

```lean
theorem ConvexFn.iSup_extremePoints_inter_of_isCompl (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hray : BddAboveOnRays f C) {N : Submodule ℝ E}
    (hN : IsCompl (linealitySubmodule C) N) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ (C ∩ (N : Set E)).extremePoints ℝ, f x

theorem exists_mem_extremePoints_inter_eq_of_isMaxOn_of_isCompl (hf : ConvexFn f)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hray : BddAboveOnRays f C) {N : Submodule ℝ E}
    (hN : IsCompl (linealitySubmodule C) N) {x : E} (hx : x ∈ C) (hmax : ∀ w ∈ C, f w ≤ f x) :
    ∃ z ∈ (C ∩ (N : Set E)).extremePoints ℝ, f z = f x
```

with `exists_isMaxOn_of_polyhedral_of_bddAboveOnRays` re-derived from the second. These are
strictly more general than the book's `L⊥` statement, need no inner product, and would make
`theorem_32_3` and `theorem_32_3_attained` one-line specialisations.

**`ConvexFn.iSup_extremePoints_of_containsNoLine` asks for a uniform bound where its proof needs
only `BddAboveOnRays`.** `ConvexFn.exists_mem_convexHull_extremePoints_le`, which is the whole
proof, was already generalised to `BddAboveOnRays`; the supremum statement above it was not, so
it cannot be used for Theorem 32.3 as the book states it (where `f` may well be unbounded on
`C` — take `C = {(ξ₁, ξ₂) | ξ₁² ≤ ξ₂}` and `f (ξ₁, ξ₂) = ξ₁`, whose only half-lines are vertical).
What is wanted, in the same module and replacing the present statement:

```lean
theorem ConvexFn.iSup_extremePoints_of_containsNoLine (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) (hray : BddAboveOnRays f C) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x
```

The proof does not change; only `bddAboveOnRays_of_forall_le hbdd` disappears from it.
`iSup_extremePoints_of_bddAboveOnRays` here is that statement, `private`.

**A finitely generated set has finitely many extreme points, and nobody says so.**
`Maximum.lean` derives it inline inside
`exists_mem_extremePoints_isMaxOn_of_finitelyGenerated_of_bddAboveOnRays`, and
`corollary_32_3_4_finite` derives it again, both from `extremePoints_convexHullPD_subset`.
What is wanted, in `Tdaf/Analysis/Convex/Representation.lean` beside that lemma:

```lean
theorem FinitelyGenerated.finite_extremePoints (hC : FinitelyGenerated C) :
    (C.extremePoints ℝ).Finite
```

**The normal cone to the Euclidean unit ball.** `normalCone_closedBall` — the vectors normal to
the unit ball at a boundary point `x` are the `λx`, `λ ≥ 0` — is the whole content of the remark
at 14061 and is not in the backbone. It belongs in
`Tdaf/Analysis/Convex/Subgradient/Defs.lean` or beside the inner-product bridges in
`Tdaf/Analysis/Convex/Subgradient/Rademacher.lean`, stated for an arbitrary real inner-product
space:

```lean
theorem normalCone_innerₗ_closedBall {x : E} (hx : ‖x‖ = 1) :
    normalCone (innerₗ E) (Metric.closedBall 0 1) x = {y | ∃ lam : ℝ, 0 ≤ lam ∧ y = lam • x}
```

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §32, pp. 342–348
  (book lines 13917–14068).
-/

open scoped Pointwise

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

variable {n : ℕ} {f : Rn n → EReal} {C : Set (Rn n)}

/-! ### Theorem 32.1: the maximum principle -/

/-- **Rockafellar, Theorem 32.1** (13927), the maximum principle: if a convex function attains
its supremum relative to a set `C ⊆ dom f` at a point of `ri C`, it takes the same value
everywhere on `C`.

Rockafellar assumes `C` convex; the proof does not use it, and neither does the backbone's
`ConvexFn.eq_of_isMaxOn_mem_relint`. All that is needed is that a relative interior point can be
prolonged past itself inside `C` (Theorem 6.4), which exhibits `z` as a proper convex combination
of `x` and a further point of `C`; if `f x` were below `f z`, convexity would put `f z` below
itself. -/
theorem theorem_32_1 (hf : ConvexFn f) (hCdom : C ⊆ dom f) {z : Rn n} (hz : z ∈ ri C)
    (hmax : ∀ w ∈ C, f w ≤ f z) {x : Rn n} (hx : x ∈ C) : f x = f z :=
  hf.eq_of_isMaxOn_mem_relint hCdom hz hmax hx

/-- **Rockafellar, Theorem 32.1** (13927): "`f` is actually constant throughout `C`", stated as
constancy rather than as "every value equals the maximum". -/
theorem theorem_32_1_const (hf : ConvexFn f) (hCdom : C ⊆ dom f) {z : Rn n} (hz : z ∈ ri C)
    (hmax : ∀ w ∈ C, f w ≤ f z) {x y : Rn n} (hx : x ∈ C) (hy : y ∈ C) : f x = f y := by
  rw [theorem_32_1 hf hCdom hz hmax hx, theorem_32_1 hf hCdom hz hmax hy]

/-- **Rockafellar, §32 (13953)**, first sentence: a convex function attaining its supremum
relative to an affine set `M ⊆ dom f` is constant on `M`.

This is Theorem 32.1 at `C = M`, where `ri M = M` (`AffineSubspace.intrinsicInterior_coe`) so the
relative interior hypothesis is free. -/
theorem theorem_32_1_affineSubspace (hf : ConvexFn f) {M : AffineSubspace ℝ (Rn n)}
    (hMdom : (M : Set (Rn n)) ⊆ dom f) {z : Rn n} (hz : z ∈ M)
    (hmax : ∀ w ∈ (M : Set (Rn n)), f w ≤ f z) {x : Rn n} (hx : x ∈ M) : f x = f z :=
  theorem_32_1 hf hMdom (by rw [AffineSubspace.intrinsicInterior_coe]; exact hz) hmax hx

/-- **Rockafellar, §32 (13953)**, second sentence, which is **Corollary 8.6.2**: the
conclusion holds as soon as the supremum over `M` is finite, attained or not. -/
theorem theorem_32_1_affineSubspace_of_le (hf : ConvexFn f) {M : AffineSubspace ℝ (Rn n)}
    {α : ℝ} (hM : ∀ w ∈ M, f w ≤ (α : EReal)) {x z : Rn n} (hx : x ∈ M) (hz : z ∈ M) :
    f z = f x :=
  hf.eq_of_le_on_affineSubspace hM hx hz

/-- **Rockafellar, Corollary 32.1.1** (13949): Rockafellar's `W`, the set of points at which
the supremum of `f` relative to `C` is attained. -/
def maximumSet (f : Rn n → EReal) (C : Set (Rn n)) : Set (Rn n) :=
  {x | x ∈ C ∧ ∀ w ∈ C, f w ≤ f x}

theorem mem_maximumSet {x : Rn n} :
    x ∈ maximumSet f C ↔ x ∈ C ∧ ∀ w ∈ C, f w ≤ f x := Iff.rfl

/-- **Rockafellar, Corollary 32.1.1** (13949): `W` is a union of faces of `C`, stated as the set
equation it is.

The inclusion `⊇` is free. For `⊆`, Theorem 18.2 (`exists_isFace_mem_relint`) produces the unique
face `C'` having a given maximiser in its relative interior, and Theorem 32.1 applied to `C'`
makes `f` constant on it — so `C'` consists of maximisers too, and is a face lying inside `W`
through the given point. -/
theorem corollary_32_1_1 (hf : ConvexFn f) (hC : Convex ℝ C) (hCdom : C ⊆ dom f) :
    maximumSet f C = ⋃₀ {C' | IsFace C C' ∧ C' ⊆ maximumSet f C} := by
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.sUnion_subset fun C' hC' => hC'.2)
  obtain ⟨C', hface, hxC', hconst⟩ :=
    exists_isFace_forall_eq_of_isMaxOn hf hC hCdom hx.1 hx.2
  refine ⟨C', ⟨hface, fun y hy => ⟨hface.toIsExtreme.1 hy, fun w hw => ?_⟩⟩, hxC'⟩
  rw [hconst y hy]
  exact hx.2 w hw

/-! ### Theorem 32.2: passing to the convex hull -/

/-- **Rockafellar, Theorem 32.2** (13957): the convex hull does not raise the supremum of a
convex function, `sup_{conv S} f = sup_S f`.

The sublevel set `{x | f x ≤ sup_S f}` is convex and contains `S`, so it contains `conv S`. This
is `convexHull_min`, not a Carathéodory decomposition, and it needs neither a topology nor a
dimension bound. -/
theorem theorem_32_2 (hf : ConvexFn f) (S : Set (Rn n)) :
    (⨆ x ∈ convexHull ℝ S, f x) = ⨆ x ∈ S, f x :=
  hf.iSup_convexHull S

/-- **Rockafellar, Theorem 32.2** (13957): "the first supremum is attained only when the second
(more restrictive) supremum is attained". The *strict* sublevel set does the same job: a convex
function staying strictly below its maximum throughout `S` stays below it throughout
`conv S`. -/
theorem theorem_32_2_attained (hf : ConvexFn f) {S : Set (Rn n)} {x : Rn n}
    (hx : x ∈ convexHull ℝ S) (hmax : ∀ z ∈ convexHull ℝ S, f z ≤ f x) :
    ∃ z ∈ S, f z = f x :=
  exists_eq_of_isMaxOn_convexHull hf hx hmax

/-- **Rockafellar, Corollary 32.2.1** (13967): for a closed convex `C` that is not an affine set
or half of one, the supremum over `C` is already the supremum over the relative boundary.

Rockafellar's two exceptional cases are one predicate in the backbone, `IsAffineHalf` — the
degenerate functional `φ = 0` gives the affine sets — and the exclusion cannot be dropped: over
`[0, ∞)` the relative boundary is `{0}` while `f x = x` has supremum `⊤`. The proof is
Theorem 18.4 in hull form (`convexHull ℝ (C \ ri C) = C`) fed to Theorem 32.2. -/
theorem corollary_32_2_1 (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) : (⨆ x ∈ C, f x) = ⨆ x ∈ C \ ri C, f x :=
  hf.iSup_sdiff_relint hC hCcl hhalf

/-- **Rockafellar, Corollary 32.2.1** (13967): "the former is attained only when the latter is
attained" — Theorem 32.2's attainment clause read through Theorem 18.4. -/
theorem corollary_32_2_1_attained (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) {x : Rn n} (hx : x ∈ C) (hmax : ∀ z ∈ C, f z ≤ f x) :
    ∃ z ∈ C \ ri C, f z = f x :=
  exists_notMem_relint_eq_of_isMaxOn hf hC hCcl hhalf hx hmax

/-! ### Theorem 32.3: the extreme point principle -/

/-- **Rockafellar, Theorem 32.3** (13973), the standing hypothesis "there are no half-lines in
`C` on which `f` is unbounded above", read over genuine half-lines (`v ≠ 0`). -/
def NoUnboundedHalfLine (f : Rn n → EReal) (C : Set (Rn n)) : Prop :=
  ∀ u v : Rn n, v ≠ 0 → (∀ t : ℝ, 0 ≤ t → u + t • v ∈ C) →
    ∃ β : ℝ, ∀ t : ℝ, 0 ≤ t → f (u + t • v) ≤ (β : EReal)

/-- **The bridge to the backbone's `BddAboveOnRays`.** The backbone folds Rockafellar's two
standing hypotheses of Theorem 32.3 into one predicate by letting the direction `v` be `0`, so
that the degenerate "half-line" `{u}` carries the condition `f u < ⊤`; under `C ⊆ dom f` the
degenerate case is automatic and the two predicates agree. Every numbered statement below takes
`C ⊆ dom f` and `NoUnboundedHalfLine f C` separately, as the book writes them, paying this
bridge once. -/
theorem bddAboveOnRays_iff (hCdom : C ⊆ dom f) :
    BddAboveOnRays f C ↔ NoUnboundedHalfLine f C := by
  constructor
  · exact fun h u v _ hray => h u v hray
  · intro h u v hray
    rcases eq_or_ne v 0 with rfl | hv
    · have hu : u ∈ C := by simpa using hray 0 le_rfl
      obtain ⟨β, hβ, -⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 (mem_dom.1 (hCdom hu))
      exact ⟨β, fun t _ => by simpa using hβ.le⟩
    · exact h u v hv hray

private theorem iSup_extremePoints_of_bddAboveOnRays (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) (hray : BddAboveOnRays f C) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x := by
  refine le_antisymm (iSup₂_le fun x hx => ?_)
    (iSup₂_le fun x hx => le_iSup₂ (f := fun z (_ : z ∈ C) => f z) x (extremePoints_subset hx))
  obtain ⟨u, hu, hle⟩ := hf.exists_mem_convexHull_extremePoints_le hC hCcl hnl hray hx
  refine hle.trans ?_
  rw [← hf.iSup_convexHull (C.extremePoints ℝ)]
  exact le_iSup₂ (f := fun z (_ : z ∈ convexHull ℝ (C.extremePoints ℝ)) => f z) u hu

private theorem exists_mem_inter_eq_of_isCompl (hf : ConvexFn f) (hray : BddAboveOnRays f C)
    {N : Submodule ℝ (Rn n)} (hN : IsCompl (linealitySubmodule C) N) {w : Rn n} (hw : w ∈ C) :
    ∃ q ∈ C ∩ (N : Set (Rn n)), f w = f q := by
  have hdec : C = (linealitySubmodule C : Set (Rn n)) + (C ∩ (N : Set (Rn n))) :=
    eq_add_inter_of_isCompl hN
  obtain ⟨p, hp, q, hq, rfl⟩ :=
    (hdec ▸ hw : w ∈ (linealitySubmodule C : Set (Rn n)) + (C ∩ (N : Set (Rn n))))
  refine ⟨q, hq, ?_⟩
  change f (p + q) = f q
  rw [show p + q = q + p by abel]
  exact hf.add_eq_of_mem_linealitySpace hray hq.1 (by simpa using hp)

private theorem containsNoLine_inter_of_isCompl (hCconv : Convex ℝ C) (hCcl : IsClosed C)
    {N : Submodule ℝ (Rn n)} (hN : IsCompl (linealitySubmodule C) N) :
    ContainsNoLine (C ∩ (N : Set (Rn n))) := by
  intro a y hy0
  by_contra hcon
  push Not at hcon
  have hyC : y ∈ recessionCone C :=
    mem_recessionCone_of_exists_ray hCconv hCcl ⟨a, fun t _ => (hcon t).1⟩
  have hyC' : -y ∈ recessionCone C := by
    refine mem_recessionCone_of_exists_ray hCconv hCcl ⟨a, fun t _ => ?_⟩
    rw [show a + t • (-y) = a + (-t) • y by module]
    exact (hcon (-t)).1
  have hyL : y ∈ linealitySubmodule C :=
    mem_linealitySubmodule.2 (mem_linealitySpace.2 ⟨hyC, hyC'⟩)
  have hyN : y ∈ N := by
    have hdiff := N.sub_mem (hcon 1).2 (hcon 0).2
    rwa [show a + (1 : ℝ) • y - (a + (0 : ℝ) • y) = y by module] at hdiff
  exact hy0 (by simpa using hN.disjoint.le_bot ⟨hyL, hyN⟩)

private theorem inter_facts {N : Submodule ℝ (Rn n)} (hC : Convex ℝ C) (hCcl : IsClosed C) :
    Convex ℝ (C ∩ (N : Set (Rn n))) ∧ IsClosed (C ∩ (N : Set (Rn n))) :=
  ⟨hC.inter (Submodule.convex N), hCcl.inter (Submodule.closed_of_finiteDimensional N)⟩

/-- **Rockafellar, Theorem 32.3** (13973), for an arbitrary complement `N` of the lineality
space. -/
private theorem iSup_extremePoints_inter_of_isCompl (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hray : BddAboveOnRays f C) {N : Submodule ℝ (Rn n)}
    (hN : IsCompl (linealitySubmodule C) N) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ (C ∩ (N : Set (Rn n))).extremePoints ℝ, f x := by
  obtain ⟨hDconv, hDcl⟩ := inter_facts (N := N) hC hCcl
  have hDnl := containsNoLine_inter_of_isCompl hC hCcl hN
  rw [← iSup_extremePoints_of_bddAboveOnRays hf hDconv hDcl hDnl
    (hray.mono Set.inter_subset_left)]
  refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun x hx =>
    le_iSup₂ (f := fun z (_ : z ∈ C) => f z) x (Set.inter_subset_left hx))
  obtain ⟨q, hq, hfq⟩ := exists_mem_inter_eq_of_isCompl hf hray hN hx
  rw [hfq]
  exact le_iSup₂ (f := fun z (_ : z ∈ C ∩ (N : Set (Rn n))) => f z) q hq

/-- **Rockafellar, Theorem 32.3** (13973), in the book's own form: `sup_C f = sup_E f`, where
`E` is the set of extreme points of `C ∩ L⊥` and `L` is the lineality space of `C` (13979).

`Maximum.lean` declines to state this form, because fixing `L⊥` needs an inner product it does
not want to assume, and proves the two ends instead — `ContainsNoLine` (`L = 0`) and Corollary
32.3.3. Here the inner product is available, so `L⊥` can be named: the whole content is the
decomposition `C = L + (C ∩ L⊥)` (`eq_add_inter_of_isCompl` at the complement
`Submodule.isCompl_orthogonal`), along which `f` is constant, plus Theorem 32.3 applied to
`C ∩ L⊥`, which contains no lines. See the module docstring, `## Backbone gaps`. -/
theorem theorem_32_3 (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCdom : C ⊆ dom f) (hray : NoUnboundedHalfLine f C) :
    (⨆ x ∈ C, f x)
      = ⨆ x ∈ (C ∩ ((linealitySubmodule C)ᗮ : Set (Rn n))).extremePoints ℝ, f x :=
  iSup_extremePoints_inter_of_isCompl hf hC hCcl ((bddAboveOnRays_iff hCdom).2 hray)
    (Submodule.isCompl_orthogonal _)

/-- **Rockafellar, Theorem 32.3** (13973): "the supremum relative to `C` is attained only when
the supremum relative to `E` is attained" (13979).

The maximiser is transported to `C ∩ L⊥` along the lineality space, where Corollary 32.3.1
applies. Rockafellar's `C ⊆ dom f` is what supplies `f x ≠ ⊤` there. -/
theorem theorem_32_3_attained (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCdom : C ⊆ dom f) (hray : NoUnboundedHalfLine f C) {x : Rn n} (hx : x ∈ C)
    (hmax : ∀ w ∈ C, f w ≤ f x) :
    ∃ z ∈ (C ∩ ((linealitySubmodule C)ᗮ : Set (Rn n))).extremePoints ℝ, f z = f x := by
  have hray' : BddAboveOnRays f C := (bddAboveOnRays_iff hCdom).2 hray
  have hN : IsCompl (linealitySubmodule C) (linealitySubmodule C)ᗮ :=
    Submodule.isCompl_orthogonal _
  obtain ⟨hDconv, hDcl⟩ := inter_facts (N := (linealitySubmodule C)ᗮ) hC hCcl
  have hDnl := containsNoLine_inter_of_isCompl hC hCcl hN
  obtain ⟨q, hq, hfq⟩ := exists_mem_inter_eq_of_isCompl hf hray' hN hx
  have hqmax : ∀ w ∈ C ∩ ((linealitySubmodule C)ᗮ : Set (Rn n)), f w ≤ f q := by
    intro w hw
    rw [← hfq]
    exact hmax w hw.1
  obtain ⟨z, hz, hzq⟩ := exists_mem_extremePoints_eq_of_isMaxOn_of_containsNoLine hf hDconv
    hDcl hDnl hq (by rw [← hfq]; exact (mem_dom.1 (hCdom hx)).ne) hqmax
  exact ⟨z, hz, by rw [hzq, ← hfq]⟩

/-- **Rockafellar, Corollary 32.3.1** (13995): if the supremum of a convex function over a
closed convex set containing no lines is attained at all, it is attained at an extreme point.

No boundedness hypothesis is needed — a finite maximum is itself a bound — but `f x ≠ ⊤` is, and
that is exactly what Rockafellar's standing `C ⊆ dom f` supplies. -/
theorem corollary_32_3_1 (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCdom : C ⊆ dom f) (hnl : ContainsNoLine C) {x : Rn n} (hx : x ∈ C)
    (hmax : ∀ z ∈ C, f z ≤ f x) : ∃ z ∈ C.extremePoints ℝ, f z = f x :=
  exists_mem_extremePoints_eq_of_isMaxOn_of_containsNoLine hf hC hCcl hnl hx
    (mem_dom.1 (hCdom hx)).ne hmax

/-- **Rockafellar, Corollary 32.3.2** (13999): a convex function attains its supremum relative to
a non-empty closed bounded convex `C ⊆ ri (dom f)` at an extreme point of `C`.

`C ⊆ ri (dom f)` makes `f` continuous relative to `C` (Theorem 10.1), closed and bounded makes
`C` compact (Heine–Borel), and Corollary 32.3.1 then moves the maximiser to an extreme point.
`Proper f` is not in the book's statement; see `## Where the book's hypotheses had to change`. -/
theorem corollary_32_3_2 (hf : ConvexFn f) (hp : Proper f) (hne : C.Nonempty)
    (hCcl : IsClosed C) (hCbdd : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    (hCri : C ⊆ ri (dom f)) : ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z :=
  exists_mem_extremePoints_isMaxOn_of_isCompact hf hp
    (Metric.isCompact_of_isClosed_isBounded hCcl hCbdd) hCconv hne hCri

/-- **Rockafellar, Corollary 32.3.2** (13999): "the supremum of `f` relative to `C` is finite".

This is the clause that needs `Proper f`: for `f ≡ −∞` the hypotheses hold and the supremum is
`⊥`. Given properness the supremum is the value at the maximiser, which is a real because the
maximiser lies in `dom f` and `f` never takes `−∞`. -/
theorem corollary_32_3_2_finite (hf : ConvexFn f) (hp : Proper f) (hne : C.Nonempty)
    (hCcl : IsClosed C) (hCbdd : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    (hCri : C ⊆ ri (dom f)) : ∃ r : ℝ, (⨆ x ∈ C, f x) = (r : EReal) := by
  obtain ⟨z, hz, hzmax⟩ := corollary_32_3_2 hf hp hne hCcl hCbdd hCconv hCri
  have hzC : z ∈ C := extremePoints_subset hz
  obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot z)
    (mem_dom.1 (intrinsicInterior_subset (hCri hzC)))
  refine ⟨r, le_antisymm (iSup₂_le fun w hw => hr ▸ hzmax w hw) ?_⟩
  rw [← hr]
  exact le_iSup₂ (f := fun w (_ : w ∈ C) => f w) z hzC

/-- **Rockafellar, Corollary 32.3.3** (14005): on a non-empty polyhedral `C ⊆ dom f` with no
half-line on which `f` is unbounded above, the supremum of `f` relative to `C` is attained.

Nothing is claimed about extreme points, and nothing is assumed about lines in `C` — a set
containing a line has no extreme points at all. The backbone quotients the lineality space out by
an arbitrary complement chosen inside the proof, so the maximiser it returns is an extreme point
of `C ∩ N` rather than of `C`; the *statement* is the book's, verbatim. -/
theorem corollary_32_3_3 (hf : ConvexFn f) (hC : Polyhedral C) (hne : C.Nonempty)
    (hCdom : C ⊆ dom f) (hray : NoUnboundedHalfLine f C) : ∃ z ∈ C, ∀ w ∈ C, f w ≤ f z :=
  exists_isMaxOn_of_polyhedral_of_bddAboveOnRays hf hC hne ((bddAboveOnRays_iff hCdom).2 hray)

/-- **Rockafellar, Corollary 32.3.4** (14009): a convex function bounded above on a non-empty
polyhedral convex set containing no lines attains its supremum at one of the extreme points.

This combines Corollaries 32.3.1 and 32.3.3, and is **the theoretical basis of the simplex
method**: Rockafellar's remark at 14013 is that it "applies in particular to the problem of
maximizing an affine function over the set of solutions to a finite system of weak linear
inequalities. This is a fact of fundamental importance in the computational theory for linear
programs." That specialisation is `corollary_32_3_4_linearSystem`.

The uniform real bound `hbdd` carries Rockafellar's standing `C ⊆ dom f` with it. "Polyhedral" is
read through Theorem 19.1 into its finitely generated form, which is what makes the extreme point
set finite (`corollary_32_3_4_finite`). -/
theorem corollary_32_3_4 (hf : ConvexFn f) (hC : Polyhedral C) (hne : C.Nonempty)
    (hnl : ContainsNoLine C) {β : ℝ} (hbdd : ∀ x ∈ C, f x ≤ (β : EReal)) :
    ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z :=
  exists_mem_extremePoints_isMaxOn_of_finitelyGenerated hf hC.finitelyGenerated hnl hne hbdd

/-- **Rockafellar, Corollary 32.3.4** (14009): the parenthetical "(finitely many)". A polyhedral
set is finitely generated (Theorem 19.1) and the extreme points of `conv P + cone D` lie in `P`
(Corollary 18.3.1). -/
theorem corollary_32_3_4_finite (hC : Polyhedral C) : (C.extremePoints ℝ).Finite := by
  obtain ⟨P, D, hCeq⟩ := hC.finitelyGenerated
  exact P.finite_toSet.subset (by rw [hCeq]; exact extremePoints_convexHullPD_subset _ _)

/-- **Rockafellar, §32 (13971)**: "Theorem 32.2 can be applied to a given closed convex set `C`
by representing `C` as the convex hull of its extreme points and extreme directions as in §18."

Unlike Theorem 32.3 this needs no boundedness: keeping the extreme *directions* in the index set
is what makes the identity unconditional, and boundedness above is precisely what collapses the
second summand and leaves `theorem_32_3_containsNoLine`. -/
theorem theorem_32_2_extremePoints_add_coneHull (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) :
    (⨆ x ∈ C, f x)
      = ⨆ x ∈ C.extremePoints ℝ + (PointedCone.hull ℝ (extremeDirections C) : Set (Rn n)), f x :=
  hf.iSup_extremePoints_add_coneHull hC hCcl hnl

/-- **Rockafellar, §32 (13981)**: the step of Theorem 32.3's proof that cites Corollary 8.6.2 —
`f` is constant along every line in `C`. -/
theorem theorem_32_3_const_on_lineality (hf : ConvexFn f) (hCdom : C ⊆ dom f)
    (hray : NoUnboundedHalfLine f C) {u v : Rn n} (hu : u ∈ C) (hv : v ∈ linealitySpace C) :
    f (u + v) = f u :=
  hf.add_eq_of_mem_linealitySpace ((bddAboveOnRays_iff hCdom).2 hray) hu hv

/-- **Rockafellar, Theorem 32.3** (13973) when `C` contains no lines: then `L = 0` and
`C ∩ L⊥ = C`, so the supremum over `C` is the supremum over the extreme points of `C` itself. This
is the form Corollary 32.3.1 is read off. -/
theorem theorem_32_3_containsNoLine (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCdom : C ⊆ dom f) (hray : NoUnboundedHalfLine f C) (hnl : ContainsNoLine C) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x :=
  iSup_extremePoints_of_bddAboveOnRays hf hC hCcl hnl ((bddAboveOnRays_iff hCdom).2 hray)

/-- **Rockafellar, Corollary 32.3.2** (13999), supremum form: over a compact convex set the
supremum of a convex function is already the supremum over the extreme points. This is
Minkowski's theorem (Corollary 18.5.1) fed to Theorem 32.2, and it needs neither `C ⊆ ri (dom f)`
nor properness — only the *attainment* clause does. -/
theorem corollary_32_3_2_iSup (hf : ConvexFn f) (hCcl : IsClosed C)
    (hCbdd : Bornology.IsBounded C) (hCconv : Convex ℝ C) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x :=
  hf.iSup_extremePoints (Metric.isCompact_of_isClosed_isBounded hCcl hCbdd) hCconv

/-- **Rockafellar, §32 (14013).** The solution set of a finite system of weak linear
inequalities `⟨x, aᵢ⟩ ≤ αᵢ`, `i < m` — the feasible region of a linear program. -/
def linearSystem {m : ℕ} (a : Fin m → Rn n) (α : Fin m → ℝ) : Set (Rn n) :=
  {x : Rn n | ∀ i, pairing n x (a i) ≤ α i}

/-- A finite system of weak linear inequalities has a polyhedral solution set — this is the
definition of `Polyhedral`, transcribed at the book's index type. -/
theorem polyhedral_linearSystem {m : ℕ} (a : Fin m → Rn n) (α : Fin m → ℝ) :
    Polyhedral (linearSystem a α) := by
  classical
  refine ⟨Finset.image (fun i => (((pairing n).flip (a i) : Rn n →ₗ[ℝ] ℝ), α i)) Finset.univ, ?_⟩
  ext x
  constructor
  · intro hx q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
    exact hx i
  · intro hx i
    exact hx _ (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩)

/-- **Rockafellar, §32 (14013)**: Corollary 32.3.4 for an affine objective `⟨x, b⟩ − γ`. An
affine function is convex (`convexFn_affineFn`) and real-valued, so both of Rockafellar's
standing hypotheses reduce to the boundedness assumption. -/
theorem corollary_32_3_4_affine (b : Rn n) (γ : ℝ) (hC : Polyhedral C) (hne : C.Nonempty)
    (hnl : ContainsNoLine C) {β : ℝ} (hbdd : ∀ x ∈ C, pairing n x b - γ ≤ β) :
    ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, pairing n w b - γ ≤ pairing n z b - γ := by
  obtain ⟨z, hz, hzmax⟩ := corollary_32_3_4 (convexFn_affineFn b γ) hC hne hnl (β := β)
    fun x hx => by rw [affineFn_eq_coe]; exact_mod_cast hbdd x hx
  refine ⟨z, hz, fun w hw => ?_⟩
  have hle := hzmax w hw
  rw [affineFn_eq_coe, affineFn_eq_coe, _root_.EReal.coe_le_coe_iff] at hle
  exact hle

/-- **Rockafellar, §32 (14013)**: maximising an affine function over the solutions of a finite
system of weak linear inequalities — the theoretical basis of the simplex method. -/
theorem corollary_32_3_4_linearSystem {m : ℕ} (a : Fin m → Rn n) (α : Fin m → ℝ) (b : Rn n)
    (γ : ℝ) (hne : (linearSystem a α).Nonempty) (hnl : ContainsNoLine (linearSystem a α))
    {β : ℝ} (hbdd : ∀ x ∈ linearSystem a α, pairing n x b - γ ≤ β) :
    ∃ z ∈ (linearSystem a α).extremePoints ℝ,
      ∀ w ∈ linearSystem a α, pairing n w b - γ ≤ pairing n z b - γ :=
  corollary_32_3_4_affine b γ (polyhedral_linearSystem a α) hne hnl hbdd

/-! ### Theorem 32.4: subgradients at a maximiser -/

/-- **Rockafellar, Theorem 32.4** (14047): "here `f` must be proper by Theorem 7.2, since `f` is
assumed to be finite at a point of `ri (dom f)`." Properness is a *consequence* of the theorem's
hypotheses, not one of them, and this is the step that produces it. -/
theorem theorem_32_4_proper (hf : ConvexFn f) {x : Rn n} (hxri : x ∈ ri (dom f))
    (hxb : f x ≠ ⊥) : Proper f := by
  by_contra himp
  exact hxb (hf.eq_bot_of_mem_relint_dom himp hxri)

/-- **Rockafellar, Theorem 32.4** (14047): "the set `∂f(x)` is non-empty, because
`x ∈ ri (dom f)` (Theorem 23.4)" — which is what makes the theorem's conclusion about *every*
subgradient a statement with content. -/
theorem theorem_32_4_nonempty (hf : ConvexFn f) {x : Rn n} (hxri : x ∈ ri (dom f))
    (hxb : f x ≠ ⊥) : (subgradient (pairing n) f x).Nonempty :=
  subgradient_nonempty_of_mem_relint_dom hf (theorem_32_4_proper hf hxri hxb) hxri

/-- **Rockafellar, Theorem 32.4** (14047): at a point where `f` attains its supremum relative to
`C`, every `x* ∈ ∂f(x)` is normal to `C` at `x`.

Rockafellar routes this through the sublevel set `D = {z | f z ≤ α}` and Theorem 23.7. Read
directly it is one line: the subgradient inequality at `z` and maximality at `z` sandwich
`⟨z − x, x*⟩` between `0` and `0`. Only the finiteness of `f x` is used, so neither convexity of
`C` nor `x ∈ ri (dom f)` appears — those hypotheses of the book feed the other two clauses. -/
theorem theorem_32_4_normal (hfin : ∀ z ∈ C, f z ≠ ⊥ ∧ f z ≠ ⊤) {x : Rn n} (hx : x ∈ C)
    (hmax : ∀ z ∈ C, f z ≤ f x) {y : Rn n} (hy : y ∈ subgradient (pairing n) f x) :
    y ∈ normalCone (pairing n) C x :=
  mem_normalCone_of_mem_subgradient_of_isMaxOn (hfin x hx).1 (hfin x hx).2 hmax hy

/-- **Rockafellar, Theorem 32.4** (14047): the vector is **non-zero**. Rockafellar's argument is
that `inf f < f x` because `f` is not constant on `C`, hence `0 ∉ ∂f(x)`; here the witness of
non-constancy is passed directly, since a set on which `f` is not constant supplies one at every
one of its points. -/
theorem theorem_32_4_ne_zero {x : Rn n} (hmax : ∀ z ∈ C, f z ≤ f x) {z₀ : Rn n} (hz₀ : z₀ ∈ C)
    (hne : f z₀ ≠ f x) {y : Rn n} (hy : y ∈ subgradient (pairing n) f x) : y ≠ 0 :=
  ne_zero_of_mem_subgradient_of_isMaxOn hmax hz₀ hne hy

/-- **Rockafellar, Corollary 32.4.1** (14057): for a proper convex `f` and a non-empty `S` on
which `f` is not constant, if the supremum of `f` relative to `S` is attained at
`x ∈ ri (dom f)`, then every `x* ∈ ∂f(x)` is non-zero and the *linear* function `⟨·, x*⟩` attains
its supremum relative to `S` at `x`.

Rockafellar passes to `C = conv S` so that Theorem 32.4 applies to a convex set, and cites
Theorem 32.2 to move the supremum. That detour is unnecessary here: `theorem_32_4_normal` asks
nothing of `C`, so it applies to `S` itself, and normality is exactly the conclusion wanted
(Corollary 32.4.1 is `le_of_mem_normalCone`, which carries no convexity hypothesis either). -/
theorem corollary_32_4_1 (hp : Proper f) {S : Set (Rn n)} {x : Rn n} (hxri : x ∈ ri (dom f))
    (hmax : ∀ z ∈ S, f z ≤ f x) {z₀ : Rn n} (hz₀ : z₀ ∈ S) (hne : f z₀ ≠ f x)
    {y : Rn n} (hy : y ∈ subgradient (pairing n) f x) :
    y ≠ 0 ∧ ∀ z ∈ S, pairing n z y ≤ pairing n x y := by
  refine ⟨ne_zero_of_mem_subgradient_of_isMaxOn hmax hz₀ hne hy, fun z hz => ?_⟩
  exact le_of_mem_normalCone (mem_normalCone_of_mem_subgradient_of_isMaxOn (hp.ne_bot x)
    (mem_dom.1 (intrinsicInterior_subset hxri)).ne hmax hy) hz

/-- **Rockafellar, §32 (14061)**: the vectors normal to the Euclidean unit ball at a boundary
point `x` are exactly the `λx` with `λ ≥ 0`. -/
theorem normalCone_closedBall {x : Rn n} (hx : ‖x‖ = 1) :
    normalCone (pairing n) (Metric.closedBall (0 : Rn n) 1) x
      = {y : Rn n | ∃ lam : ℝ, 0 ≤ lam ∧ y = lam • x} := by
  have hxx : (inner ℝ x x : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_mul_norm, hx, mul_one]
  ext y
  simp only [mem_normalCone, Set.mem_ofPred_eq, map_sub, LinearMap.sub_apply,
    sub_nonpos, Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro hy
    rcases eq_or_ne y 0 with rfl | hy0
    · exact ⟨0, le_rfl, by simp⟩
    have hn0 : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hmem : ‖(‖y‖⁻¹ : ℝ) • y‖ ≤ 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hn0)]
    have hkey := hy _ hmem
    rw [pairing_apply, pairing_apply, real_inner_smul_left,
      real_inner_self_eq_norm_mul_norm, inv_mul_eq_div, mul_div_assoc,
      div_self (ne_of_gt hn0), mul_one] at hkey
    have hcs : (inner ℝ x y : ℝ) ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
    have heq : (inner ℝ x y : ℝ) = ‖x‖ * ‖y‖ := by
      rw [hx, one_mul] at hcs ⊢
      exact le_antisymm hcs hkey
    have hsm : ‖y‖ • x = ‖x‖ • y := inner_eq_norm_mul_iff_real.1 heq
    rw [hx, one_smul] at hsm
    exact ⟨‖y‖, hn0.le, hsm.symm⟩
  · rintro ⟨lam, hlam, rfl⟩ z hz
    have hcs : (inner ℝ z x : ℝ) ≤ ‖z‖ * ‖x‖ := real_inner_le_norm z x
    rw [hx, mul_one] at hcs
    have hzx : (inner ℝ z x : ℝ) ≤ 1 := le_trans hcs hz
    simp only [pairing_apply, real_inner_smul_right]
    rw [hxx]
    nlinarith

/-- **Rockafellar, §32 (14061)**: at a maximiser of `f` over the unit Euclidean ball,
maximisation leads to the "eigenvalue" condition `λx ∈ ∂f(x)`, `|x| = 1`. -/
theorem theorem_32_4_ball {x : Rn n} (hx : ‖x‖ = 1)
    (hfin : ∀ z ∈ Metric.closedBall (0 : Rn n) 1, f z ≠ ⊥ ∧ f z ≠ ⊤)
    (hmax : ∀ z ∈ Metric.closedBall (0 : Rn n) 1, f z ≤ f x) {z₀ : Rn n}
    (hz₀ : z₀ ∈ Metric.closedBall (0 : Rn n) 1) (hne : f z₀ ≠ f x) {y : Rn n}
    (hy : y ∈ subgradient (pairing n) f x) : ∃ lam : ℝ, 0 < lam ∧ y = lam • x := by
  have hxmem : x ∈ Metric.closedBall (0 : Rn n) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hx]
  have hyne : y ≠ 0 := theorem_32_4_ne_zero hmax hz₀ hne hy
  have hnormal := theorem_32_4_normal hfin hxmem hmax hy
  rw [normalCone_closedBall hx] at hnormal
  obtain ⟨lam, hlam, rfl⟩ := hnormal
  refine ⟨lam, lt_of_le_of_ne hlam ?_, rfl⟩
  rintro rfl
  exact hyne (by simp)

/-! ### The two examples of pp. 344–345 -/

/-- Coordinates of the pairing on `ℝ²`. `private`: nothing outside this module should be
reading coordinates. -/
private theorem pairing_two (u v : Rn 2) : pairing 2 u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- **Rockafellar, §32 (14023).** The parabolic convex set
`K = {(ξ₁, ξ₂) | ξ₁² + 4ξ₂ + 4 ≤ 0}`, whose support function is `parabolicFn`. -/
def parabolicSet : Set (Rn 2) := {y : Rn 2 | y 0 ^ 2 + 4 * y 1 + 4 ≤ 0}

theorem mem_parabolicSet {y : Rn 2} :
    y ∈ parabolicSet ↔ y 0 ^ 2 + 4 * y 1 + 4 ≤ 0 := Iff.rfl

/-- The boundary point of `parabolicSet` with abscissa `t`. -/
private noncomputable def parabolicPoint (t : ℝ) : Rn 2 :=
  WithLp.toLp 2 ![t, -(t ^ 2 + 4) / 4]

private theorem parabolicPoint_zero (t : ℝ) : parabolicPoint t 0 = t := rfl

private theorem parabolicPoint_one (t : ℝ) : parabolicPoint t 1 = -(t ^ 2 + 4) / 4 := rfl

private theorem parabolicPoint_mem (t : ℝ) : parabolicPoint t ∈ parabolicSet := by
  rw [mem_parabolicSet, parabolicPoint_zero, parabolicPoint_one]
  exact le_of_eq (by ring)

/-- The point `(0, s)` of `ℝ²`. -/
private noncomputable def verticalPoint (s : ℝ) : Rn 2 := WithLp.toLp 2 ![0, s]

private theorem verticalPoint_zero (s : ℝ) : verticalPoint s 0 = 0 := rfl

private theorem verticalPoint_one (s : ℝ) : verticalPoint s 1 = s := rfl

private theorem verticalPoint_mem {s : ℝ} (hs : s ≤ -1) : verticalPoint s ∈ parabolicSet := by
  rw [mem_parabolicSet, verticalPoint_zero, verticalPoint_one]
  nlinarith

/-- **Rockafellar, §32 (14017).** The closed proper convex function
`f(ξ₁, ξ₂) = ξ₁²/ξ₂ − ξ₂` for `ξ₂ > 0`, `0` at the origin, `+∞` elsewhere. Lean's `x / 0 = 0`
makes the first branch compute the second, so one `⨅ _ : p, …` suffices. -/
noncomputable def parabolicFn (x : Rn 2) : EReal :=
  ⨅ _ : 0 ≤ x 1 ∧ (x 1 = 0 → x 0 = 0), ((x 0 ^ 2 / x 1 - x 1 : ℝ) : EReal)

theorem parabolicFn_of_mem {x : Rn 2} (hx : 0 ≤ x 1 ∧ (x 1 = 0 → x 0 = 0)) :
    parabolicFn x = ((x 0 ^ 2 / x 1 - x 1 : ℝ) : EReal) := iInf_pos hx

theorem parabolicFn_of_notMem {x : Rn 2} (hx : ¬ (0 ≤ x 1 ∧ (x 1 = 0 → x 0 = 0))) :
    parabolicFn x = ⊤ := iInf_neg hx

/-- **Rockafellar, §32 (14023)**: `f` is the support function of the parabolic set, which is
the verification of convexity and closedness the book suggests in its own parenthesis. -/
theorem supportFn_parabolicSet : supportFn (pairing 2) parabolicSet = parabolicFn := by
  funext y
  by_cases hy : 0 ≤ y 1 ∧ (y 1 = 0 → y 0 = 0)
  · rw [parabolicFn_of_mem hy]
    rcases lt_or_eq_of_le hy.1 with hy1 | hy1
    · have hy1ne : y 1 ≠ 0 := ne_of_gt hy1
      refine le_antisymm (supportFn_le_coe_iff.2 fun x hx => ?_) ?_
      · have hx' : x 0 ^ 2 + 4 * x 1 + 4 ≤ 0 := hx
        rw [pairing_two, le_sub_iff_add_le, le_div_iff₀ hy1]
        nlinarith [sq_nonneg (2 * y 0 - x 0 * y 1),
          mul_nonneg (sq_nonneg (y 1)) (by linarith : (0 : ℝ) ≤ -(x 0 ^ 2 + 4 * x 1 + 4))]
      · have hval : pairing 2 (parabolicPoint (2 * y 0 / y 1)) y = y 0 ^ 2 / y 1 - y 1 := by
          rw [pairing_two, parabolicPoint_zero, parabolicPoint_one]
          field_simp
          ring
        rw [← hval]
        exact le_supportFn (parabolicPoint_mem _) y
    · have hy1' : y 1 = 0 := hy1.symm
      have hy0 : y 0 = 0 := hy.2 hy1'
      have hzero : ∀ x : Rn 2, pairing 2 x y = 0 := by
        intro x; rw [pairing_two, hy0, hy1']; ring
      have hsup : supportFn (pairing 2) parabolicSet y = ((0 : ℝ) : EReal) := by
        refine le_antisymm (supportFn_le_coe_iff.2 fun x _ => le_of_eq (hzero x)) ?_
        rw [← hzero (parabolicPoint 0)]
        exact le_supportFn (parabolicPoint_mem 0) y
      rw [hsup, hy0, hy1']
      norm_num
  · rw [parabolicFn_of_notMem hy, _root_.EReal.eq_top_iff_forall_lt]
    intro c
    by_cases hy1 : 0 ≤ y 1
    · have hy1' : y 1 = 0 := by
        by_contra h
        exact hy ⟨hy1, fun hc => absurd hc h⟩
      have hy0 : y 0 ≠ 0 := fun h => hy ⟨hy1, fun _ => h⟩
      have hval : pairing 2 (parabolicPoint ((c + 1) / y 0)) y = c + 1 := by
        rw [pairing_two, parabolicPoint_zero, hy1', mul_zero, add_zero]
        field_simp
      have hle := le_supportFn (B := pairing 2) (parabolicPoint_mem ((c + 1) / y 0)) y
      rw [hval] at hle
      exact lt_of_lt_of_le (by exact_mod_cast (by linarith : c < c + 1)) hle
    · have hyneg : y 1 < 0 := not_le.1 hy1
      have hy1ne : y 1 ≠ 0 := ne_of_lt hyneg
      have hnn : 0 ≤ (|c| + 1) / (-y 1) := div_nonneg (by positivity) (by linarith)
      have hs : -1 - (|c| + 1) / (-y 1) ≤ -1 := by linarith
      have hval : pairing 2 (verticalPoint (-1 - (|c| + 1) / (-y 1))) y = -y 1 + (|c| + 1) := by
        rw [pairing_two, verticalPoint_zero, verticalPoint_one]
        field_simp
        ring
      have hle := le_supportFn (B := pairing 2) (verticalPoint_mem hs) y
      rw [hval] at hle
      refine lt_of_lt_of_le ?_ hle
      exact_mod_cast (by cases abs_cases c <;> linarith : c < -y 1 + (|c| + 1))

theorem convexFn_parabolicFn : ConvexFn parabolicFn := by
  rw [← supportFn_parabolicSet]; exact convexFn_supportFn _ _

theorem closedFn_parabolicFn : ClosedFn parabolicFn := by
  rw [← supportFn_parabolicSet]; exact closedFn_supportFn

theorem proper_parabolicFn : Proper parabolicFn := by
  rw [← supportFn_parabolicSet]
  exact proper_supportFn ⟨parabolicPoint 0, parabolicPoint_mem 0⟩

/-! #### The two caps -/

private def cap (g : ℝ → ℝ) : Set (Rn 2) := {x : Rn 2 | g (x 0) ≤ x 1 ∧ x 1 ≤ 1}

private theorem zero_mem_cap {g : ℝ → ℝ} (hg0 : g 0 ≤ 0) : (0 : Rn 2) ∈ cap g := by
  have h0 : (0 : Rn 2) 0 = 0 := by simp
  have h1 : (0 : Rn 2) 1 = 0 := by simp
  exact ⟨by rw [h0, h1]; exact hg0, by rw [h1]; norm_num⟩

private theorem isClosed_cap {g : ℝ → ℝ} (hgc : Continuous g) : IsClosed (cap g) := by
  have hc0 : Continuous fun x : Rn 2 => x 0 := by fun_prop
  have hc1 : Continuous fun x : Rn 2 => x 1 := by fun_prop
  have hcg : Continuous fun x : Rn 2 => g (x 0) := hgc.comp hc0
  exact (isClosed_le hcg hc1).inter (isClosed_le hc1 continuous_const)

private theorem isBounded_cap {g : ℝ → ℝ} (hgnn : ∀ t : ℝ, 0 ≤ g t)
    (hgsq : ∀ t : ℝ, g t ≤ 1 → t ^ 2 ≤ 1) : Bornology.IsBounded (cap g) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2, fun x hx => ?_⟩
  have hx1nn : 0 ≤ x 1 := le_trans (hgnn _) hx.1
  have hsq : x 0 ^ 2 ≤ 1 := hgsq _ (le_trans hx.1 hx.2)
  have hnorm : ‖x‖ = Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    congr 1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  rw [hnorm]
  have hle : x 0 ^ 2 + x 1 ^ 2 ≤ 4 := by nlinarith [hx.2]
  calc Real.sqrt (x 0 ^ 2 + x 1 ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hle
    _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- The convexity inequality for `t ↦ t²` in the form `convex_cap` consumes. -/
private theorem sq_combo_le {p q a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * p + b * q) ^ 2 ≤ a * p ^ 2 + b * q ^ 2 := by
  have key : a * p ^ 2 + b * q ^ 2 - (a * p + b * q) ^ 2 = a * b * (p - q) ^ 2 := by
    linear_combination (-(a * p ^ 2 + b * q ^ 2)) * hab
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p - q))]

/-- The convexity inequality for `t ↦ t⁴`: square the one for `t ↦ t²` twice. -/
private theorem quartic_combo_le {p q a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * p + b * q) ^ 4 ≤ a * p ^ 4 + b * q ^ 4 :=
  calc (a * p + b * q) ^ 4 = ((a * p + b * q) ^ 2) ^ 2 := by ring
    _ ≤ (a * p ^ 2 + b * q ^ 2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) (sq_combo_le ha hb hab) 2
    _ ≤ a * (p ^ 2) ^ 2 + b * (q ^ 2) ^ 2 := sq_combo_le ha hb hab
    _ = a * p ^ 4 + b * q ^ 4 := by ring

private theorem convex_cap {g : ℝ → ℝ}
    (hg : ∀ p q a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      g (a * p + b * q) ≤ a * g p + b * g q) :
    Convex ℝ (cap g) := by
  intro x hx y hy a b ha hb hab
  have h0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := rfl
  have h1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := rfl
  have hcv := hg (x 0) (y 0) a b ha hb hab
  refine ⟨?_, ?_⟩
  · rw [h0, h1]
    have h₁ := mul_le_mul_of_nonneg_left hx.1 ha
    have h₂ := mul_le_mul_of_nonneg_left hy.1 hb
    linarith
  · rw [h1]
    have h₁ := mul_le_mul_of_nonneg_left hx.2 ha
    have h₂ := mul_le_mul_of_nonneg_left hy.2 hb
    linarith

private theorem parabolicFn_cap {g : ℝ → ℝ} (hgnn : ∀ t : ℝ, 0 ≤ g t)
    (hgz : ∀ t : ℝ, g t ≤ 0 → t = 0) {x : Rn 2} (hx : x ∈ cap g) :
    parabolicFn x = ((x 0 ^ 2 / x 1 - x 1 : ℝ) : EReal) :=
  parabolicFn_of_mem ⟨le_trans (hgnn _) hx.1, fun h => hgz _ (h ▸ hx.1)⟩

private theorem cap_subset_dom {g : ℝ → ℝ} (hgnn : ∀ t : ℝ, 0 ≤ g t)
    (hgz : ∀ t : ℝ, g t ≤ 0 → t = 0) : cap g ⊆ dom parabolicFn := fun x hx => by
  rw [mem_dom, parabolicFn_cap hgnn hgz hx]
  exact _root_.EReal.coe_lt_top _

private noncomputable def capPoint (k : ℕ) (t : ℝ) : Rn 2 := WithLp.toLp 2 ![t, t ^ k]

private theorem capPoint_zero (k : ℕ) (t : ℝ) : capPoint k t 0 = t := rfl

private theorem capPoint_one (k : ℕ) (t : ℝ) : capPoint k t 1 = t ^ k := rfl

private theorem capPoint_mem {k : ℕ} {t : ℝ} (ht : t ^ k ≤ 1) :
    capPoint k t ∈ cap (fun s : ℝ => s ^ k) :=
  ⟨le_of_eq (by rw [capPoint_zero, capPoint_one]), by rw [capPoint_one]; exact ht⟩

private theorem sq_nonneg' : ∀ t : ℝ, 0 ≤ t ^ 2 := fun t => sq_nonneg t

private theorem sq_eq_zero' : ∀ t : ℝ, t ^ 2 ≤ 0 → t = 0 := fun t h =>
  pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h (sq_nonneg t))

private theorem quartic_nonneg : ∀ t : ℝ, 0 ≤ t ^ 4 := fun t => by positivity

private theorem quartic_eq_zero : ∀ t : ℝ, t ^ 4 ≤ 0 → t = 0 := fun t h =>
  pow_eq_zero_iff (by norm_num) |>.1 (le_antisymm h (by positivity))

/-- **Rockafellar, §32 (14029).** `C = {(ξ₁, ξ₂) | ξ₁² ≤ ξ₂ ≤ 1}`. -/
def parabolicCap : Set (Rn 2) := {x : Rn 2 | x 0 ^ 2 ≤ x 1 ∧ x 1 ≤ 1}

/-- **Rockafellar, §32 (14037).** `D = {(ξ₁, ξ₂) | ξ₁⁴ ≤ ξ₂ ≤ 1}`. -/
def quarticCap : Set (Rn 2) := {x : Rn 2 | x 0 ^ 4 ≤ x 1 ∧ x 1 ≤ 1}

private theorem parabolicCap_eq : parabolicCap = cap (fun t : ℝ => t ^ 2) := rfl

private theorem quarticCap_eq : quarticCap = cap (fun t : ℝ => t ^ 4) := rfl

theorem zero_mem_parabolicCap : (0 : Rn 2) ∈ parabolicCap := by
  rw [parabolicCap_eq]; exact zero_mem_cap (by norm_num)

theorem isClosed_parabolicCap : IsClosed parabolicCap := by
  rw [parabolicCap_eq]; exact isClosed_cap (by fun_prop)

theorem isBounded_parabolicCap : Bornology.IsBounded parabolicCap := by
  rw [parabolicCap_eq]; exact isBounded_cap sq_nonneg' fun _ h => h

theorem convex_parabolicCap : Convex ℝ parabolicCap := by
  rw [parabolicCap_eq]; exact convex_cap fun _ _ _ _ ha hb hab => sq_combo_le ha hb hab

theorem parabolicCap_subset_dom : parabolicCap ⊆ dom parabolicFn := by
  rw [parabolicCap_eq]; exact cap_subset_dom sq_nonneg' sq_eq_zero'

theorem zero_mem_quarticCap : (0 : Rn 2) ∈ quarticCap := by
  rw [quarticCap_eq]; exact zero_mem_cap (by norm_num)

theorem isClosed_quarticCap : IsClosed quarticCap := by
  rw [quarticCap_eq]; exact isClosed_cap (by fun_prop)

theorem isBounded_quarticCap : Bornology.IsBounded quarticCap := by
  rw [quarticCap_eq]
  exact isBounded_cap quartic_nonneg fun t h => by nlinarith [sq_nonneg t, sq_nonneg (t ^ 2 - 1)]

theorem convex_quarticCap : Convex ℝ quarticCap := by
  rw [quarticCap_eq]; exact convex_cap fun _ _ _ _ ha hb hab => quartic_combo_le ha hb hab

theorem quarticCap_subset_dom : quarticCap ⊆ dom parabolicFn := by
  rw [quarticCap_eq]; exact cap_subset_dom quartic_nonneg quartic_eq_zero

/-! #### The first example: a supremum that is not attained -/

/-- **Rockafellar, §32 (14035)**: "clearly `f(ξ₁, ξ₂) < 1` throughout `C`". On `C` one has
`ξ₁² ≤ ξ₂`, so `ξ₁²/ξ₂ ≤ 1` and `f ≤ 1 − ξ₂ < 1` when `ξ₂ > 0`; and `ξ₂ = 0` forces the
origin, where `f = 0`. -/
theorem parabolicFn_lt_one_of_mem_parabolicCap {x : Rn 2} (hx : x ∈ parabolicCap) :
    parabolicFn x < ((1 : ℝ) : EReal) := by
  rw [parabolicFn_cap (g := fun t : ℝ => t ^ 2) sq_nonneg' sq_eq_zero' hx,
    _root_.EReal.coe_lt_coe_iff]
  rcases eq_or_lt_of_le (le_trans (sq_nonneg (x 0)) hx.1) with h | h
  · have hx0 : x 0 = 0 := sq_eq_zero' _ (h ▸ hx.1)
    rw [hx0, ← h]
    norm_num
  · have hdiv : x 0 ^ 2 / x 1 ≤ 1 := (div_le_one h).2 hx.1
    linarith

/-- **Rockafellar, §32 (14035)**: "the value of `f(ξ₁, ξ₂)` approaches `1` as `(ξ₁, ξ₂)` moves
toward `(0, 0)` along the boundary of `C`." On the boundary parabola `ξ₂ = ξ₁²` the value is
exactly `1 − t²`. -/
theorem parabolicFn_capPoint {t : ℝ} (ht : t ≠ 0) (ht1 : t ^ 2 ≤ 1) :
    parabolicFn (capPoint 2 t) = ((1 - t ^ 2 : ℝ) : EReal) := by
  rw [parabolicFn_cap sq_nonneg' sq_eq_zero' (capPoint_mem ht1), capPoint_zero, capPoint_one,
    div_self (pow_ne_zero 2 ht)]

/-- **Rockafellar, §32 (14035)**: "thus `1` is the supremum of `f` relative to `C`, and this
supremum is not attained."

Given a candidate maximiser with value `r < 1`, the boundary point `(t, t²)` with
`t = min 1 ((1 − r)/2)` lies in `C` and carries the strictly larger value `1 − t²`. -/
theorem parabolicCap_not_attained :
    ¬ ∃ z ∈ parabolicCap, ∀ w ∈ parabolicCap, parabolicFn w ≤ parabolicFn z := by
  rintro ⟨z, hz, hzmax⟩
  have hfz : parabolicFn z = ((z 0 ^ 2 / z 1 - z 1 : ℝ) : EReal) :=
    parabolicFn_cap (g := fun t : ℝ => t ^ 2) sq_nonneg' sq_eq_zero' hz
  have hr1 : z 0 ^ 2 / z 1 - z 1 < 1 := by
    have hlt := parabolicFn_lt_one_of_mem_parabolicCap hz
    rw [hfz, _root_.EReal.coe_lt_coe_iff] at hlt
    exact hlt
  have ht0 : 0 < min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2) := lt_min one_pos (by linarith)
  have ht1 : min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2) ≤ 1 := min_le_left _ _
  have ht2 : min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2) ≤ (1 - (z 0 ^ 2 / z 1 - z 1)) / 2 :=
    min_le_right _ _
  have hsq : min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2) ^ 2 ≤ 1 := pow_le_one₀ ht0.le ht1
  have hmem : capPoint 2 (min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2)) ∈ parabolicCap := by
    rw [parabolicCap_eq]; exact capPoint_mem hsq
  have hle := hzmax _ hmem
  rw [parabolicFn_capPoint (ne_of_gt ht0) hsq, hfz, _root_.EReal.coe_le_coe_iff] at hle
  nlinarith

/-! #### The second example: a supremum that is not finite -/

/-- **Rockafellar, §32 (14043)**: "along the boundary curve `ξ₁⁴ = ξ₂` of `D`, the value of
`f(ξ₁, ξ₂)` is `ξ₁⁻² − ξ₂`, and this rises to `+∞` as `(ξ₁, ξ₂)` moves toward the origin. Thus
`f` is not even bounded above on `D`."

Given a candidate bound `r`, the boundary point `(t, t⁴)` with `t = min 1 (1/(|r| + 2))` lies in
`D` and carries a value at least `(|r| + 2)² − 1 > r`. -/
theorem quarticCap_not_bddAbove :
    ¬ ∃ r : ℝ, ∀ w ∈ quarticCap, parabolicFn w ≤ (r : EReal) := by
  rintro ⟨r, hr⟩
  have hM1 : (1 : ℝ) ≤ |r| + 2 := by cases abs_cases r <;> linarith
  have hM0 : (0 : ℝ) < |r| + 2 := by linarith
  have hrM : r ≤ |r| + 2 - 2 := by cases abs_cases r <;> linarith
  have ht0 : 0 < min 1 (1 / (|r| + 2)) := lt_min one_pos (by positivity)
  have ht1 : min 1 (1 / (|r| + 2)) ≤ 1 := min_le_left _ _
  have htM : min 1 (1 / (|r| + 2)) ≤ 1 / (|r| + 2) := min_le_right _ _
  have hmt : min 1 (1 / (|r| + 2)) * (|r| + 2) ≤ 1 := (le_div_iff₀ hM0).1 htM
  have hq1 : min 1 (1 / (|r| + 2)) ^ 4 ≤ 1 := pow_le_one₀ ht0.le ht1
  have hmem : capPoint 4 (min 1 (1 / (|r| + 2))) ∈ quarticCap := by
    rw [quarticCap_eq]; exact capPoint_mem hq1
  have hval : parabolicFn (capPoint 4 (min 1 (1 / (|r| + 2))))
      = ((min 1 (1 / (|r| + 2)) ^ 2 / min 1 (1 / (|r| + 2)) ^ 4
          - min 1 (1 / (|r| + 2)) ^ 4 : ℝ) : EReal) := by
    rw [parabolicFn_cap quartic_nonneg quartic_eq_zero (capPoint_mem hq1), capPoint_zero,
      capPoint_one]
  have hsq : min 1 (1 / (|r| + 2)) ^ 2 * (|r| + 2) ^ 2 ≤ 1 := by
    nlinarith [mul_pos ht0 hM0]
  have hbig : (|r| + 2) ^ 2 ≤ min 1 (1 / (|r| + 2)) ^ 2 / min 1 (1 / (|r| + 2)) ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (min 1 (1 / (|r| + 2))), pow_pos ht0 2]
  have hle := hr _ hmem
  rw [hval, _root_.EReal.coe_le_coe_iff] at hle
  nlinarith

/-! #### The weakening of Corollary 32.3.2 that the two examples refute -/

/-- **Rockafellar, §32 (14015)**, first half, *stated and refuted*: Corollary 32.3.2 with
`C ⊆ ri (dom f)` weakened to `C ⊆ dom f` would say that the supremum is still attained. It is
not, and adding `ClosedFn` and `Proper` — the book's "even when `f` is closed" — does not save
it. The witness is the first example. -/
theorem corollary_32_3_2_not_attained_of_subset_dom :
    ¬ ∀ (g : Rn 2 → EReal) (D : Set (Rn 2)), ConvexFn g → ClosedFn g → Proper g →
        D.Nonempty → IsClosed D → Bornology.IsBounded D → Convex ℝ D → D ⊆ dom g →
        ∃ z ∈ D, ∀ w ∈ D, g w ≤ g z := fun h =>
  parabolicCap_not_attained (h parabolicFn parabolicCap convexFn_parabolicFn
    closedFn_parabolicFn proper_parabolicFn ⟨0, zero_mem_parabolicCap⟩ isClosed_parabolicCap
    isBounded_parabolicCap convex_parabolicCap parabolicCap_subset_dom)

/-- **Rockafellar, §32 (14015)**, second half, *stated and refuted*: the same weakening would
say that the supremum is still finite. The witness is the second example, where `f` is not even
bounded above on a compact convex subset of its domain. -/
theorem corollary_32_3_2_not_bddAbove_of_subset_dom :
    ¬ ∀ (g : Rn 2 → EReal) (D : Set (Rn 2)), ConvexFn g → ClosedFn g → Proper g →
        D.Nonempty → IsClosed D → Bornology.IsBounded D → Convex ℝ D → D ⊆ dom g →
        ∃ r : ℝ, ∀ w ∈ D, g w ≤ (r : EReal) := fun h =>
  quarticCap_not_bddAbove (h parabolicFn quarticCap convexFn_parabolicFn
    closedFn_parabolicFn proper_parabolicFn ⟨0, zero_mem_quarticCap⟩ isClosed_quarticCap
    isBounded_quarticCap convex_quarticCap quarticCap_subset_dom)

end Rockafellar
