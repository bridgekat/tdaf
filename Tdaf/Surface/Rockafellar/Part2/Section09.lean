/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.Convex.Join
import Tdaf.Analysis.Convex.Caratheodory
import Tdaf.Analysis.Convex.Duality.Gauge
import Tdaf.Analysis.Convex.Recession.Closedness
import Tdaf.Analysis.Convex.Recession.ConeHull
import Tdaf.Surface.Common.Euclidean

/-!
# Rockafellar, §9: Some Closedness Criteria

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §9, pp. 72–81. The section introduces no
new concepts: it is entirely criteria, built on §8's recession cones, for an operation on convex
sets or convex functions to preserve closedness.

## Contents

| label | declaration |
|---|---|
| Theorem 9.1 | `theorem_9_1_closure`, `theorem_9_1_recession`, `theorem_9_1_isClosed` |
| Corollary 9.1.1 | `corollary_9_1_1_closure`, `_recession`, `_isClosed` |
| Corollary 9.1.2 | `corollary_9_1_2_isClosed`, `_recession`, `_isClosed_of_isBounded` |
| Corollary 9.1.3 | `corollary_9_1_3` |
| Theorem 9.2 | `theorem_9_2`, `theorem_9_2_attained` |
| Corollary 9.2.1 | `corollary_9_2_1`, `corollary_9_2_1_recession`, `corollary_9_2_1_attained` |
| Corollary 9.2.2 | `corollary_9_2_2`, `corollary_9_2_2_recession`, `corollary_9_2_2_attained` |
| Theorem 9.3 | `theorem_9_3_closed`, `theorem_9_3_recession`, `theorem_9_3_closure` |
| Theorem 9.4 | `theorem_9_4_closed`, `_proper`, `_recession`, `_closure` |
| Theorem 9.5 | `theorem_9_5_closed`, `theorem_9_5_recession`, `theorem_9_5_closure` |
| Theorem 9.6 | `theorem_9_6`, `theorem_9_6_iUnion` |
| Corollary 9.6.1 | `corollary_9_6_1` |
| Theorem 9.7 | `theorem_9_7`, `theorem_9_7_proper`, `_attained`, `_closed`, `_iInf_pos` |
| Corollary 9.7.1 | `corollary_9_7_1_closed`, `corollary_9_7_1_level`, `corollary_9_7_1_zero` |
| Theorem 9.8 | `theorem_9_8`, `theorem_9_8_recession` |
| Corollary 9.8.1 | `corollary_9_8_1_isClosed`, `corollary_9_8_1_recession` |
| Corollary 9.8.2 | `corollary_9_8_2` |
| Corollary 9.8.3 | `corollary_9_8_3`, `corollary_9_8_3_recession`, `corollary_9_8_3_attained` |

## The `λ ≥ 0⁺` convention

Rockafellar writes `λ₁C₁ + ⋯ + λₘCₘ` where each `λᵢ` ranges over the non-negative reals *together
with a formal symbol* `0⁺`, and where `0⁺Cᵢ` denotes the recession cone `0⁺Cᵢ` rather than the
`{0}` that plain `0 • Cᵢ` would give (book, pp. 79 and 81). The same convention governs the
infimum in Theorem 9.7, where `f0⁺` is the recession *function*.

That is a genuine extra symbol, not a limit, and it is modelled here as one: `ExtCoeff` is the
disjoint union of `ℝ` and a formal `0⁺`, with `ExtCoeff.smulSet` acting on sets and
`ExtCoeff.smulFn` acting on functions. Each carries its bridge to the backbone —
`ExtCoeff.smulSet_ofReal`, `ExtCoeff.smulSet_zeroPlus`, `ExtCoeff.smulFn_ofReal`,
`ExtCoeff.smulFn_zeroPlus` — and every theorem below is proved by *reducing to* the backbone form
rather than by unfolding the convention. `iUnion_extCoeff_pair` is where the reduction has content:
it identifies Rockafellar's `⋃ {λ₁C₁ + λ₂C₂ | λᵢ ≥ 0⁺, λ₁ + λ₂ = 1}` with the backbone's
convention-free `conv (C₁ ∪ C₂) + (0⁺C₁ + 0⁺C₂)`.

This is the definition §19 (Theorems 19.5.1, 19.6, 19.7) is expected to inherit.

## What is not here

* **The `m`-ary forms of Corollaries 9.1.1, 9.1.3 and 9.2.1, of Theorem 9.3, and of Theorems 9.8
  and its corollaries** — *deferred by scope, backbone gap*. The book states each for `C₁, …, Cₘ`
  (respectively `f₁, …, fₘ`); the backbone proves each for two sets or two functions and no
  backbone result asks for more, so every `m`-ary statement here is its `m = 2` instance. The
  `m`-ary version of Corollary 9.1.1 is not a contentless induction — the book's own proof runs
  Theorem 9.1 on the product `C₁ ⊕ ⋯ ⊕ Cₘ ⊆ ℝᵐⁿ`. `Recession/Cone.lean` now has the coordinatewise
  half of that, `recessionCone_pi` and `linealitySpace_pi`; what is still missing is the sum map
  `(xᵢ) ↦ ∑ xᵢ` run against a `Set.pi`. Corollary 9.2.1 goes the same way — the book proves it by
  running Theorem 9.2 on the separable sum `h(x₁, …, xₘ) = f₁(x₁) + ⋯ + fₘ(xₘ)` over `ℝᵐⁿ` — and it
  needs, in addition, an `m`-ary infimal convolution and the recession function of a separable sum.
* **Theorem 9.2's recession formula `(Ah)0⁺ = A(h0⁺)`** — *omitted, backbone gap*.
  `closedProperConvexFn_mapLin` delivers the epigraph identity, closedness, properness and
  attainment, but not the recession identity; getting it means re-running Theorem 9.1's
  recession half on `epi h` and then recognising `B(epi (h0⁺))` as `epi (A(h0⁺))`, which is a
  second application of the theorem and belongs beside the first, in the backbone.
* **The two worked examples** (the non-closed image of `exp[-(ξ₁ξ₂)^(1/2)]`'s epigraph, p. 72, and
  `C = {ξ₂ ≥ ξ₁²}` with `0⁺(AC) ≠ A(0⁺C)`, p. 75) — *omitted*. They are motivation, and the
  hypotheses they show to be necessary are already carried as hypotheses.
* **The monotone-hull illustration of Corollary 9.2.2** (`g x = inf {f y | y ≥ x}`, p. 77) —
  *omitted*. It is Corollary 9.2.2 applied to `δ(· | -C)` for `C` the non-negative orthant, and
  the orthant is not a §9 notion.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §9.
-/

open Set Pointwise

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

variable {n m : ℕ}

/-! ### Rockafellar's extended coefficient `λ ≥ 0⁺` -/

/-- **Rockafellar's extended coefficient** `λ ≥ 0⁺` (book, pp. 79 and 81): either an ordinary real
coefficient `λ`, or the formal symbol `0⁺`. -/
inductive ExtCoeff where
  /-- An ordinary real coefficient `λ`. -/
  | ofReal (t : ℝ) : ExtCoeff
  /-- The formal symbol `0⁺`, distinct from the real number `0`. -/
  | zeroPlus : ExtCoeff

namespace ExtCoeff

/-- `λ ≥ 0⁺`: a real coefficient is admitted when it is non-negative, and `0⁺` always is. -/
def Nonneg : ExtCoeff → Prop
  | ofReal t => 0 ≤ t
  | zeroPlus => True

/-- `λ > 0 or λ = 0⁺`, the index set of the unions in Theorems 9.6 and 9.7. -/
def Pos : ExtCoeff → Prop
  | ofReal t => 0 < t
  | zeroPlus => True

/-- The numerical value of `λ`, with `0⁺` counting as `0`. This is what `λ₁ + ⋯ + λₘ = 1` means in
Theorem 9.8. -/
def toReal : ExtCoeff → ℝ
  | ofReal t => t
  | zeroPlus => 0

/-- **`λC` in the `λ ≥ 0⁺` convention**: `0⁺C` is the recession cone of `C`, not `{0}`. -/
def smulSet {n : ℕ} : ExtCoeff → Set (Rn n) → Set (Rn n)
  | ofReal t, C => t • C
  | zeroPlus, C => recessionCone C

/-- **`fλ` in the `λ ≥ 0⁺` convention**: `f0⁺` is the recession function of `f`, and for a real
`λ` it is §5's right scalar multiple `fλ`. -/
noncomputable def smulFn {n : ℕ} : ExtCoeff → (Rn n → EReal) → (Rn n → EReal)
  | ofReal t, f => smulRight f t
  | zeroPlus, f => recessionFn f

/-- The numerical value of an ordinary coefficient is itself. -/
@[simp] theorem toReal_ofReal (t : ℝ) : (ofReal t).toReal = t := rfl

/-- The numerical value of `0⁺` is `0`: this is what makes `λ₁ + λ₂ = 1` exclude `λ₁ = λ₂ = 0⁺`. -/
@[simp] theorem toReal_zeroPlus : zeroPlus.toReal = 0 := rfl

/-- Bridge: on an ordinary coefficient the convention is plain scalar multiplication of sets. -/
@[simp] theorem smulSet_ofReal (t : ℝ) (C : Set (Rn n)) : (ofReal t).smulSet C = t • C := rfl

/-- Bridge: `0⁺C` is the backbone's `recessionCone C`. -/
@[simp] theorem smulSet_zeroPlus (C : Set (Rn n)) : zeroPlus.smulSet C = recessionCone C := rfl

/-- Bridge: on an ordinary coefficient the convention is §5's `fλ`. -/
@[simp] theorem smulFn_ofReal (t : ℝ) (f : Rn n → EReal) :
    (ofReal t).smulFn f = smulRight f t := rfl

/-- Bridge: `f0⁺` is the backbone's `recessionFn f`. -/
@[simp] theorem smulFn_zeroPlus (f : Rn n → EReal) : zeroPlus.smulFn f = recessionFn f := rfl

end ExtCoeff

/-! ### Theorem 9.1 and its corollaries -/

/-- **Rockafellar, Theorem 9.1.** Let `C` be a non-empty convex set in `ℝⁿ` and `A` a linear
transformation from `ℝⁿ` to `ℝᵐ`. Assume that every non-zero `z ∈ 0⁺(cl C)` with `Az = 0` belongs
to the lineality space of `cl C`. Then `cl (AC) = A (cl C)`.

Specialises `Convex.closure_image_eq`, which does not need `C` non-empty. -/
theorem theorem_9_1_closure {C : Set (Rn n)} (hC : Convex ℝ C) (A : Rn n →ₗ[ℝ] Rn m)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    closure (A '' C) = A '' closure C :=
  Convex.closure_image_eq hC A h

/-- **Rockafellar, Theorem 9.1**, second conclusion: `0⁺(A (cl C)) = A (0⁺(cl C))`.

Specialises `Convex.recessionCone_image_closure`. -/
theorem theorem_9_1_recession {C : Set (Rn n)} (hC : Convex ℝ C) (hne : C.Nonempty)
    (A : Rn n →ₗ[ℝ] Rn m)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    recessionCone (A '' closure C) = A '' recessionCone (closure C) :=
  Convex.recessionCone_image_closure hC hne A h

/-- **Rockafellar, Theorem 9.1**, the "in particular" clause: if `C` is closed and `z = 0` is the
only `z ∈ 0⁺C` with `Az = 0`, then `AC` is closed.

Specialises `isClosed_image_of_recessionCone_inter_ker`, whose hypothesis is stated as
`0⁺C ∩ ker A ⊆ {0}`. -/
theorem theorem_9_1_isClosed {C : Set (Rn n)} (hC : Convex ℝ C) (hCc : IsClosed C)
    (A : Rn n →ₗ[ℝ] Rn m) (h : ∀ z ∈ recessionCone C, A z = 0 → z = 0) :
    IsClosed (A '' C) := by
  refine isClosed_image_of_recessionCone_inter_ker A hC hCc fun z hz => ?_
  exact Set.mem_singleton_iff.2 (h z hz.1 (LinearMap.mem_ker.1 hz.2))

/-- **Rockafellar, Corollary 9.1.1** for `m = 2`. If the only way a direction of recession of
`cl C₁` and one of `cl C₂` can cancel is inside the two lineality spaces, then
`cl (C₁ + C₂) = cl C₁ + cl C₂`.

Specialises `Convex.closure_add_eq`. The book states this for `m` sets; see
`## What is not here`. -/
theorem corollary_9_1_1_closure {C D : Set (Rn n)} (hC : Convex ℝ C) (hCne : C.Nonempty)
    (hD : Convex ℝ D) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone (closure C), ∀ w ∈ recessionCone (closure D), z + w = 0 →
      z ∈ linealitySpace (closure C) ∧ w ∈ linealitySpace (closure D)) :
    closure (C + D) = closure C + closure D :=
  Convex.closure_add_eq hC hCne hD hDne h

/-- **Rockafellar, Corollary 9.1.1**, second conclusion:
`0⁺(cl C₁ + cl C₂) = 0⁺(cl C₁) + 0⁺(cl C₂)`.

Specialises `Convex.recessionCone_add`. -/
theorem corollary_9_1_1_recession {C D : Set (Rn n)} (hC : Convex ℝ C) (hCne : C.Nonempty)
    (hD : Convex ℝ D) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone (closure C), ∀ w ∈ recessionCone (closure D), z + w = 0 →
      z ∈ linealitySpace (closure C) ∧ w ∈ linealitySpace (closure D)) :
    recessionCone (closure C + closure D) =
      recessionCone (closure C) + recessionCone (closure D) :=
  Convex.recessionCone_add hC hCne hD hDne h

/-- **Rockafellar, Corollary 9.1.1**, the "in particular" clause: under the same hypothesis
`C₁ + C₂` is closed when `C₁` and `C₂` are.

Specialises `Convex.isClosed_add`. -/
theorem corollary_9_1_1_isClosed {C D : Set (Rn n)} (hC : Convex ℝ C) (hCc : IsClosed C)
    (hCne : C.Nonempty) (hD : Convex ℝ D) (hDc : IsClosed D) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone C, ∀ w ∈ recessionCone D, z + w = 0 →
      z ∈ linealitySpace C ∧ w ∈ linealitySpace D) :
    IsClosed (C + D) :=
  Convex.isClosed_add hC hCc hCne hD hDc hDne h

/-- **Rockafellar, Corollary 9.1.2.** Let `C₁` and `C₂` be non-empty closed convex sets in `ℝⁿ`
with no direction of recession of `C₁` whose opposite is a direction of recession of `C₂`. Then
`C₁ + C₂` is closed.

Specialises `Convex.isClosed_add_of_neg_notMem_recessionCone`. -/
theorem corollary_9_1_2_isClosed {C D : Set (Rn n)} (hC : Convex ℝ C) (hCc : IsClosed C)
    (hCne : C.Nonempty) (hD : Convex ℝ D) (hDc : IsClosed D) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone C, -z ∈ recessionCone D → z = 0) :
    IsClosed (C + D) :=
  Convex.isClosed_add_of_neg_notMem_recessionCone hC hCc hCne hD hDc hDne h

/-- **Rockafellar, Corollary 9.1.2**, second conclusion:
`0⁺(C₁ + C₂) = 0⁺C₁ + 0⁺C₂`.

Specialises `Convex.recessionCone_add_of_neg_notMem_recessionCone`. -/
theorem corollary_9_1_2_recession {C D : Set (Rn n)} (hC : Convex ℝ C) (hCc : IsClosed C)
    (hCne : C.Nonempty) (hD : Convex ℝ D) (hDc : IsClosed D) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone C, -z ∈ recessionCone D → z = 0) :
    recessionCone (C + D) = recessionCone C + recessionCone D :=
  Convex.recessionCone_add_of_neg_notMem_recessionCone hC hCc hCne hD hDc hDne h

/-- **Rockafellar, Corollary 9.1.2**, the parenthetical clause: the hypothesis holds in particular
when one of the two sets is bounded.

Specialises `Convex.isClosed_add_of_isBounded`. -/
theorem corollary_9_1_2_isClosed_of_isBounded {C D : Set (Rn n)} (hC : Convex ℝ C)
    (hCc : IsClosed C) (hCne : C.Nonempty) (hCb : Bornology.IsBounded C) (hD : Convex ℝ D)
    (hDc : IsClosed D) (hDne : D.Nonempty) :
    IsClosed (C + D) :=
  Convex.isClosed_add_of_isBounded hC hCc hCne hCb hD hDc hDne

/-- **Rockafellar, Corollary 9.1.3** for `m = 2`. For convex cones the recession cone of the
closure is the closure itself, so Corollary 9.1.1's hypothesis becomes a hypothesis about
`cl K₁` and `cl K₂`, and `cl (K₁ + K₂) = cl K₁ + cl K₂`.

Specialises `closure_add_coe_pointedCone`. Rockafellar's cones need not contain the origin; the
backbone models a convex cone as a `PointedCone`, which does. -/
theorem corollary_9_1_3 (K L : PointedCone ℝ (Rn n))
    (h : ∀ z ∈ closure (K : Set (Rn n)), ∀ w ∈ closure (L : Set (Rn n)), z + w = 0 →
      z ∈ linealitySpace (closure (K : Set (Rn n))) ∧
        w ∈ linealitySpace (closure (L : Set (Rn n)))) :
    closure ((K : Set (Rn n)) + (L : Set (Rn n)))
      = closure (K : Set (Rn n)) + closure (L : Set (Rn n)) :=
  closure_add_coe_pointedCone K L h

/-! ### Theorem 9.2 and its corollaries -/

/-- **Rockafellar, Theorem 9.2.** Let `h` be a closed proper convex function on `ℝⁿ` and `A` a
linear transformation from `ℝⁿ` to `ℝᵐ`. Assume `Az ≠ 0` for every `z` with `(h0⁺)(z) ≤ 0` and
`(h0⁺)(-z) > 0`. Then `Ah`, where `(Ah)(y) = inf {h x | A x = y}`, is a closed proper convex
function.

Specialises `closedProperConvexFn_mapLin`. The hypothesis is transported by
`mk_zero_mem_linealitySpace_epi_iff`: "`(h0⁺)(z) ≤ 0` and `(h0⁺)(-z) > 0` force `Az ≠ 0`" is the
contrapositive of "`(h0⁺)(z) ≤ 0` and `Az = 0` force `z ∈ constancySpace h`". -/
theorem theorem_9_2 {f : Rn n → EReal} (hconv : ConvexFn f) (hp : Proper f)
    (hc : IsClosed (epi f)) (A : Rn n →ₗ[ℝ] Rn m)
    (hrec : ∀ z, recessionFn f z ≤ 0 → A z = 0 → z ∈ constancySpace f) :
    ClosedProperConvexFn (mapLin A f) :=
  (closedProperConvexFn_mapLin hconv hp hc A hrec).2

/-- **Rockafellar, Theorem 9.2**, last sentence: for each `y` with `(Ah)(y) ≠ +∞` the infimum
defining `(Ah)(y)` is attained.

Specialises `exists_mapLin_eq`, which reads attainment off the epigraph identity
`epi (Ah) = B (epi h)`. -/
theorem theorem_9_2_attained {f : Rn n → EReal} (hconv : ConvexFn f) (hp : Proper f)
    (hc : IsClosed (epi f)) (A : Rn n →ₗ[ℝ] Rn m)
    (hrec : ∀ z, recessionFn f z ≤ 0 → A z = 0 → z ∈ constancySpace f)
    {y : Rn m} {μ : ℝ} (hμ : mapLin A f y ≤ (μ : EReal)) :
    ∃ x : Rn n, A x = y ∧ f x ≤ (μ : EReal) :=
  exists_mapLin_eq hconv hp hc A hrec hμ

/-- Rockafellar's hypothesis in Corollary 9.2.1, at `m = 2`, in the shape the backbone takes it:
the directions `z` with `(f₁0⁺)(z) + (f₂0⁺)(-z) ≤ 0` form a symmetric set. The two are equivalent,
because `z₁ + z₂ = 0` says exactly that `z₂ = -z₁`. -/
private theorem recessionFn_symm_of_corollary_9_2_1 {f g : Rn n → EReal}
    (h : ∀ z w : Rn n, recessionFn f z + recessionFn g w ≤ 0 →
      0 < recessionFn f (-z) + recessionFn g (-w) → z + w ≠ 0) :
    ∀ z : Rn n, recessionFn f z + recessionFn g (-z) ≤ 0 →
      recessionFn f (-z) + recessionFn g z ≤ 0 := by
  intro z hz
  by_contra hcon
  refine h z (-z) hz ?_ (add_neg_cancel z)
  rw [neg_neg]
  exact not_le.1 hcon

/-- **Rockafellar, Corollary 9.2.1** for `m = 2`. Let `f₁, f₂` be closed proper convex functions on
`ℝⁿ` such that `z₁ + z₂ ≠ 0` for every pair of vectors with

`(f₁0⁺)(z₁) + (f₂0⁺)(z₂) ≤ 0` and `(f₁0⁺)(-z₁) + (f₂0⁺)(-z₂) > 0`.

Then the infimal convolute `f₁ □ f₂` is a closed proper convex function.

This is genuinely weaker in hypothesis than Corollary 9.2.2, which demands
`(f₁0⁺)(z) + (f₂0⁺)(-z) > 0` for every `z ≠ 0`: here `f₁ = f₂ = 0` is admitted, and there it is
not. Specialises `closedProperConvexFn_infConv_of_recessionFn_symm`. -/
theorem corollary_9_2_1 {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : ∀ z w : Rn n, recessionFn f z + recessionFn g w ≤ 0 →
      0 < recessionFn f (-z) + recessionFn g (-w) → z + w ≠ 0) :
    ClosedProperConvexFn (infConv f g) :=
  (closedProperConvexFn_infConv_of_recessionFn_symm hf hg
    (recessionFn_symm_of_corollary_9_2_1 h)).2.1

/-- **Rockafellar, Corollary 9.2.1**, last formula: `(f₁ □ f₂)0⁺ = f₁0⁺ □ f₂0⁺`. -/
theorem corollary_9_2_1_recession {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : ∀ z w : Rn n, recessionFn f z + recessionFn g w ≤ 0 →
      0 < recessionFn f (-z) + recessionFn g (-w) → z + w ≠ 0) :
    recessionFn (infConv f g) = infConv (recessionFn f) (recessionFn g) :=
  (closedProperConvexFn_infConv_of_recessionFn_symm hf hg
    (recessionFn_symm_of_corollary_9_2_1 h)).2.2

/-- **Rockafellar, Corollary 9.2.1**, attainment: the infimum in the definition of
`(f₁ □ f₂)(x)` is attained for each `x`.

Specialises `exists_add_eq_of_infConv_le_of_recessionFn_symm`; the epigraph identity
`epi (f₁ □ f₂) = epi f₁ + epi f₂` *is* the attainment statement. -/
theorem corollary_9_2_1_attained {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : ∀ z w : Rn n, recessionFn f z + recessionFn g w ≤ 0 →
      0 < recessionFn f (-z) + recessionFn g (-w) → z + w ≠ 0) {x : Rn n} {μ : ℝ}
    (hμ : infConv f g x ≤ (μ : EReal)) :
    ∃ (y : Rn n) (ν ρ : ℝ), y + (x - y) = x ∧ ν + ρ = μ ∧ f y ≤ (ν : EReal) ∧
      g (x - y) ≤ (ρ : EReal) :=
  exists_add_eq_of_infConv_le_of_recessionFn_symm hf hg
    (recessionFn_symm_of_corollary_9_2_1 h) hμ

/-- **Rockafellar, Corollary 9.2.2.** Let `f₁, f₂` be closed proper convex functions on `ℝⁿ` with
`(f₁0⁺)(z) + (f₂0⁺)(-z) > 0` for every `z ≠ 0`. Then `f₁ □ f₂` is a closed proper convex function.

Specialises `closedProperConvexFn_infConv`. -/
theorem corollary_9_2_2 {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : ∀ z : Rn n, z ≠ 0 → 0 < recessionFn f z + recessionFn g (-z)) :
    ClosedProperConvexFn (infConv f g) :=
  (closedProperConvexFn_infConv hf hg h).2.1

/-- **Rockafellar, Corollary 9.2.2**, last formula: `(f₁ □ f₂)0⁺ = f₁0⁺ □ f₂0⁺`.

The same formula under the weaker hypothesis of Corollary 9.2.1 is
`corollary_9_2_1_recession`. -/
theorem corollary_9_2_2_recession {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : ∀ z : Rn n, z ≠ 0 → 0 < recessionFn f z + recessionFn g (-z)) :
    recessionFn (infConv f g) = infConv (recessionFn f) (recessionFn g) :=
  (closedProperConvexFn_infConv hf hg h).2.2

/-- **Rockafellar, Corollary 9.2.2**, attainment: the infimum in
`(f₁ □ f₂)(x) = inf_y {f₁(x - y) + f₂(y)}` is attained for each `x`.

Specialises `exists_add_eq_of_infConv_le`; the epigraph identity `epi (f □ g) = epi f + epi g`
*is* the attainment statement. -/
theorem corollary_9_2_2_attained {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : ∀ z : Rn n, z ≠ 0 → 0 < recessionFn f z + recessionFn g (-z)) {x : Rn n} {μ : ℝ}
    (hμ : infConv f g x ≤ (μ : EReal)) :
    ∃ (y : Rn n) (ν ρ : ℝ), y + (x - y) = x ∧ ν + ρ = μ ∧ f y ≤ (ν : EReal) ∧
      g (x - y) ≤ (ρ : EReal) :=
  exists_add_eq_of_infConv_le hf hg h hμ

/-! ### Theorem 9.3: sums of functions -/

/-- **Rockafellar, Theorem 9.3** for `m = 2`, closed case. If `f₁` and `f₂` are closed proper
convex and `f₁ + f₂` is not identically `+∞`, then `f₁ + f₂` is a closed proper convex function.

Specialises `ClosedProperConvexFn.add`. -/
theorem theorem_9_3_closed {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) (hne : (dom (f + g)).Nonempty) :
    ClosedProperConvexFn (f + g) :=
  hf.add hg hne

/-- **Rockafellar, Theorem 9.3** for `m = 2`, recession formula:
`(f₁ + f₂)0⁺ = f₁0⁺ + f₂0⁺`.

Specialises `recessionFn_add`, which is the book's own proof: Theorem 8.5's difference quotients
based at a common point of the two effective domains. -/
theorem theorem_9_3_recession {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) (hne : (dom (f + g)).Nonempty) :
    recessionFn (f + g) = recessionFn f + recessionFn g :=
  recessionFn_add hf hg hne

/-- **Rockafellar, Theorem 9.3** for `m = 2`, second half: if the `fᵢ` are not all closed but
their effective domains have a common relative interior point, then
`cl (f₁ + f₂) = cl f₁ + cl f₂`.

Specialises `clFn_add`. -/
theorem theorem_9_3_closure {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    (hg : ConvexFn g) (hpg : Proper g) {x : Rn n} (hxf : x ∈ ri (dom f)) (hxg : x ∈ ri (dom g)) :
    clFn (f + g) = clFn f + clFn g :=
  clFn_add hf hpf hg hpg hxf hxg

/-! ### Theorem 9.4: pointwise suprema -/

/-- **Rockafellar, Theorem 9.4**, closed case: a pointwise supremum of closed convex functions is
closed, because its epigraph is the intersection of their epigraphs.

Specialises `isClosed_epi_iSup`, which needs neither convexity nor finite dimension. -/
theorem theorem_9_4_closed {ι : Type*} {f : ι → Rn n → EReal} (hc : ∀ i, IsClosed (epi (f i))) :
    IsClosed (epi fun z => ⨆ i, f i z) :=
  isClosed_epi_iSup hc

/-- **Rockafellar, Theorem 9.4**, properness. `f = sup {fᵢ | i ∈ I}` is proper as soon as every
`fᵢ` is proper and `f` is finite somewhere.

"Finite somewhere" is spelled out as both `≠ ⊥` and `≠ ⊤` at one point; the `≠ ⊥` half is what
forces the book's index set `I` to be non-empty, since a supremum over an empty family is `-∞`
everywhere. -/
theorem theorem_9_4_proper {ι : Type*} {f : ι → Rn n → EReal} (hp : ∀ i, Proper (f i))
    {x : Rn n} (hbot : (⨆ i, f i x) ≠ ⊥) (htop : (⨆ i, f i x) ≠ ⊤) :
    Proper (fun z => ⨆ i, f i z) := by
  have hι : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hbot (by simp)
  obtain ⟨i₀⟩ := hι
  refine ⟨⟨x, mem_dom.2 (lt_top_iff_ne_top.2 htop)⟩, fun z => ?_⟩
  exact fun hz => (hp i₀).ne_bot z (le_bot_iff.1 (hz ▸ le_iSup (fun i => f i z) i₀))

/-- **Rockafellar, Theorem 9.4**, recession formula: `f0⁺ = sup {fᵢ0⁺ | i ∈ I}`.

Specialises `recessionFn_iSup`, which is Corollary 8.3.3 read through `epi_recessionFn`. -/
theorem theorem_9_4_recession {ι : Type*} {f : ι → Rn n → EReal} (hconv : ∀ i, ConvexFn (f i))
    (hc : ∀ i, IsClosed (epi (f i))) (hne : (epi fun z => ⨆ i, f i z).Nonempty) :
    recessionFn (fun z => ⨆ i, f i z) = fun z => ⨆ i, recessionFn (f i) z :=
  recessionFn_iSup hconv hc hne

/-- **Rockafellar, Theorem 9.4**, second half: if the `fᵢ` are not all closed but some `x̄` lies in
every `ri (dom fᵢ)` and `f x̄` is finite, then `cl f = sup {cl fᵢ | i ∈ I}`.

Specialises `lscHull_iSup`; for proper convex functions `cl` and `lscHull` agree
(`ConvexFn.clFn_eq_lscHull`). -/
theorem theorem_9_4_closure {ι : Type*} {f : ι → Rn n → EReal} (hconv : ∀ i, ConvexFn (f i))
    {x : Rn n} (hx : ∀ i, x ∈ ri (dom (f i))) (hfin : (⨆ i, f i x) < ⊤) :
    lscHull (fun z => ⨆ i, f i z) = fun z => ⨆ i, lscHull (f i) z :=
  lscHull_iSup hconv hx hfin

/-! ### Theorem 9.5: composition with a linear transformation -/

/-- **Rockafellar, Theorem 9.5**, closed case: if `g` is closed then so is `gA`.

Specialises `isClosed_epi_compLin`: `epi (gA)` is the preimage of `epi g` under the continuous
linear map `(x, μ) ↦ (Ax, μ)`, so no relative interior hypothesis is needed. -/
theorem theorem_9_5_closed {g : Rn m → EReal} (hc : IsClosed (epi g)) (A : Rn n →ₗ[ℝ] Rn m) :
    IsClosed (epi (compLin g A)) :=
  isClosed_epi_compLin hc A

/-- **Rockafellar, Theorem 9.5**, recession formula: `(gA)0⁺ = (g0⁺)A`.

Specialises `recessionFn_compLin`, which is Corollary 8.3.4 read through `epi_recessionFn`. -/
theorem theorem_9_5_recession {g : Rn m → EReal} (hg : ConvexFn g) (hc : IsClosed (epi g))
    (A : Rn n →ₗ[ℝ] Rn m) (hne : (dom (compLin g A)).Nonempty) :
    recessionFn (compLin g A) = compLin (recessionFn g) A :=
  recessionFn_compLin hg hc A hne

/-- **Rockafellar, Theorem 9.5**, second half: if `g` is not closed but `Ax ∈ ri (dom g)` for some
`x`, then `cl (gA) = (cl g)A`.

Specialises `clFn_compLin`, which is Theorem 6.7 applied to `epi g`. -/
theorem theorem_9_5_closure {g : Rn m → EReal} (hg : ConvexFn g) (hp : Proper g)
    (A : Rn n →ₗ[ℝ] Rn m) {x : Rn n} (hx : A x ∈ ri (dom g)) :
    clFn (compLin g A) = compLin (clFn g) A :=
  clFn_compLin hg hp A hx

/-! ### Theorem 9.6: the convex cone generated by a set -/

/-- **Rockafellar, Theorem 9.6.** Let `C` be a non-empty closed convex set not containing the
origin and let `K` be the convex cone generated by `C`. Then `cl K = K ∪ 0⁺C`.

Specialises `closure_coe_hull_eq_union`. The backbone models "the convex cone generated by `C`" as
`PointedCone.hull ℝ C`. -/
theorem theorem_9_6 {C : Set (Rn n)} (hC : Convex ℝ C) (hCc : IsClosed C) (hne : C.Nonempty)
    (h0 : (0 : Rn n) ∉ C) :
    closure (PointedCone.hull ℝ C : Set (Rn n))
      = (PointedCone.hull ℝ C : Set (Rn n)) ∪ recessionCone C :=
  closure_coe_hull_eq_union hC hCc hne h0

/-- **Rockafellar, Theorem 9.6**, in the `λ ≥ 0⁺` form the book gives it:
`cl K = ⋃ {λC | λ > 0 or λ = 0⁺}`.

The union is indexed by `ExtCoeff.Pos`, and `ExtCoeff.smulSet` is what makes `λ = 0⁺` contribute
`0⁺C` rather than `{0}`. Specialises `closure_coe_hull`. -/
theorem theorem_9_6_iUnion {C : Set (Rn n)} (hC : Convex ℝ C) (hCc : IsClosed C)
    (hne : C.Nonempty) (h0 : (0 : Rn n) ∉ C) :
    closure (PointedCone.hull ℝ C : Set (Rn n))
      = ⋃ l : ExtCoeff, ⋃ _ : l.Pos, l.smulSet C := by
  rw [closure_coe_hull hC hCc hne h0]
  refine Set.ext fun y => ⟨?_, ?_⟩
  · rintro (⟨t, ht, hy⟩ | hy)
    · exact Set.mem_iUnion₂.2 ⟨ExtCoeff.ofReal t, ht, hy⟩
    · exact Set.mem_iUnion₂.2 ⟨ExtCoeff.zeroPlus, trivial, hy⟩
  · rintro hy
    obtain ⟨l, hl, hy⟩ := Set.mem_iUnion₂.1 hy
    cases l with
    | ofReal t => exact Or.inl ⟨t, hl, hy⟩
    | zeroPlus => exact Or.inr hy

/-- **Rockafellar, Corollary 9.6.1.** If `C` is a non-empty closed *bounded* convex set not
containing the origin, the convex cone generated by `C` is closed.

Specialises `isClosed_coe_hull_of_isBounded`. -/
theorem corollary_9_6_1 {C : Set (Rn n)} (hC : Convex ℝ C) (hCc : IsClosed C) (hne : C.Nonempty)
    (h0 : (0 : Rn n) ∉ C) (hb : Bornology.IsBounded C) :
    IsClosed (PointedCone.hull ℝ C : Set (Rn n)) :=
  isClosed_coe_hull_of_isBounded hC hCc hne h0 hb

/-! ### Theorem 9.7: the positively homogeneous convex function generated by `f` -/

/-- **Rockafellar, Theorem 9.7.** For a closed proper convex `f` on `ℝⁿ` with `f 0 > 0`, the
positively homogeneous convex function `k` generated by `f` is proper.

Specialises `proper_posHomGen`; the backbone's `posHomGen` *is* §5's `k`. -/
theorem theorem_9_7_proper {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    (hc : IsClosed (epi f)) (h0 : 0 < f 0) :
    Proper (posHomGen f) :=
  proper_posHomGen hf hp hc h0

/-- **Rockafellar, Theorem 9.7**, the formula
`(cl k)(x) = inf {(fλ)(x) | λ > 0 or λ = 0⁺}`, in the `λ ≥ 0⁺` convention.

Specialises `lscHull_posHomGen`, which states the same infimum split into its `λ > 0` part and its
`λ = 0⁺` part; `ExtCoeff.smulFn` puts the two back under one index. -/
theorem theorem_9_7 {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) (hc : IsClosed (epi f))
    (h0 : 0 < f 0) :
    lscHull (posHomGen f) = ⨅ l : ExtCoeff, ⨅ _ : l.Pos, l.smulFn f := by
  rw [lscHull_posHomGen hf hp hc h0]
  refine le_antisymm (le_iInf₂ fun l hl => ?_) (le_inf ?_ ?_)
  · cases l with
    | ofReal t => exact inf_le_of_left_le (iInf₂_le t hl)
    | zeroPlus => exact inf_le_right
  · exact le_iInf₂ fun t ht => iInf₂_le (ExtCoeff.ofReal t) ht
  · exact iInf₂_le ExtCoeff.zeroPlus trivial

/-- **Rockafellar, Theorem 9.7**, attainment: the infimum
`inf {(fλ)(x) | λ > 0 or λ = 0⁺}` is attained for each `x`.

Specialises `exists_smulRight_le_of_lscHull_posHomGen_le`. Attainment is the assertion that the
right-hand side of Theorem 9.7 is a *union of epigraphs* rather than merely the epigraph of the
infimum, so it is stated at each real bound `μ`. -/
theorem theorem_9_7_attained {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    (hc : IsClosed (epi f)) (h0 : 0 < f 0) {x : Rn n} {μ : ℝ}
    (hμ : lscHull (posHomGen f) x ≤ (μ : EReal)) :
    ∃ l : ExtCoeff, l.Pos ∧ l.smulFn f x ≤ (μ : EReal) := by
  rcases exists_smulRight_le_of_lscHull_posHomGen_le hf hp hc h0 hμ with ⟨t, ht, hle⟩ | hle
  · exact ⟨ExtCoeff.ofReal t, ht, hle⟩
  · exact ⟨ExtCoeff.zeroPlus, trivial, hle⟩

/-- **Rockafellar, Theorem 9.7**, last sentence: if `0 ∈ dom f` then `k` is itself closed.

Specialises `lscHull_posHomGen_eq`. -/
theorem theorem_9_7_closed {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    (hc : IsClosed (epi f)) (h0 : 0 < f 0) (hdom : f 0 ≠ ⊤) :
    lscHull (posHomGen f) = posHomGen f :=
  lscHull_posHomGen_eq hf hp hc h0 hdom

/-- **Rockafellar, Theorem 9.7**, last sentence: if `0 ∈ dom f` then `λ = 0⁺` may be omitted from
the infimum — though the infimum then need not be attained.

Specialises `posHomGen_eq_iInf_smulRight`. -/
theorem theorem_9_7_iInf_pos {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    (hc : IsClosed (epi f)) (h0 : 0 < f 0) (hdom : f 0 ≠ ⊤) :
    posHomGen f = ⨅ t : ℝ, ⨅ _ : (0 : ℝ) < t, smulRight f t :=
  posHomGen_eq_iInf_smulRight hf hp hc h0 hdom

/-- **Rockafellar, Corollary 9.7.1.** For a closed convex set `C` containing `0`, the gauge
`γ(· | C)` is closed.

Specialises `closedFn_gaugeFn`. The backbone takes the *computed* formula
`γ(x | C) = inf {λ ≥ 0 | x ∈ λC}` as its definition of `gaugeFn`, where the book defines `γ` as
the positively homogeneous convex function generated by `δ(· | C) + 1`; the bridge between the two
is a recorded backbone gap (see `Section05.lean`). -/
theorem corollary_9_7_1_closed {C : Set (Rn n)} (hC : Convex ℝ C) (h0 : (0 : Rn n) ∈ C)
    (hcl : IsClosed C) :
    ClosedFn (gaugeFn C) :=
  closedFn_gaugeFn hC h0 hcl

/-- **Rockafellar, Corollary 9.7.1**, first formula: `{x | γ(x | C) ≤ λ} = λC` for `λ > 0`.

Specialises `setOf_gaugeFn_le_pos`. -/
theorem corollary_9_7_1_level {C : Set (Rn n)} (hC : Convex ℝ C) (h0 : (0 : Rn n) ∈ C)
    (hcl : IsClosed C) {c : ℝ} (hc : 0 < c) :
    {x : Rn n | gaugeFn C x ≤ (c : EReal)} = c • C :=
  setOf_gaugeFn_le_pos hC h0 hcl hc

/-- **Rockafellar, Corollary 9.7.1**, second formula: `{x | γ(x | C) = 0} = 0⁺C`.

The level sets of `γ` at every positive height are the sets `λC` (`setOf_gaugeFn_le_pos`), and
`0⁺C` is their intersection (`recessionCone_eq_iInter_smul`). -/
theorem corollary_9_7_1_zero {C : Set (Rn n)} (hC : Convex ℝ C) (h0 : (0 : Rn n) ∈ C)
    (hcl : IsClosed C) :
    {x : Rn n | gaugeFn C x = 0} = recessionCone C := by
  rw [recessionCone_eq_iInter_smul hC hcl h0]
  refine Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · refine Set.mem_iInter₂.2 fun c hc => ?_
    rw [← setOf_gaugeFn_le_pos hC h0 hcl hc]
    have hx' : gaugeFn C x = 0 := hx
    have hle : gaugeFn C x ≤ (c : EReal) := by
      rw [hx']
      exact_mod_cast hc.le
    exact hle
  · refine le_antisymm ?_ (gaugeFn_nonneg C x)
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    obtain ⟨d, hd0, hdc⟩ : ∃ d : ℝ, 0 < d ∧ (d : EReal) ≤ c := by
      obtain ⟨d, hd₁, hd₂⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hc
      exact ⟨d, by exact_mod_cast hd₁, hd₂.le⟩
    refine le_trans ?_ hdc
    have := Set.mem_iInter₂.1 hx d hd0
    rw [← setOf_gaugeFn_le_pos hC h0 hcl hd0] at this
    exact this

/-! ### Theorem 9.8: the convex hull of a union -/

/-- **The `λ ≥ 0⁺` convention, reduced to the backbone.** For non-empty closed convex `C₁, C₂`,
Rockafellar's `⋃ {λ₁C₁ + λ₂C₂ | λᵢ ≥ 0⁺, λ₁ + λ₂ = 1}` is exactly
`conv (C₁ ∪ C₂) + (0⁺C₁ + 0⁺C₂)`.

This is the one place where the convention has to be *earned* rather than unfolded, and it is what
makes Theorem 9.8 below a statement in the book's own terms. Both `λᵢ = 0⁺` is excluded by
`λ₁ + λ₂ = 1`; the mixed cases are the two summands `0⁺C₁ + C₂` and `C₁ + 0⁺C₂`, and the case with
both `λᵢ` real and positive absorbs the recession cones into `Cᵢ` because
`Cᵢ + 0⁺Cᵢ = Cᵢ`. -/
theorem iUnion_extCoeff_pair {C D : Set (Rn n)} (hC : Convex ℝ C) (hCne : C.Nonempty)
    (hD : Convex ℝ D) (hDne : D.Nonempty) :
    (⋃ p : ExtCoeff × ExtCoeff,
        ⋃ _ : p.1.Nonneg ∧ p.2.Nonneg ∧ p.1.toReal + p.2.toReal = 1,
          p.1.smulSet C + p.2.smulSet D)
      = convexHull ℝ (C ∪ D) + (recessionCone C + recessionCone D) := by
  have hjoin : convexHull ℝ (C ∪ D) = convexJoin ℝ C D := hC.convexHull_union hD hCne hDne
  have hCsub : C ⊆ convexHull ℝ (C ∪ D) := Set.subset_union_left.trans (subset_convexHull ℝ _)
  have hDsub : D ⊆ convexHull ℝ (C ∪ D) := Set.subset_union_right.trans (subset_convexHull ℝ _)
  have hzero : (0 : Rn n) ∈ recessionCone C + recessionCone D := by
    simpa using Set.add_mem_add (zero_mem_recessionCone C) (zero_mem_recessionCone D)
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨⟨l₁, l₂⟩, hp, hmem⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨h₁, h₂, hsum⟩ := hp
    obtain ⟨u, hu, v, hv, huv⟩ := hmem
    have huv' : u + v = x := huv
    cases l₁ with
    | ofReal a =>
      cases l₂ with
      | ofReal b =>
        obtain ⟨c, hc, hcu⟩ := hu
        obtain ⟨d, hd, hdv⟩ := hv
        have hcu' : a • c = u := hcu
        have hdv' : b • d = v := hdv
        have hxconv : x ∈ convexHull ℝ (C ∪ D) := by
          rw [hjoin]
          refine mem_convexJoin.2 ⟨c, hc, d, hd, ⟨a, b, h₁, h₂, hsum, ?_⟩⟩
          rw [hcu', hdv', huv']
        simpa using Set.add_mem_add hxconv hzero
      | zeroPlus =>
        obtain ⟨c, hc, hcu⟩ := hu
        have hcu' : a • c = u := hcu
        have ha : a = 1 := by simpa using hsum
        have hv' : v ∈ recessionCone C + recessionCone D := by
          simpa using Set.add_mem_add (zero_mem_recessionCone C) hv
        have hmem := Set.add_mem_add (hCsub hc) hv'
        have hcx : c + v = x := by rw [← huv', ← hcu', ha, one_smul]
        rwa [hcx] at hmem
    | zeroPlus =>
      cases l₂ with
      | ofReal b =>
        obtain ⟨d, hd, hdv⟩ := hv
        have hdv' : b • d = v := hdv
        have hb : b = 1 := by simpa using hsum
        have hu' : u ∈ recessionCone C + recessionCone D := by
          simpa using Set.add_mem_add hu (zero_mem_recessionCone D)
        have hmem := Set.add_mem_add (hDsub hd) hu'
        have hdx : d + u = x := by rw [← huv', ← hdv', hb, one_smul, add_comm]
        rwa [hdx] at hmem
      | zeroPlus => exact absurd hsum (by norm_num [ExtCoeff.toReal])
  · obtain ⟨c, hc, w, hw, hcw⟩ := hx
    obtain ⟨z₁, hz₁, z₂, hz₂, hz⟩ := hw
    have hcw' : c + w = x := hcw
    have hz' : z₁ + z₂ = w := hz
    rw [hjoin] at hc
    obtain ⟨u, hu, v, hv, hseg⟩ := mem_convexJoin.1 hc
    obtain ⟨a, b, ha, hb, hab, hc'⟩ := hseg
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · -- `a = 0`, hence `b = 1` and `c = v ∈ D`
      have hb1 : b = 1 := by rw [← hab, ← ha0]; ring
      have hcv : v = c := by rw [← hc', ← ha0, hb1, zero_smul, one_smul, zero_add]
      refine Set.mem_iUnion₂.2 ⟨(ExtCoeff.zeroPlus, ExtCoeff.ofReal b), ⟨trivial, hb, ?_⟩, ?_⟩
      · simp [ExtCoeff.toReal, hb1]
      · have hvD : v + z₂ ∈ D := add_mem_of_mem_recessionCone hz₂ hv
        have hmem := Set.add_mem_add (a := z₁) hz₁ (Set.smul_mem_smul_set (a := b) hvD)
        have hval : z₁ + b • (v + z₂) = x := by
          rw [hb1, one_smul, hcv, ← hcw', ← hz']
          abel
        rwa [hval] at hmem
    · rcases eq_or_lt_of_le hb with hb0 | hbpos
      · -- `b = 0`, hence `a = 1` and `c = u ∈ C`
        have ha1 : a = 1 := by rw [← hab, ← hb0]; ring
        have hcu : u = c := by rw [← hc', ← hb0, ha1, zero_smul, one_smul, add_zero]
        refine Set.mem_iUnion₂.2 ⟨(ExtCoeff.ofReal a, ExtCoeff.zeroPlus), ⟨ha, trivial, ?_⟩, ?_⟩
        · simp [ExtCoeff.toReal, ha1]
        · have huC : u + z₁ ∈ C := add_mem_of_mem_recessionCone hz₁ hu
          have hmem := Set.add_mem_add (Set.smul_mem_smul_set (a := a) huC) hz₂
          have hval : a • (u + z₁) + z₂ = x := by
            rw [ha1, one_smul, hcu, ← hcw', ← hz']
            abel
          rwa [hval] at hmem
      · -- both coefficients positive: the recession cones are absorbed into `C` and `D`
        refine Set.mem_iUnion₂.2 ⟨(ExtCoeff.ofReal a, ExtCoeff.ofReal b), ⟨ha, hb, hab⟩, ?_⟩
        have huC : u + a⁻¹ • z₁ ∈ C :=
          add_mem_of_mem_recessionCone (smul_mem_recessionCone (by positivity) hz₁) hu
        have hvD : v + b⁻¹ • z₂ ∈ D :=
          add_mem_of_mem_recessionCone (smul_mem_recessionCone (by positivity) hz₂) hv
        have hmem := Set.add_mem_add (Set.smul_mem_smul_set (a := a) huC)
          (Set.smul_mem_smul_set (a := b) hvD)
        have hval : a • (u + a⁻¹ • z₁) + b • (v + b⁻¹ • z₂) = x := by
          rw [smul_add, smul_add, smul_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt hapos),
            mul_inv_cancel₀ (ne_of_gt hbpos), one_smul, one_smul, ← hcw', ← hc', ← hz']
          abel
        rwa [hval] at hmem

/-- **Rockafellar, Theorem 9.8** for `m = 2`. Let `C₁, C₂` be non-empty closed convex sets in `ℝⁿ`
such that the only way a direction of recession of one can cancel a direction of recession of the
other is inside the two lineality spaces, and let `C = conv (C₁ ∪ C₂)`. Then

`cl C = ⋃ {λ₁C₁ + λ₂C₂ | λᵢ ≥ 0⁺, λ₁ + λ₂ = 1}`,

where `λᵢ ≥ 0⁺` means that `λᵢCᵢ` is taken to be `0⁺Cᵢ` rather than `{0}` when `λᵢ = 0`.

Specialises `closure_convexHull_union` through `iUnion_extCoeff_pair`. -/
theorem theorem_9_8 {C D : Set (Rn n)} (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hD : Convex ℝ D) (hDc : IsClosed D) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone C, ∀ w ∈ recessionCone D, z + w = 0 →
      z ∈ linealitySpace C ∧ w ∈ linealitySpace D) :
    closure (convexHull ℝ (C ∪ D))
      = ⋃ p : ExtCoeff × ExtCoeff,
          ⋃ _ : p.1.Nonneg ∧ p.2.Nonneg ∧ p.1.toReal + p.2.toReal = 1,
            p.1.smulSet C + p.2.smulSet D := by
  rw [iUnion_extCoeff_pair hC hCne hD hDne]
  exact closure_convexHull_union hC hCc hCne hD hDc hDne h

/-- **Rockafellar, Theorem 9.8**, second conclusion: `0⁺(cl C) = 0⁺C₁ + 0⁺C₂`.

Specialises `recessionCone_closure_convexHull_union`. -/
theorem theorem_9_8_recession {C D : Set (Rn n)} (hC : Convex ℝ C) (hCc : IsClosed C)
    (hCne : C.Nonempty) (hD : Convex ℝ D) (hDc : IsClosed D) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone C, ∀ w ∈ recessionCone D, z + w = 0 →
      z ∈ linealitySpace C ∧ w ∈ linealitySpace D) :
    recessionCone (closure (convexHull ℝ (C ∪ D))) = recessionCone C + recessionCone D :=
  recessionCone_closure_convexHull_union hC hCc hCne hD hDc hDne h

/-- **Rockafellar, Corollary 9.8.1** for `m = 2`. If `C₁, C₂` are non-empty closed convex sets with
the *same* recession cone `K`, then `C = conv (C₁ ∪ C₂)` is closed.

Specialises `isClosed_convexHull_union_of_recessionCone_eq`. -/
theorem corollary_9_8_1_isClosed {C D : Set (Rn n)} (hC : Convex ℝ C) (hCc : IsClosed C)
    (hCne : C.Nonempty) (hD : Convex ℝ D) (hDc : IsClosed D) (hDne : D.Nonempty)
    (heq : recessionCone C = recessionCone D) :
    IsClosed (convexHull ℝ (C ∪ D)) :=
  (isClosed_convexHull_union_of_recessionCone_eq hC hCc hCne hD hDc hDne heq).1

/-- **Rockafellar, Corollary 9.8.1**, second conclusion: `C` has `K` as its recession cone. -/
theorem corollary_9_8_1_recession {C D : Set (Rn n)} (hC : Convex ℝ C) (hCc : IsClosed C)
    (hCne : C.Nonempty) (hD : Convex ℝ D) (hDc : IsClosed D) (hDne : D.Nonempty)
    (heq : recessionCone C = recessionCone D) :
    recessionCone (convexHull ℝ (C ∪ D)) = recessionCone C :=
  (isClosed_convexHull_union_of_recessionCone_eq hC hCc hCne hD hDc hDne heq).2

/-- **Rockafellar, Corollary 9.8.2.** If `C₁, C₂` are closed bounded convex sets in `ℝⁿ`, then
`conv (C₁ ∪ C₂)` is closed and bounded.

The backbone route is not Theorem 9.8 but Corollary 17.2.1: in `ℝⁿ` closed and bounded is compact,
and `IsCompact.isCompact_convexHull` does the rest. Convexity of the `Cᵢ` is not needed, and
neither is non-emptiness — which is why the book's proof has to discard the empty `Cᵢ` by hand. -/
theorem corollary_9_8_2 {C D : Set (Rn n)} (hCc : IsClosed C) (hCb : Bornology.IsBounded C)
    (hDc : IsClosed D) (hDb : Bornology.IsBounded D) :
    IsClosed (convexHull ℝ (C ∪ D)) ∧ Bornology.IsBounded (convexHull ℝ (C ∪ D)) := by
  have hcpt : IsCompact (C ∪ D) :=
    (Metric.isCompact_iff_isClosed_bounded.2 ⟨hCc, hCb⟩).union
      (Metric.isCompact_iff_isClosed_bounded.2 ⟨hDc, hDb⟩)
  have h := IsCompact.isCompact_convexHull hcpt
  exact ⟨h.isClosed, h.isBounded⟩

/-- **Rockafellar, Corollary 9.8.3** for `m = 2`. If `f₁, f₂` are closed proper convex functions on
`ℝⁿ` all having the same recession function `k`, then `f = conv {f₁, f₂}` is closed and proper.

Specialises `closedProperConvexFn_convFn₂`. -/
theorem corollary_9_8_3 {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) (heq : recessionFn f = recessionFn g) :
    ClosedProperConvexFn (convFn₂ f g) :=
  (closedProperConvexFn_convFn₂ hf hg heq).2.1

/-- **Rockafellar, Corollary 9.8.3**, second conclusion: `f` has `k` as its recession function. -/
theorem corollary_9_8_3_recession {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) (heq : recessionFn f = recessionFn g) :
    recessionFn (convFn₂ f g) = recessionFn f :=
  (closedProperConvexFn_convFn₂ hf hg heq).2.2

/-- **Rockafellar, Corollary 9.8.3**, last sentence: in the formula for `f(x)` of Theorem 5.6 the
infimum is attained for each `x` by some convex combination.

Specialises `exists_combo_of_convFn₂_le`. Attainment is stated against a real upper bound, which is
the `EReal`-faithful reading of "the infimum is attained": the value `conv {f₁, f₂} x` itself may
be `+∞`, and then there is nothing to attain. -/
theorem corollary_9_8_3_attained {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) (heq : recessionFn f = recessionFn g) {x : Rn n} {μ : ℝ}
    (hμ : convFn₂ f g x ≤ (μ : EReal)) :
    ∃ (a b : ℝ) (u v : Rn n), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • u + b • v = x ∧
      (a : EReal) * f u + (b : EReal) * g v ≤ (μ : EReal) :=
  exists_combo_of_convFn₂_le hf hg heq hμ

end Rockafellar
