/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Ops
import Tdaf.Analysis.Convex.Optimization.Prox
import Tdaf.Analysis.Convex.Subgradient.LegendreType

/-!
# The gradient formulas of Moreau's theorem

For `f` closed proper convex on a finite-dimensional inner product space and `w z = ½‖z‖²`, the
Moreau envelope `f □ w` is finite everywhere and differentiable everywhere, with

`∇(f □ w) z = z - prox (z | f)`,  `∇(f* □ w) z = prox (z | f)`.

So the two halves of Moreau's splitting `z = prox (z | f) + prox (z | f*)` are the gradients of the
two envelopes; this is the last clause of **Theorem 31.5**. The splitting itself is in
`Optimization/Prox.lean`; what is added here is that `∂(f □ w) z` is a single point, which the
converse half of Theorem 25.1 upgrades to a gradient.

## Main results

* `subgradient_infConv_quadFn` — `∂(f □ w) z = {prox (z | f*)}`.
* `hasGradientAt_infConv_quadFn`, `hasGradientAt_infConv_conj_quadFn`,
  `gradient_infConv_quadFn`, `gradient_infConv_conj_quadFn` — **Theorem 31.5**, the gradient
  formulas, in `HasGradientAt` form and in terms of Mathlib's `gradient`.
* `closedProperConvexFn_infConv_quadFn` — the Moreau envelope is finite everywhere, hence closed
  proper convex.
* `conj_infConv_quadFn` — `(f □ w)* = f* + w`, Theorem 16.4 with `w* = w`.

## Implementation notes

No relative-interior or exactness hypothesis is needed: Theorem 16.4 is used in its unconditional
direction, and the constraint qualification for Theorem 23.8 is supplied by `w` being finite and
continuous.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §31.
-/

namespace Tdaf.ConvexAnalysis

open scoped Pointwise RealInnerProductSpace

section MoreauGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-! ### The Moreau envelope is closed proper convex -/

/-- The Moreau envelope is finite everywhere. -/
theorem dom_infConv_quadFn (hf : ClosedProperConvexFn f) :
    dom (infConv f (quadFn (innerₗ E))) = Set.univ :=
  Set.eq_univ_of_forall fun z => mem_dom.2 (lt_top_iff_ne_top.2 (infConv_quadFn_ne_top hf z))

/-- Finite everywhere and convex, so closed (Corollary 7.4.2). -/
theorem closedProperConvexFn_infConv_quadFn (hf : ClosedProperConvexFn f) :
    ClosedProperConvexFn (infConv f (quadFn (innerₗ E))) := by
  have hc : ConvexFn (infConv f (quadFn (innerₗ E))) := convexFn_infConv hf.convex convexFn_quadFn
  have hp : Proper (infConv f (quadFn (innerₗ E))) :=
    ⟨⟨0, mem_dom.2 (lt_top_iff_ne_top.2 (infConv_quadFn_ne_top hf 0))⟩,
      fun z => infConv_quadFn_ne_bot hf z⟩
  exact ⟨hc, closedFn_of_dom_eq_univ hc hp (dom_infConv_quadFn hf), hp⟩

omit [FiniteDimensional ℝ E] in
/-- **Theorem 16.4** for the Moreau envelope: `(f □ w)* = f* + w`, since `w* = w`. -/
theorem conj_infConv_quadFn (f : E → EReal) :
    conj (innerₗ E) (infConv f (quadFn (innerₗ E))) = conj (innerₗ E) f + quadFn (innerₗ E) := by
  rw [conj_infConv]
  congr 1
  funext y
  exact conj_quadFn y

/-! ### Theorem 31.5, the gradient formulas -/

/-- **The subdifferential of a Moreau envelope is a single point**: `∂(f □ w) z = {prox (z | f*)}`.
Corollary 23.5.1 turns `y ∈ ∂(f □ w) z` into `z ∈ ∂(f* + w) y`, Theorem 23.8 splits that as
`∂f* y + {y}`, and what is left, `z - y ∈ ∂f* y`, characterises `prox (z | f*)`. -/
theorem subgradient_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    subgradient (innerₗ E) (infConv f (quadFn (innerₗ E))) z
      = {prox (innerₗ E) (conj (innerₗ E) f) z} := by
  have hg := closedProperConvexFn_infConv_quadFn hf
  have hcf := closedProperConvexFn_conj (B := innerₗ E) hf
  ext y
  rw [Set.mem_singleton_iff, ← mem_subgradient_conj_innerL_iff hg.convex hg.closed z y,
    conj_infConv_quadFn, (isExactSum_quadFn hcf).subgradient_add, subgradient_quadFn]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [Set.mem_singleton_iff] at hb
    rw [hb] at hab
    have hab' : a + y = z := hab
    refine ((prox_eq_iff hcf z y).2 ?_).symm
    have hza : z - y = a := by rw [← hab']; abel
    rw [hza]
    exact ha
  · intro hy
    exact ⟨z - y, (prox_eq_iff hcf z y).1 hy.symm, y, rfl, by change z - y + y = z; abel⟩

/-- The two proximal points of Theorem 31.5 add up to `z`, written as a formula for the second. -/
theorem prox_conj_eq (hf : ClosedProperConvexFn f) (z : E) :
    prox (innerₗ E) (conj (innerₗ E) f) z = z - prox (innerₗ E) f z :=
  eq_sub_of_add_eq (by rw [add_comm]; exact prox_add_prox_conj hf z)

/-- **Theorem 31.5**: `x* = ∇(f □ w) z`. The subdifferential is a single point, which Theorem 25.1
upgrades to a gradient. -/
theorem hasGradientAt_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    HasGradientAt (infConv f (quadFn (innerₗ E)))
      (InnerProductSpace.toDual ℝ E (prox (innerₗ E) (conj (innerₗ E) f) z)) z :=
  hasGradientAt_toDual_of_subgradient_eq_singleton
    (closedProperConvexFn_infConv_quadFn hf).convex
    (closedProperConvexFn_infConv_quadFn hf).proper (subgradient_infConv_quadFn hf z)

/-- **Theorem 31.5**: `x = ∇(f* □ w) z`. The previous statement applied to `f*`, using
`prox (z | f**) = z - prox (z | f*) = prox (z | f)`. -/
theorem hasGradientAt_infConv_conj_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    HasGradientAt (infConv (conj (innerₗ E) f) (quadFn (innerₗ E)))
      (InnerProductSpace.toDual ℝ E (prox (innerₗ E) f z)) z := by
  have hcf := closedProperConvexFn_conj (B := innerₗ E) hf
  have h := hasGradientAt_infConv_quadFn hcf z
  rwa [prox_conj_eq hcf z, prox_conj_eq hf z, sub_sub_cancel] at h

/-- **Theorem 31.5**: `∇(f □ w) z = z - prox (z | f)`. -/
theorem gradient_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    gradient (fun u => (infConv f (quadFn (innerₗ E)) u).toReal) z = z - prox (innerₗ E) f z := by
  rw [(hasGradientAt_infConv_quadFn hf z).gradient_toReal_eq,
    LinearIsometryEquiv.symm_apply_apply, prox_conj_eq hf z]

/-- **Theorem 31.5**: `∇(f* □ w) z = prox (z | f)`. -/
theorem gradient_infConv_conj_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    gradient (fun u => (infConv (conj (innerₗ E) f) (quadFn (innerₗ E)) u).toReal) z
      = prox (innerₗ E) f z := by
  rw [(hasGradientAt_infConv_conj_quadFn hf z).gradient_toReal_eq,
    LinearIsometryEquiv.symm_apply_apply]

/-- **Theorem 31.5**: the Moreau envelope is differentiable everywhere. -/
theorem differentiableAtFn_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    DifferentiableAtFn (infConv f (quadFn (innerₗ E))) z :=
  ⟨_, hasGradientAt_infConv_quadFn hf z⟩

end MoreauGradient

end Tdaf.ConvexAnalysis
