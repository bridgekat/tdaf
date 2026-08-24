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

The last clause of Rockafellar's **Theorem 31.5**: the two halves of the splitting `z = x + x*` are
the gradients of the two Moreau envelopes,

`x = ∇(f* □ w) z`,  `x* = ∇(f □ w) z`,   where `w z = ½‖z‖²`.

`Optimization/Prox.lean` has everything about the splitting itself — that it exists, that it is
unique, and that its two halves are `prox (z | f)` and `prox (z | f*)`. What was missing was the
step from "`∂(f □ w) z` is a single point" to "`f □ w` is differentiable at `z`", which is
Theorem 25.1's converse.

## Main results

* `subgradient_infConv_quadFn` — `∂(f □ w) z = {prox (z | f*)}`. This is the whole theorem:
  Corollary 23.5.1 turns `y ∈ ∂(f □ w) z` into `z ∈ ∂((f □ w)*) y`, Theorem 16.4 rewrites
  `(f □ w)*` as `f* + w`, Theorem 23.8 splits `∂(f* + w) y` as `∂f* y + {y}`, and what is left is
  `z - y ∈ ∂f* y` — the defining property of `prox (z | f*)`.
* `hasGradientAt_infConv_quadFn`, `hasGradientAt_infConv_conj_quadFn`,
  `gradient_infConv_quadFn`, `gradient_infConv_conj_quadFn` — **Theorem 31.5**, the gradient
  formulas, in subgradient form and in terms of Mathlib's `gradient`.
* `closedProperConvexFn_infConv_quadFn` — the Moreau envelope is finite everywhere, hence closed
  proper convex.
* `conj_infConv_quadFn` — `(f □ w)* = f* + w`, Theorem 16.4 with `w* = w`.

## Design notes

**No `ri` hypothesis and no exactness hypothesis is needed anywhere here.** Theorem 16.4 is used in
its *unconditional* direction (`conj_infConv`), and the constraint qualification for Theorem 23.8 is
supplied by `w` being finite and continuous — `isExactSum_quadFn`, which is `Prox.lean`'s
`isExactSum_quadFn_sub` at the translation `z = 0`.

**The dual formula costs one line**, because `f*` is again closed proper convex and
`prox (z | f*) = z - prox (z | f)`. Nothing has to be proved twice.

## What is not here

**`f □ w` is not shown to be continuously differentiable.** Theorem 25.5
(`continuousOn_fderiv_toReal`) gives that immediately from `subgradient_infConv_quadFn`, and
Corollary 31.5.1 (`lipschitzWith_prox`, in `Prox.lean`) already records the stronger statement that
the gradient is nonexpansive.
-/

namespace Tdaf.ConvexAnalysis

open scoped Pointwise RealInnerProductSpace

section MoreauGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-! ### The untranslated quadratic -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The quadratic translated to the origin is the quadratic: `w (0 - ·) = w`. -/
theorem quadFn_zero_sub : (fun u : E => quadFn E (0 - u)) = quadFn E := by
  funext u
  rw [zero_sub, quadFn_apply, quadFn_apply, norm_neg]

omit [FiniteDimensional ℝ E] in
theorem convexFn_quadFn : ConvexFn (quadFn E) := by
  rw [← quadFn_zero_sub]
  exact convexFn_quadFn_sub 0

omit [FiniteDimensional ℝ E] in
/-- `∂w x = {x}`: the quadratic is its own gradient mapping. -/
theorem subgradient_quadFn (x : E) : subgradient (innerₗ E) (quadFn E) x = {x} := by
  rw [← quadFn_zero_sub, subgradient_quadFn_sub, sub_zero]

/-- The constraint qualification of Theorem 23.8 for `f + w`: `w` is finite and continuous. -/
theorem isExactSum_quadFn (hf : ClosedProperConvexFn f) :
    IsExactSum (innerₗ E) f (quadFn E) := by
  have h := isExactSum_quadFn_sub hf 0
  rwa [quadFn_zero_sub] at h

/-! ### The Moreau envelope is closed proper convex -/

/-- The Moreau envelope is finite everywhere. -/
theorem dom_infConv_quadFn (hf : ClosedProperConvexFn f) :
    dom (infConv f (quadFn E)) = Set.univ :=
  Set.eq_univ_of_forall fun z => mem_dom.2 (lt_top_iff_ne_top.2 (infConv_quadFn_ne_top hf z))

/-- Being finite everywhere and convex, the Moreau envelope is closed (Corollary 7.4.2). -/
theorem closedProperConvexFn_infConv_quadFn (hf : ClosedProperConvexFn f) :
    ClosedProperConvexFn (infConv f (quadFn E)) := by
  have hc : ConvexFn (infConv f (quadFn E)) := convexFn_infConv hf.convex convexFn_quadFn
  have hp : Proper (infConv f (quadFn E)) :=
    ⟨⟨0, mem_dom.2 (lt_top_iff_ne_top.2 (infConv_quadFn_ne_top hf 0))⟩,
      fun z => infConv_quadFn_ne_bot hf z⟩
  exact ⟨hc, closedFn_of_dom_eq_univ hc hp (dom_infConv_quadFn hf), hp⟩

omit [FiniteDimensional ℝ E] in
/-- **Rockafellar, Theorem 16.4** for the Moreau envelope: `(f □ w)* = f* + w`, since `w* = w`. -/
theorem conj_infConv_quadFn (f : E → EReal) :
    conj (innerₗ E) (infConv f (quadFn E)) = conj (innerₗ E) f + quadFn E := by
  rw [conj_infConv]
  congr 1
  funext y
  exact conj_quadFn y

/-! ### Theorem 31.5, the gradient formulas -/

/-- **The subdifferential of a Moreau envelope is a single point**: `∂(f □ w) z = {prox (z | f*)}`.

Corollary 23.5.1 turns `y ∈ ∂(f □ w) z` into `z ∈ ∂((f □ w)*) y`; Theorem 16.4 rewrites the
conjugate as `f* + w`, and Theorem 23.8 splits its subdifferential as `∂f* y + {y}`. What is left,
`z - y ∈ ∂f* y`, is exactly the characterisation of the proximal point of `f*` at `z`. -/
theorem subgradient_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    subgradient (innerₗ E) (infConv f (quadFn E)) z = {prox (conj (innerₗ E) f) z} := by
  have hg := closedProperConvexFn_infConv_quadFn hf
  have hcf := closedProperConvexFn_conj hf
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
    prox (conj (innerₗ E) f) z = z - prox f z :=
  eq_sub_of_add_eq (by rw [add_comm]; exact prox_add_prox_conj hf z)

/-- **Rockafellar, Theorem 31.5**: `x* = ∇(f □ w) z`. The subdifferential is a single point, so
Theorem 25.1's converse upgrades it to a gradient. -/
theorem hasGradientAt_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    HasGradientAt (infConv f (quadFn E))
      (InnerProductSpace.toDual ℝ E (prox (conj (innerₗ E) f) z)) z :=
  hasGradientAt_toDual_of_subgradient_eq_singleton
    (closedProperConvexFn_infConv_quadFn hf).convex
    (closedProperConvexFn_infConv_quadFn hf).proper (subgradient_infConv_quadFn hf z)

/-- **Rockafellar, Theorem 31.5**: `x = ∇(f* □ w) z`. This is the previous statement for `f*`,
using `prox (z | f**) = z - prox (z | f*) = prox (z | f)`. -/
theorem hasGradientAt_infConv_conj_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    HasGradientAt (infConv (conj (innerₗ E) f) (quadFn E))
      (InnerProductSpace.toDual ℝ E (prox f z)) z := by
  have h := hasGradientAt_infConv_quadFn (closedProperConvexFn_conj hf) z
  rwa [prox_conj_eq (closedProperConvexFn_conj hf) z, prox_conj_eq hf z, sub_sub_cancel] at h

/-- **Rockafellar, Theorem 31.5**: `∇(f □ w) z = z - prox (z | f)`. -/
theorem gradient_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    gradient (fun u => (infConv f (quadFn E) u).toReal) z = z - prox f z := by
  rw [(hasGradientAt_infConv_quadFn hf z).gradient_toReal_eq,
    LinearIsometryEquiv.symm_apply_apply, prox_conj_eq hf z]

/-- **Rockafellar, Theorem 31.5**: `∇(f* □ w) z = prox (z | f)`. -/
theorem gradient_infConv_conj_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    gradient (fun u => (infConv (conj (innerₗ E) f) (quadFn E) u).toReal) z = prox f z := by
  rw [(hasGradientAt_infConv_conj_quadFn hf z).gradient_toReal_eq,
    LinearIsometryEquiv.symm_apply_apply]

/-- **Rockafellar, Theorem 31.5**: the two Moreau envelopes are differentiable everywhere. -/
theorem differentiableAtFn_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    DifferentiableAtFn (infConv f (quadFn E)) z :=
  ⟨_, hasGradientAt_infConv_quadFn hf z⟩

end MoreauGradient

end Tdaf.ConvexAnalysis
