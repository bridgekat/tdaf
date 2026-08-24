/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Optimization.Moreau
import Tdaf.Analysis.Convex.Subgradient.Monotone

/-!
# Proximal mappings, and maximal monotonicity of the subdifferential

The attainment and uniqueness half of Rockafellar's **Theorem 31.5**, and the two corollaries it
carries: **Corollary 31.5.1** (the graph of `∂f` is homeomorphic to the space under
`(x, x*) ↦ x + x*`) and **Corollary 31.5.2** (`∂f` is a *maximal monotone* mapping).

`Optimization/Moreau.lean` proves the identity `(f □ w) + (f* □ w) = w` in an arbitrary real
Hilbert space. What is added here is that the infimum defining `(f □ w) z` is *attained at exactly
one point*, Rockafellar's `prox (z | f)`, and that the minimiser is characterised by
`z - x ∈ ∂f x`.

## Main definitions

* `moreauObj f z` — Rockafellar's objective `x ↦ f x + w (z - x)`, whose infimum is `(f □ w) z`.
* `prox f z` — the **proximal point**: the unique minimiser of `moreauObj f z`, or `0` when there
  is none.

## Main results

* `subgradient_quadFn_sub` — `∂(w (z - ·)) x = {x - z}`, the one computation the sum rule needs.
* `recessionFn_quadFn_sub` — `w (z - ·)` recedes in no direction but `0`; this is what makes
  Theorem 27.2 applicable.
* `argmin_moreauObj_nonempty` — **Theorem 31.5**, attainment: the infimum is attained.
* `mem_argmin_moreauObj_iff` — **Theorem 31.5**, the characterisation: `x` minimises
  `f + w (z - ·)` iff `z - x ∈ ∂f x`. This is the statement Corollary 31.5.1 is about.
* `eq_of_sub_mem_subgradient` — **Theorem 31.5**, uniqueness, with
  `existsUnique_sub_mem_subgradient` for the two clauses together.
* `argmin_moreauObj_eq_singleton`, `infConv_quadFn_eq_moreauObj_prox` — the infimum in Moreau's
  identity is attained at `prox f z` and nowhere else.
* `prox_add_prox_conj` — **Theorem 31.5**: `z = prox (z | f) + prox (z | f*)`.
* `lipschitzWith_prox` — `prox` is nonexpansive, the analytic content of Corollary 31.5.1.
* `subgradientRelHomeomorph` — **Corollary 31.5.1**: `(x, x*) ↦ x + x*` is a homeomorphism of the
  graph of `∂f` onto `E`.
* `isMaximalMonotoneRel_subgradientRel` — **Corollary 31.5.2**: `∂f` is maximal monotone.

## Design notes

**Finite dimensions, because attainment is Theorem 27.2.** `Optimization/Minimum.lean` proves
Theorem 27.2 — a closed proper convex function with no direction of recession attains its infimum —
in a finite-dimensional space, and that is what `argmin_moreauObj_nonempty` uses. Moreau's identity
itself (`Optimization/Moreau.lean`) needs no such hypothesis; only this file does. Everything the
statements say is Rockafellar's, who works in `Rⁿ` throughout §31.

**Attainment goes through the recession function, not through a growth estimate.** Theorem 9.3
(`recessionFn_add`) splits the recession function of `f + w (z - ·)` as the sum of the two, and
`(w (z - ·))0⁺ y = +∞` for `y ≠ 0` by a one-line test of the recession inequality at the single
point `z`. Since `f0⁺` never takes `-∞` (`recessionFn_ne_bot`), the sum is `+∞` off the origin, so
the recession cone is `{0}` and Theorem 27.2 applies.

**Uniqueness is monotonicity of `∂f`, not strict convexity of `w`.** If `z - x₁ ∈ ∂f x₁` and
`z - x₂ ∈ ∂f x₂` then monotonicity (Theorem 24.8) gives `0 ≤ ⟨x₁ - x₂, -(x₁ - x₂)⟩`, i.e.
`|x₁ - x₂|² ≤ 0`. The same two lines with `z₁ ≠ z₂` give `|prox z₁ - prox z₂| ≤ |z₁ - z₂|`, which
is Rockafellar's proof of the nonexpansiveness Corollary 31.5.1 rests on, so uniqueness and
continuity are one argument used twice.

**`prox` is total.** It is a `Classical` choice from the minimum set, with `0` as the value where
that set is empty; every theorem about it carries `ClosedProperConvexFn f`, which is exactly what
makes the set a singleton.

## What is not here

**The gradient formulas** `x = ∇(f* □ w) z` and `x* = ∇(f □ w) z` of Theorem 31.5. They need
Theorem 26.3 — a finite convex function is differentiable at `x` exactly when `∂f x` is a
singleton — applied to the two Moreau envelopes, which is `Subgradient/Differentiability.lean`
material rather than §31 material.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §31 (Theorem 31.5,
  Corollary 31.5.1, Corollary 31.5.2).
-/

open RealInnerProductSpace

namespace Tdaf.ConvexAnalysis

/-! ### The Moreau objective and the subdifferential of the quadratic -/

section Objective

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → EReal}

/-- **Rockafellar's objective in Theorem 31.5**: `x ↦ f x + w (z - x)`, whose infimum over `x` is
the Moreau envelope `(f □ w) z`. -/
noncomputable def moreauObj (f : E → EReal) (z : E) : E → EReal :=
  f + fun x => quadFn E (z - x)

omit [InnerProductSpace ℝ E] in
theorem moreauObj_def (f : E → EReal) (z : E) :
    moreauObj f z = f + fun x => quadFn E (z - x) := rfl

omit [InnerProductSpace ℝ E] in
@[simp] theorem moreauObj_apply (f : E → EReal) (z x : E) :
    moreauObj f z x = f x + quadFn E (z - x) := rfl

/-- `x - z` is a subgradient of `u ↦ w (z - u)` at `x`; the defect in the inequality is
`½|u - x|²`. -/
theorem sub_mem_subgradient_quadFn_sub (z x : E) :
    x - z ∈ subgradient (innerₗ E) (fun u => quadFn E (z - u)) x := by
  intro u
  simp only [innerₗ_apply_apply, quadFn_apply, ← _root_.EReal.coe_add,
    _root_.EReal.coe_le_coe_iff]
  have hexp := norm_sub_sq_real (z - x) (u - x)
  have hinner : ⟪u - x, x - z⟫ = -⟪z - x, u - x⟫ := by
    rw [show x - z = -(z - x) by abel, inner_neg_right, real_inner_comm]
  rw [show z - u = (z - x) - (u - x) by abel]
  nlinarith [sq_nonneg ‖u - x‖]

/-- **The subdifferential of the translated quadratic is a singleton**: `∂(w (z - ·)) x = {x - z}`.
Testing the subgradient inequality at the single point `y + z` forces `½|(z - x) + y|² ≤ 0`. -/
theorem subgradient_quadFn_sub (z x : E) :
    subgradient (innerₗ E) (fun u => quadFn E (z - u)) x = {x - z} := by
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · have h := hy (y + z)
    simp only [innerₗ_apply_apply, quadFn_apply, ← _root_.EReal.coe_add,
      _root_.EReal.coe_le_coe_iff] at h
    have hnorm : ‖z - (y + z)‖ = ‖y‖ := by rw [show z - (y + z) = -y by abel, norm_neg]
    have hyz : ⟪y + z - x, y⟫ = ‖y‖ ^ 2 + ⟪z - x, y⟫ := by
      rw [show y + z - x = y + (z - x) by abel, inner_add_left, real_inner_self_eq_norm_sq]
    rw [hnorm, hyz] at h
    have hexp := norm_add_sq_real (z - x) y
    have hsq : ‖(z - x) + y‖ ^ 2 ≤ 0 := by nlinarith
    have hz : ‖(z - x) + y‖ = 0 :=
      (pow_eq_zero_iff two_ne_zero).1 (le_antisymm hsq (sq_nonneg _))
    rw [Set.mem_singleton_iff, ← sub_eq_zero, show y - (x - z) = (z - x) + y by abel]
    exact norm_eq_zero.1 hz
  · rw [Set.singleton_subset_iff]
    exact sub_mem_subgradient_quadFn_sub z x

/-- `u ↦ w (z - u)` is closed proper convex: it is finite, convex and continuous. -/
theorem closedProperConvexFn_quadFn_sub (z : E) :
    ClosedProperConvexFn (fun x => quadFn E (z - x)) := by
  refine ⟨convexFn_quadFn_sub z, ?_, proper_quadFn_sub z⟩
  rw [closedFn_iff_lowerSemicontinuous fun _ => quadFn_ne_bot _]
  exact (continuous_quadFn_sub z).lowerSemicontinuous

/-- **The translated quadratic recedes in no direction**: `(w (z - ·))0⁺ y = +∞` for `y ≠ 0`.

Testing the recession inequality `q (x + a • y) ≤ q x + a ν` at `x = z`, where `q z = 0`, gives
`½ a²|y|² ≤ a ν` for every `a ≥ 0`, which fails for `a` large. -/
theorem recessionFn_quadFn_sub (z : E) {y : E} (hy : y ≠ 0) :
    recessionFn (fun x => quadFn E (z - x)) y = ⊤ := by
  by_contra hne
  obtain ⟨ν, hν⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
    (recessionFn_ne_bot (proper_quadFn_sub z) y) (lt_top_iff_ne_top.2 hne)
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hy2 : 0 < ‖y‖ ^ 2 := by positivity
  have ha1 : (1 : ℝ) ≤ max 1 (2 * (|ν| + 1) / ‖y‖ ^ 2) := le_max_left _ _
  have ha0 : (0 : ℝ) ≤ max 1 (2 * (|ν| + 1) / ‖y‖ ^ 2) := le_trans zero_le_one ha1
  have ha3 : 2 * (|ν| + 1) ≤ max 1 (2 * (|ν| + 1) / ‖y‖ ^ 2) * ‖y‖ ^ 2 := by
    rw [← div_le_iff₀ hy2]
    exact le_max_right _ _
  have hkey := recessionFn_le_coe_iff_forall.1 (le_of_eq hν) z _ ha0
  have hz : quadFn E (z - z) = ((0 : ℝ) : EReal) := by
    rw [sub_self, quadFn_apply, norm_zero]
    norm_num
  have hza : ∀ a : ℝ, quadFn E (z - (z + a • y)) = ((a ^ 2 * ‖y‖ ^ 2 / 2 : ℝ) : EReal) := by
    intro a
    rw [show z - (z + a • y) = -(a • y) by abel, quadFn_apply, norm_neg, norm_smul,
      Real.norm_eq_abs, _root_.EReal.coe_eq_coe_iff, mul_pow, sq_abs]
  simp only [hz, hza, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at hkey
  nlinarith [hkey, mul_le_mul_of_nonneg_left ha3 ha0,
    mul_le_mul_of_nonneg_left (le_abs_self ν) ha0]

/-- **Rockafellar, Theorem 31.5**, uniqueness: at most one `x` satisfies `z - x ∈ ∂f x`.

Monotonicity of `∂f` (Theorem 24.8) applied to the two pairs gives `0 ≤ ⟨x₁ - x₂, -(x₁ - x₂)⟩`. -/
theorem eq_of_sub_mem_subgradient (hp : Proper f) {z x₁ x₂ : E}
    (h₁ : z - x₁ ∈ subgradient (innerₗ E) f x₁) (h₂ : z - x₂ ∈ subgradient (innerₗ E) f x₂) :
    x₁ = x₂ := by
  have hmono := isMonotoneRel_subgradientRel (B := innerₗ E) hp (x₁, z - x₁) h₁ (x₂, z - x₂) h₂
  rw [innerₗ_apply_apply, show z - x₁ - (z - x₂) = -(x₁ - x₂) by abel, inner_neg_right,
    real_inner_self_eq_norm_sq] at hmono
  rw [← sub_eq_zero]
  exact norm_eq_zero.1
    ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm (by linarith) (sq_nonneg _)))

/-- **Rockafellar's proximal mapping** `prox (z | f)`: the point at which `x ↦ f x + w (z - x)`
attains its minimum. It is `0` where no minimum exists, which for a closed proper convex `f` never
happens (`argmin_moreauObj_nonempty`). -/
noncomputable def prox (f : E → EReal) (z : E) : E :=
  Classical.epsilon fun x => x ∈ argmin (moreauObj f z)

end Objective

/-! ### Theorem 31.5: attainment, uniqueness, and `prox` -/

section Attainment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- The constraint qualification of Theorem 31.5: `w (z - ·)` is finite and continuous, so the
conjugate of `f + w (z - ·)` splits. This is the hypothesis `moreau_add` runs on, in the form the
subgradient sum rule (Theorem 23.8) wants. -/
theorem isExactSum_quadFn_sub (hf : ClosedProperConvexFn f) (z : E) :
    IsExactSum (innerₗ E) f (fun x => quadFn E (z - x)) := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.dom_nonempty
  exact (IsExactSum.of_continuousAt (convexFn_quadFn_sub z) (proper_quadFn_sub z) hf.convex
    hf.proper (mem_dom.2 (lt_top_iff_ne_top.2 (quadFn_ne_top _))) hx₀
    (continuous_quadFn_sub z).continuousAt).symm

omit [FiniteDimensional ℝ E] in
/-- The Moreau objective of a closed proper convex function is closed proper convex
(Theorem 9.3). -/
theorem closedProperConvexFn_moreauObj (hf : ClosedProperConvexFn f) (z : E) :
    ClosedProperConvexFn (moreauObj f z) := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.dom_nonempty
  refine ClosedProperConvexFn.add hf (closedProperConvexFn_quadFn_sub z) ⟨x₀, ?_⟩
  exact mem_dom.2 (_root_.EReal.add_lt_top (mem_dom.1 hx₀).ne (quadFn_ne_top _))

omit [FiniteDimensional ℝ E] in
/-- **The Moreau objective has no direction of recession.** Theorem 9.3 splits its recession
function as `f0⁺ + (w (z - ·))0⁺`; the second term is `+∞` off the origin and the first never
takes `-∞`. -/
theorem recessionConeFn_moreauObj (hf : ClosedProperConvexFn f) (z : E) :
    recessionConeFn (moreauObj f z) = {0} := by
  have hg := closedProperConvexFn_moreauObj hf z
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · by_contra hy0
    rw [Set.mem_singleton_iff] at hy0
    rw [mem_recessionConeFn, moreauObj_def,
      congrFun (recessionFn_add hf (closedProperConvexFn_quadFn_sub z) hg.proper.dom_nonempty) y,
      Pi.add_apply, recessionFn_quadFn_sub z hy0,
      _root_.EReal.add_top_of_ne_bot (recessionFn_ne_bot hf.proper y)] at hy
    exact absurd hy (by simp)
  · rw [Set.singleton_subset_iff, mem_recessionConeFn]
    exact recessionFn_apply_zero_le _

/-- **Rockafellar, Theorem 31.5**, attainment: the infimum defining `(f □ w) z` is attained.

This is Theorem 27.2 applied to `f + w (z - ·)`, whose recession cone is `{0}`. -/
theorem argmin_moreauObj_nonempty (hf : ClosedProperConvexFn f) (z : E) :
    (argmin (moreauObj f z)).Nonempty :=
  argmin_nonempty_of_recessionConeFn_eq_zero (closedProperConvexFn_moreauObj hf z).convex
    (closedProperConvexFn_moreauObj hf z).closed (closedProperConvexFn_moreauObj hf z).proper
    (recessionConeFn_moreauObj hf z)

/-- **Rockafellar, Theorem 31.5**, the characterisation of the minimiser: `x` minimises
`f + w (z - ·)` exactly when `z - x` is a subgradient of `f` at `x`.

Fermat's rule `0 ∈ ∂(f + w (z - ·)) x`, the sum rule (Theorem 23.8) and
`subgradient_quadFn_sub`. -/
theorem mem_argmin_moreauObj_iff (hf : ClosedProperConvexFn f) (z x : E) :
    x ∈ argmin (moreauObj f z) ↔ z - x ∈ subgradient (innerₗ E) f x := by
  rw [mem_argmin_iff_zero_mem_subgradient (innerₗ E), moreauObj_def,
    (isExactSum_quadFn_sub hf z).subgradient_add x, subgradient_quadFn_sub]
  constructor
  · rintro ⟨y, hy, w, hw, hsum⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have hyz : y = z - x := by
      rw [← sub_eq_zero, show y - (z - x) = y + (x - z) by abel]
      exact hsum
    rwa [hyz] at hy
  · intro h
    exact ⟨z - x, h, x - z, rfl, by abel_nf⟩

/-- **Rockafellar, Theorem 31.5**: there is exactly one `x` with `z = x + x*` and `x* ∈ ∂f x`. -/
theorem existsUnique_sub_mem_subgradient (hf : ClosedProperConvexFn f) (z : E) :
    ∃! x : E, z - x ∈ subgradient (innerₗ E) f x := by
  obtain ⟨x, hx⟩ := argmin_moreauObj_nonempty hf z
  have hx' := (mem_argmin_moreauObj_iff hf z x).1 hx
  exact ⟨x, hx', fun x' hx'' => eq_of_sub_mem_subgradient hf.proper hx'' hx'⟩

/-- `prox f z` minimises the Moreau objective. -/
theorem prox_mem_argmin (hf : ClosedProperConvexFn f) (z : E) :
    prox f z ∈ argmin (moreauObj f z) := by
  exact Classical.epsilon_spec (argmin_moreauObj_nonempty hf z)

/-- **Rockafellar, Theorem 31.5**: `z - prox (z | f)` is a subgradient of `f` at `prox (z | f)`,
i.e. the splitting `z = x + x*` with `x* ∈ ∂f x` exists. -/
theorem sub_prox_mem_subgradient (hf : ClosedProperConvexFn f) (z : E) :
    z - prox f z ∈ subgradient (innerₗ E) f (prox f z) :=
  (mem_argmin_moreauObj_iff hf z _).1 (prox_mem_argmin hf z)

/-- The splitting of Theorem 31.5 determines `prox`. -/
theorem prox_eq_of_sub_mem_subgradient (hf : ClosedProperConvexFn f) {z x : E}
    (h : z - x ∈ subgradient (innerₗ E) f x) : prox f z = x :=
  eq_of_sub_mem_subgradient hf.proper (sub_prox_mem_subgradient hf z) h

/-- **Rockafellar, Theorem 31.5**, attainment and uniqueness in one statement. -/
theorem prox_eq_iff (hf : ClosedProperConvexFn f) (z x : E) :
    prox f z = x ↔ z - x ∈ subgradient (innerₗ E) f x :=
  ⟨fun h => h ▸ sub_prox_mem_subgradient hf z, prox_eq_of_sub_mem_subgradient hf⟩

/-- **Rockafellar, Theorem 31.5**: the minimum set of the Moreau objective is the single point
`prox (z | f)`. -/
theorem argmin_moreauObj_eq_singleton (hf : ClosedProperConvexFn f) (z : E) :
    argmin (moreauObj f z) = {prox f z} := by
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · rw [Set.mem_singleton_iff]
    exact (prox_eq_of_sub_mem_subgradient hf ((mem_argmin_moreauObj_iff hf z x).1 hx)).symm
  · rw [Set.singleton_subset_iff]
    exact prox_mem_argmin hf z

/-- **Rockafellar, Theorem 31.5**: the Moreau envelope is the value of the objective at the
proximal point. -/
theorem infConv_quadFn_eq_moreauObj_prox (hf : ClosedProperConvexFn f) (z : E) :
    infConv f (quadFn E) z = f (prox f z) + quadFn E (z - prox f z) := by
  rw [infConv_quadFn_apply hf.proper.ne_bot z]
  exact iInf_eq_of_mem_argmin (f := moreauObj f z) (prox_mem_argmin hf z)

/-- The conjugate of a closed proper convex function is closed proper convex (Theorem 12.2). -/
theorem closedProperConvexFn_conj (hf : ClosedProperConvexFn f) :
    ClosedProperConvexFn (conj (innerₗ E) f) := by
  have : IsContinuousPairing ((innerₗ E).flip) := by rw [flip_innerₗ]; infer_instance
  exact ⟨convexFn_conj _ _, closedFn_conj, proper_conj hf⟩

/-- **Rockafellar, Theorem 31.5**: `z` splits as `prox (z | f) + prox (z | f*)`.

Corollary 23.5.1 inverts `∂f` into `∂f*`, so the second half of the splitting `z = x + x*` is the
proximal point of `f*`. -/
theorem prox_add_prox_conj (hf : ClosedProperConvexFn f) (z : E) :
    prox f z + prox (conj (innerₗ E) f) z = z := by
  have hx : z - prox f z ∈ subgradient (innerₗ E) f (prox f z) := sub_prox_mem_subgradient hf z
  have hstar : z - (z - prox f z) ∈
      subgradient (innerₗ E) (conj (innerₗ E) f) (z - prox f z) := by
    rw [sub_sub_cancel]
    have h := (mem_subgradient_conj_iff_of_closedFn (B := innerₗ E) hf.convex hf.closed).2 hx
    rwa [flip_innerₗ] at h
  rw [prox_eq_of_sub_mem_subgradient (closedProperConvexFn_conj hf) hstar]
  abel

/-! ### Corollary 31.5.1: the graph of `∂f` is homeomorphic to the space -/

/-- **Rockafellar, Theorem 31.5**, nonexpansiveness of proximation: `prox` moves points no further
than their arguments.

Monotonicity of `∂f` gives `|x₁ - x₂|² ≤ ⟨x₁ - x₂, z₁ - z₂⟩`, and Cauchy–Schwarz finishes. -/
theorem dist_prox_prox_le (hf : ClosedProperConvexFn f) (z₁ z₂ : E) :
    dist (prox f z₁) (prox f z₂) ≤ dist z₁ z₂ := by
  have hmono := isMonotoneRel_subgradientRel (B := innerₗ E) hf.proper
    (prox f z₁, z₁ - prox f z₁) (sub_prox_mem_subgradient hf z₁)
    (prox f z₂, z₂ - prox f z₂) (sub_prox_mem_subgradient hf z₂)
  rw [innerₗ_apply_apply,
    show z₁ - prox f z₁ - (z₂ - prox f z₂)
      = (z₁ - z₂) - (prox f z₁ - prox f z₂) by abel,
    inner_sub_right, real_inner_self_eq_norm_sq] at hmono
  have hcs : ⟪prox f z₁ - prox f z₂, z₁ - z₂⟫ ≤ ‖prox f z₁ - prox f z₂‖ * ‖z₁ - z₂‖ :=
    real_inner_le_norm _ _
  rw [dist_eq_norm, dist_eq_norm]
  rcases eq_or_lt_of_le (norm_nonneg (prox f z₁ - prox f z₂)) with h0 | h0
  · rw [← h0]
    exact norm_nonneg _
  · refine le_of_mul_le_mul_left ?_ h0
    nlinarith

/-- `prox` is nonexpansive, hence continuous. -/
theorem lipschitzWith_prox (hf : ClosedProperConvexFn f) : LipschitzWith 1 (prox f) :=
  LipschitzWith.of_dist_le_mul fun z₁ z₂ => by
    simpa using dist_prox_prox_le hf z₁ z₂

theorem continuous_prox (hf : ClosedProperConvexFn f) : Continuous (prox f) :=
  (lipschitzWith_prox hf).continuous

/-- **Rockafellar, Corollary 31.5.1**: `(x, x*) ↦ x + x*` is a homeomorphism of the graph of `∂f`
onto `E`.

It is one-to-one and onto by Theorem 31.5 (`existsUnique_sub_mem_subgradient`), continuous because
addition is, and its inverse `z ↦ (prox (z | f), z - prox (z | f))` is continuous because `prox` is
nonexpansive. -/
noncomputable def subgradientRelHomeomorph (hf : ClosedProperConvexFn f) :
    ↥(subgradientRel (innerₗ E) f) ≃ₜ E where
  toFun p := p.1.1 + p.1.2
  invFun z := ⟨(prox f z, z - prox f z), sub_prox_mem_subgradient hf z⟩
  left_inv := by
    rintro ⟨⟨x, y⟩, hp⟩
    have hpx : prox f (x + y) = x :=
      prox_eq_of_sub_mem_subgradient hf (by rwa [show x + y - x = y by abel])
    refine Subtype.ext ?_
    simp only [hpx, Prod.mk.injEq, true_and]
    abel
  right_inv z := by
    simp only
    abel
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).add (continuous_snd.comp continuous_subtype_val)
  continuous_invFun :=
    Continuous.subtype_mk
      ((continuous_prox hf).prodMk (continuous_id.sub (continuous_prox hf))) _

@[simp] theorem subgradientRelHomeomorph_apply (hf : ClosedProperConvexFn f)
    (p : ↥(subgradientRel (innerₗ E) f)) : subgradientRelHomeomorph hf p = p.1.1 + p.1.2 := rfl

@[simp] theorem subgradientRelHomeomorph_symm_apply (hf : ClosedProperConvexFn f) (z : E) :
    (subgradientRelHomeomorph hf).symm z
      = ⟨(prox f z, z - prox f z), sub_prox_mem_subgradient hf z⟩ := rfl

/-! ### Corollary 31.5.2: `∂f` is maximal monotone -/

/-- **Rockafellar, Corollary 31.5.2**: the subdifferential of a closed proper convex function is a
*maximal monotone* mapping.

Given `(y, y*)` monotonically related to the whole graph, Theorem 31.5 produces `(x, x*)` in the
graph with `x + x* = y + y*`; then `y - x = -(y* - x*)`, so the monotonicity inequality reads
`0 ≤ -|y - x|²` and `(y, y*) = (x, x*)`.

This is the *monotone* maximality of §31, not the *cyclically* monotone maximality of Theorem 24.9
(`isMaximalCyclicallyMonotone_subgradientRel`); neither statement implies the other. -/
theorem isMaximalMonotoneRel_subgradientRel (hf : ClosedProperConvexFn f) :
    IsMaximalMonotoneRel (innerₗ E) (subgradientRel (innerₗ E) f) := by
  refine ⟨isMonotoneRel_subgradientRel hf.proper, fun σ hσ hsub q hq => ?_⟩
  have hmem : (prox f (q.1 + q.2), q.1 + q.2 - prox f (q.1 + q.2))
      ∈ subgradientRel (innerₗ E) f := sub_prox_mem_subgradient hf (q.1 + q.2)
  have hmono := hσ q hq _ (hsub hmem)
  rw [innerₗ_apply_apply,
    show q.2 - (q.1 + q.2 - prox f (q.1 + q.2)) = -(q.1 - prox f (q.1 + q.2)) by abel,
    inner_neg_right, real_inner_self_eq_norm_sq] at hmono
  have hq1 : q.1 = prox f (q.1 + q.2) := by
    rw [← sub_eq_zero]
    exact norm_eq_zero.1
      ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm (by linarith) (sq_nonneg _)))
  have hq2 : q.2 = q.1 + q.2 - prox f (q.1 + q.2) := by rw [← hq1]; abel
  rw [show q = (prox f (q.1 + q.2), q.1 + q.2 - prox f (q.1 + q.2)) from Prod.ext hq1 hq2]
  exact hmem

end Attainment

end Tdaf.ConvexAnalysis
