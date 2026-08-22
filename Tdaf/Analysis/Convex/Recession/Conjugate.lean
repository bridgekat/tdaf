/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Support
import Tdaf.Analysis.Convex.Recession.Function

/-!
# The recession function of a conjugate

Rockafellar's **Theorem 13.3**: `(f*) 0⁺ = δ*(· | dom f)`. The recession function of a conjugate is
the support function of the effective domain.

`Duality/Support.lean` deliberately leaves §13.3–§13.5 unstated — it cannot name `f 0⁺`, which
lives in `Recession/Function.lean`. This file is the join of those two, and it is where the §13
statements that need recession functions belong.

## Main results

* `recessionFn_conj_le_supportFn_dom` — the unconditional half.
* `recessionFn_conj` — **Theorem 13.3**.
* `constancySpace_conj` — the constancy space of `f*` is the annihilator of `dom f`. This is the
  form Theorems 9.2 and 16.3 consume: it turns "`f*` is constant along `z`" into "`z` annihilates
  `dom f`", which a relative-interior hypothesis can discharge.

## Design notes

**One direction is free, the other needs Theorem 12.2.** `(f*)0⁺ y ≤ ν` unfolds, through
`recessionFn_le_coe_iff` and `mk_mem_recessionCone_epi_iff`, to `f*(z + a • y) ≤ f* z + a ν` for
all `z` and `a ≥ 0`, and `δ*(y | dom f) ≤ ν` unfolds to `⟨x, y⟩ ≤ ν` for all `x ∈ dom f`. Bounding
the supremum that defines `f*` termwise gives `(f*)0⁺ ≤ δ*(· | dom f)` with no hypothesis at all.

The reverse needs a `z` at which `f*` is *finite*: only then can the resulting inequality
`⟨x, z⟩ + a⟨x, y⟩ - f x ≤ f* z + a ν` be pushed to `a → ∞` to give `⟨x, y⟩ ≤ ν`. That is why the
hypothesis is `Proper (conj B f)`, which `proper_conj` supplies for closed proper convex `f` — i.e.
exactly Theorem 12.2.

**The file is layer A.** Neither half needs a topology: properness of `f*` is taken as a
hypothesis rather than derived, so callers at layer C supply it from `proper_conj` and everyone
else can still use the statement.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §13 (Theorem 13.3).
-/

namespace Tdaf.ConvexAnalysis

section Thm133

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **Theorem 13.3**, the unconditional half: `(f*) 0⁺ ≤ δ*(· | dom f)`.

Bounding the supremum that defines `f*` termwise: off `dom f` the term is `⊥`, and on `dom f` the
bound `⟨x, y⟩ ≤ ν` moves `a⟨x, y⟩` past the supremum. -/
theorem recessionFn_conj_le_supportFn_dom (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    recessionFn (conj B f) ≤ supportFn B (dom f) := by
  intro y
  refine Tdaf.EReal.le_of_forall_coe_le fun ν hν => ?_
  rw [supportFn_le_coe_iff] at hν
  rw [recessionFn_le_coe_iff, mk_mem_recessionCone_epi_iff]
  intro z a ha
  rw [conj_apply]
  refine iSup_le fun x => ?_
  by_cases hx : x ∈ dom f
  · have hBx : B x (z + a • y) = B x z + a * B x y := by rw [map_add, map_smul, smul_eq_mul]
    have hmul : a * B x y ≤ a * ν := mul_le_mul_of_nonneg_left (hν x hx) ha
    have hle : B x (z + a • y) ≤ B x z + a * ν := by rw [hBx]; linarith
    calc ((B x (z + a • y) : ℝ) : EReal) - f x
        ≤ ((B x z + a * ν : ℝ) : EReal) - f x :=
          _root_.EReal.sub_le_sub (_root_.EReal.coe_le_coe_iff.2 hle) le_rfl
      _ = (((B x z : ℝ) : EReal) - f x) + ((a * ν : ℝ) : EReal) :=
          Tdaf.EReal.coe_add_sub _ _ _
      _ ≤ conj B f z + ((a * ν : ℝ) : EReal) :=
          add_le_add (sub_le_conj B f x z) le_rfl
  · rw [mem_dom, not_lt, top_le_iff] at hx
    rw [hx, _root_.EReal.sub_top]
    exact bot_le

/-- **Theorem 13.3**, the half that needs Theorem 12.2: `δ*(· | dom f) ≤ (f*) 0⁺`.

`Proper (conj B f)` supplies a `z` at which `f*` is finite; Fenchel's inequality at `z + a • y`
then reads `⟨x, z⟩ + a⟨x, y⟩ - f x ≤ f* z + a ν`, and letting `a → ∞` forces `⟨x, y⟩ ≤ ν`. -/
theorem supportFn_dom_le_recessionFn_conj (hp : Proper f) (hc : Proper (conj B f)) :
    supportFn B (dom f) ≤ recessionFn (conj B f) := by
  intro y
  refine Tdaf.EReal.le_of_forall_coe_le fun ν hν => ?_
  rw [supportFn_le_coe_iff]
  intro x hx
  obtain ⟨z, hz⟩ := hc.dom_nonempty
  obtain ⟨c, hcz⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hc.ne_bot z) hz
  obtain ⟨r, hrx⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
  have hrec : ∀ a : ℝ, 0 ≤ a → conj B f (z + a • y) ≤ conj B f z + ((a * ν : ℝ) : EReal) :=
    fun a ha => mk_mem_recessionCone_epi_iff.1 (recessionFn_le_coe_iff.1 hν) z a ha
  have hbound : ∀ a : ℝ, 0 ≤ a → B x z + a * B x y - r ≤ c + a * ν := by
    intro a ha
    have hsub := sub_le_conj B f x (z + a • y)
    rw [hrx] at hsub
    have hle := hsub.trans (hrec a ha)
    rw [hcz, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at hle
    have hBx : B x (z + a • y) = B x z + a * B x y := by rw [map_add, map_smul, smul_eq_mul]
    rw [hBx] at hle
    linarith
  by_contra hcon
  push Not at hcon
  have hd : 0 < B x y - ν := by linarith
  set q : ℝ := (c + r - B x z) / (B x y - ν) with hq
  set a : ℝ := max (q + 1) 0 with ha
  have ha0 : 0 ≤ a := le_max_right _ _
  have haq : q < a := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hqmul : q * (B x y - ν) = c + r - B x z := by rw [hq, div_mul_cancel₀ _ hd.ne']
  have hb := hbound a ha0
  have hexp : a * (B x y - ν) = a * B x y - a * ν := by ring
  have hstep : a * (B x y - ν) ≤ q * (B x y - ν) := by rw [hqmul, hexp]; linarith
  exact absurd (le_of_mul_le_mul_right hstep hd) (not_le.2 haq)

/-- **Rockafellar, Theorem 13.3**: the recession function of a conjugate is the support function of
the effective domain, `(f*) 0⁺ = δ*(· | dom f)`. -/
theorem recessionFn_conj (hp : Proper f) (hc : Proper (conj B f)) :
    recessionFn (conj B f) = supportFn B (dom f) :=
  le_antisymm (recessionFn_conj_le_supportFn_dom B f) (supportFn_dom_le_recessionFn_conj hp hc)

/-- **The constancy space of a conjugate is the annihilator of the effective domain.**

This is what Theorem 9.2's hypothesis becomes when it is applied to `f*`: "`f*` is constant along
`y`" says exactly that `y` pairs to zero with every point of `dom f`. -/
theorem constancySpace_conj (hp : Proper f) (hc : Proper (conj B f)) :
    constancySpace (conj B f) = {y : F | ∀ x ∈ dom f, B x y = 0} := by
  ext y
  rw [mem_constancySpace, recessionFn_conj hp hc, Set.mem_ofPred_eq]
  have hzero : ((0 : ℝ) : EReal) = 0 := by norm_num
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [← hzero, supportFn_le_coe_iff] at h₁ h₂
    intro x hx
    have hneg := h₂ x hx
    rw [map_neg] at hneg
    linarith [h₁ x hx]
  · intro h
    constructor <;> rw [← hzero, supportFn_le_coe_iff] <;> intro x hx
    · exact le_of_eq (h x hx)
    · rw [map_neg, h x hx, neg_zero]

end Thm133

end Tdaf.ConvexAnalysis
