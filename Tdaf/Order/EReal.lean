/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Data.EReal.Operations

/-!
# Auxiliary lemmas about `EReal`

Convex analysis over `EReal` needs a handful of order and arithmetic facts that Mathlib does not
provide directly. They are collected here so that they do not accumulate as ad hoc `have`s
throughout the library.

## Rockafellar's arithmetic conventions

Rockafellar (*Convex Analysis*, §4) fixes the conventions

* `α + ∞ = ∞` for `-∞ < α ≤ ∞`,
* `α - ∞ = -∞` for `-∞ ≤ α < ∞`,
* `0 · ∞ = 0`,
* `inf ∅ = +∞`, `sup ∅ = -∞`,

and leaves `∞ - ∞` *undefined*, avoiding it by properness hypotheses. Every one of these agrees
with the corresponding fact about `EReal` in Mathlib, so no bespoke arithmetic type is needed; see
the `example`s below, which are exactly the conventions listed in the book.
-/

namespace Tdaf

section Conventions

example (r : ℝ) : (r : EReal) + ⊤ = ⊤ := by simp
example (r : ℝ) : (r : EReal) - ⊤ = ⊥ := by simp
example : (0 : EReal) * ⊤ = 0 := by simp
example : -(⊥ : EReal) = ⊤ := by simp
example : (⨆ _ : (∅ : Set ℝ), (0 : EReal)) = ⊥ := by simp

end Conventions

namespace EReal

/-- If `z` is below every real number strictly above `r`, then `z ≤ r`.

This is the standard device for turning a family of strict inequalities into a non-strict one, and
is what lets Rockafellar's strict form of convexity (Theorem 4.2) be converted back into the
epigraph form. -/
theorem le_coe_of_forall_lt {z : EReal} {r : ℝ} (h : ∀ q : ℝ, r < q → z < (q : EReal)) :
    z ≤ (r : EReal) := by
  by_contra hz
  push Not at hz
  obtain ⟨q, hrq, hqz⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hz
  exact absurd (h q (by exact_mod_cast hrq)) (not_lt.2 hqz.le)

/-- A value strictly below a real number is bounded by some real number strictly below it. -/
theorem exists_real_btwn_of_lt_coe {z : EReal} {r : ℝ} (h : z < (r : EReal)) :
    ∃ q : ℝ, z < (q : EReal) ∧ q < r := by
  obtain ⟨q, hzq, hqr⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 h
  exact ⟨q, hzq, by exact_mod_cast hqr⟩

/-- Multiplication by a positive real coefficient, in the form used by convexity arguments. -/
theorem coe_mul_coe (a r : ℝ) : (a : EReal) * (r : EReal) = ((a * r : ℝ) : EReal) :=
  (_root_.EReal.coe_mul a r).symm

/-- If `z` is below every real number, then `z = ⊥`. -/
theorem eq_bot_of_forall_le_coe {z : EReal} (h : ∀ r : ℝ, z ≤ (r : EReal)) : z = ⊥ := by
  by_contra hz
  obtain ⟨q, _, hqz⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 (bot_lt_iff_ne_bot.2 hz)
  exact absurd (h q) (not_le.2 hqz)

/-- An `EReal` that is neither `⊥` nor `⊤` is a real number. -/
theorem exists_coe_of_ne_bot_of_lt_top {z : EReal} (h₁ : z ≠ ⊥) (h₂ : z < ⊤) :
    ∃ r : ℝ, z = (r : EReal) := by
  lift z to ℝ using ⟨h₂.ne, h₁⟩ with r
  exact ⟨r, rfl⟩

end EReal

end Tdaf
