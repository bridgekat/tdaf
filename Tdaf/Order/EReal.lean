/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Data.EReal.Inv
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

/-- Negation distributes over an `EReal` sum as soon as neither summand is `⊤`, so that the
forbidden `∞ - ∞` cannot arise. Mathlib's `EReal.neg_add` has the sharpest hypotheses; this is the
symmetric special case that concave/convex sign transfer actually uses. -/
theorem neg_add_of_ne_top {u v : EReal} (hu : u ≠ ⊤) (hv : v ≠ ⊤) : -(u + v) = -u + -v := by
  rw [_root_.EReal.neg_add (Or.inr hv) (Or.inl hu), sub_eq_add_neg]

/-- A positive real multiple of an `EReal` below `⊤` stays below `⊤`. -/
theorem coe_mul_ne_top {a : ℝ} (ha : 0 < a) {u : EReal} (hu : u ≠ ⊤) : (a : EReal) * u ≠ ⊤ := by
  rw [_root_.EReal.mul_ne_top]
  exact ⟨Or.inl (_root_.EReal.coe_ne_bot a), Or.inl (by exact_mod_cast ha.le),
    Or.inl (_root_.EReal.coe_ne_top a), Or.inr hu⟩

/-- Negation turns a convex combination with positive real coefficients into the combination of the
negations — provided neither value is `⊤`, without which the identity is false on `EReal`. -/
theorem neg_combo {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {u v : EReal} (hu : u ≠ ⊤) (hv : v ≠ ⊤) :
    (a : EReal) * -u + (b : EReal) * -v = -((a : EReal) * u + (b : EReal) * v) := by
  rw [neg_add_of_ne_top (coe_mul_ne_top ha hu) (coe_mul_ne_top hb hv), mul_neg, mul_neg]

/-! The hypotheses of `Tdaf.EReal.neg_combo` are load-bearing, not defensive: at `u = ⊤`, `v = ⊥`
the two sides are `⊥` and `⊤`. Do not weaken them away. -/

example : (1 : EReal) * -(⊤ : EReal) + (1 : EReal) * -(⊥ : EReal) = ⊥ := by simp

example : -((1 : EReal) * (⊤ : EReal) + (1 : EReal) * (⊥ : EReal)) = ⊤ := by simp

/-- Multiplication by a positive real scalar reflects, as well as preserves, the order on `EReal`.
The reflection direction is proved by multiplying by the inverse scalar, since `EReal` has
`PosMulMono` but not `PosMulStrictMono`. -/
theorem coe_mul_le_coe_mul_iff {a : ℝ} (ha : 0 < a) {z w : EReal} :
    (a : EReal) * z ≤ (a : EReal) * w ↔ z ≤ w := by
  refine ⟨fun h => ?_, fun h => mul_le_mul_of_nonneg_left h (by exact_mod_cast ha.le)⟩
  have ha' : (0 : EReal) ≤ ((a⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.2 ha).le
  have h' := mul_le_mul_of_nonneg_left h ha'
  rwa [← mul_assoc, ← mul_assoc, ← _root_.EReal.coe_mul, inv_mul_cancel₀ ha.ne',
    _root_.EReal.coe_one, one_mul, one_mul] at h'

/-- An extended real is determined by the real numbers that bound it above. -/
theorem eq_of_forall_le_coe_iff {z w : EReal}
    (h : ∀ r : ℝ, z ≤ (r : EReal) ↔ w ≤ (r : EReal)) : z = w := by
  refine le_antisymm ?_ ?_
  · induction w with
    | bot => exact le_of_eq (eq_bot_of_forall_le_coe fun r => (h r).2 bot_le)
    | top => exact le_top
    | coe s => exact (h s).2 le_rfl
  · induction z with
    | bot => exact le_of_eq (eq_bot_of_forall_le_coe fun r => (h r).1 bot_le)
    | top => exact le_top
    | coe s => exact (h s).1 le_rfl

/-- The only extended reals fixed by multiplication by a positive scalar other than `1` are `0`,
`⊤` and `⊥`. This is the whole content of "positive homogeneity says nothing about `f 0`". -/
theorem eq_zero_or_eq_top_or_eq_bot {a : ℝ} (ha : a ≠ 1) {z : EReal} (h : (a : EReal) * z = z) :
    z = 0 ∨ z = ⊤ ∨ z = ⊥ := by
  induction z with
  | bot => exact Or.inr (Or.inr rfl)
  | top => exact Or.inr (Or.inl rfl)
  | coe r =>
    left
    rw [← _root_.EReal.coe_mul] at h
    have hr : a * r = r := by exact_mod_cast h
    have hz : (a - 1) * r = 0 := by rw [sub_mul, one_mul, hr, sub_self]
    rcases mul_eq_zero.1 hz with h1 | h1
    · exact absurd (by linarith : a = 1) ha
    · rw [h1, _root_.EReal.coe_zero]

/-- An extended real equal to its own negative is `0`. -/
theorem eq_zero_of_neg_eq {z : EReal} (h : -z = z) : z = 0 := by
  induction z with
  | bot => rw [_root_.EReal.neg_bot] at h; exact absurd h (by simp)
  | top => rw [_root_.EReal.neg_top] at h; exact absurd h (by simp)
  | coe r =>
    have hr : (-r : ℝ) = r := by exact_mod_cast h
    rw [(by linarith : r = (0 : ℝ)), _root_.EReal.coe_zero]

/-- Transposing a term across `0 ≤ u + v`, when `u` is not `⊥`. -/
theorem neg_le_of_zero_le_add {u v : EReal} (hu : u ≠ ⊥) (h : 0 ≤ u + v) : -u ≤ v := by
  induction u with
  | bot => exact absurd rfl hu
  | top => rw [_root_.EReal.neg_top]; exact bot_le
  | coe r =>
    induction v with
    | bot => rw [_root_.EReal.add_bot] at h; simp at h
    | top => exact le_top
    | coe s =>
      rw [← _root_.EReal.coe_add] at h
      have hrs : (0 : ℝ) ≤ r + s := by exact_mod_cast h
      rw [← _root_.EReal.coe_neg]
      exact_mod_cast (by linarith : -r ≤ s)

/-- A finite sum of `EReal`s none of which is `⊥` is not `⊥`.

This is an `EReal` fact rather than a convexity fact; it is stated here because `Tdaf.ConvexFn.sum`
is its only consumer so far. -/
theorem sum_ne_bot {ι : Type*} {s : Finset ι} {g : ι → EReal} (h : ∀ i ∈ s, g i ≠ ⊥) :
    ∑ i ∈ s, g i ≠ ⊥ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i t hi ih =>
    rw [Finset.sum_cons]
    exact _root_.EReal.add_ne_bot_iff.2 ⟨h i (by simp), ih fun j hj => h j (by simp [hj])⟩

/-- Dividing through by a positive real coefficient. This is the form in which a hypothesis
`(a : EReal) * z ≤ r` gets used: it turns a statement about `a • f` into one about `f`. -/
theorem coe_mul_le_coe_iff {a : ℝ} (ha : 0 < a) {z : EReal} {r : ℝ} :
    (a : EReal) * z ≤ (r : EReal) ↔ z ≤ ((r / a : ℝ) : EReal) := by
  induction z with
  | bot => simp [_root_.EReal.coe_mul_bot_of_pos ha]
  | top => simp [_root_.EReal.coe_mul_top_of_pos ha]
  | coe s =>
    rw [coe_mul_coe, _root_.EReal.coe_le_coe_iff, _root_.EReal.coe_le_coe_iff, le_div_iff₀ ha,
      mul_comm]

variable {κ : Type*}

/-- The coercion `ℝ → EReal` commutes with finite sums. -/
theorem coe_sum (t : Finset κ) (r : κ → ℝ) :
    ((∑ i ∈ t, r i : ℝ) : EReal) = ∑ i ∈ t, ((r i : ℝ) : EReal) := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons i t hi ih => rw [Finset.sum_cons, Finset.sum_cons, _root_.EReal.coe_add, ih]

/-- A non-negative real multiple of an `EReal` other than `⊥` is not `⊥`. The coefficient `0` is
harmless because `EReal` obeys Rockafellar's convention `0 · ∞ = 0`. -/
theorem coe_mul_ne_bot {a : ℝ} (ha : 0 ≤ a) {z : EReal} (hz : z ≠ ⊥) : (a : EReal) * z ≠ ⊥ := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h, _root_.EReal.coe_zero, zero_mul]; simp
  · induction z with
    | bot => exact absurd rfl hz
    | top => rw [_root_.EReal.coe_mul_top_of_pos h]; exact top_ne_bot
    | coe r => rw [coe_mul_coe]; exact _root_.EReal.coe_ne_bot _

/-- If a finite sum of `EReal`s none of which is `⊥` is not `⊤`, then no term is `⊤`. This is the
form in which "the sum is unambiguous" gets used: it turns a finite bound on a sum into a finite
bound on each term. -/
theorem forall_ne_top_of_sum_ne_top (t : Finset κ) (z : κ → EReal) :
    (∀ i ∈ t, z i ≠ ⊥) → (∑ i ∈ t, z i ≠ ⊤) → ∀ i ∈ t, z i ≠ ⊤ := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons j t hj ih =>
    intro hbot hsum i hi
    rw [Finset.sum_cons] at hsum
    have h₁ : z j ≠ ⊥ := hbot j (by simp)
    have h₂ : (∑ k ∈ t, z k) ≠ ⊥ := sum_ne_bot fun k hk => hbot k (by simp [hk])
    obtain ⟨hj', ht'⟩ := (_root_.EReal.add_ne_top_iff_ne_top₂ h₁ h₂).1 hsum
    rcases Finset.mem_cons.1 hi with rfl | hi'
    · exact hj'
    · exact ih (fun k hk => hbot k (by simp [hk])) ht' i hi'

end EReal

end Tdaf
