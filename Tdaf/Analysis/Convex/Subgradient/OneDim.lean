/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Closure
import Tdaf.Analysis.Convex.Subgradient.Monotone

/-!
# One-sided derivatives of a convex function on the line

On the line a convex function has a right derivative `f'₊` and a left derivative `f'₋` at every
point, with values in `[-∞, +∞]`, and they carry all the first-order information:

```
∂f(x) = {x* ∈ ℝ | f'₋(x) ≤ x* ≤ f'₊(x)}.
```

Both are **nondecreasing**, interlaced as

```
f'₊(z₁) ≤ f'₋(x) ≤ f'₊(x) ≤ f'₋(z₂)          for z₁ < x < z₂,
```

both are real exactly on `int (dom f)`, and — when `f` is closed — each is the one-sided limit of
the other:

```
lim_{z ↓ x} f'₊(z) = lim_{z ↓ x} f'₋(z) = f'₊(x),
lim_{z ↑ x} f'₊(z) = lim_{z ↑ x} f'₋(z) = f'₋(x).
```

So `f'₊` is right-continuous, `f'₋` is left-continuous, and either one determines the other. In
consequence any nondecreasing `φ` with `f'₋ ≤ φ ≤ f'₊` determines `∂f`, and hence determines `f`
itself up to an additive constant.

## Main definitions

* `rightDeriv f x`, `leftDeriv f x` — the two one-sided derivatives, extended by `+∞` to the right
  of `dom f` and by `-∞` to its left.

## Main results

* `leftDeriv_le_rightDeriv`, `rightDeriv_le_leftDeriv`, `monotone_rightDeriv`,
  `monotone_leftDeriv` — the interlacing chain and monotonicity.
* `rightDeriv_lt_top_iff`, `bot_lt_leftDeriv_iff`,
  `bot_lt_leftDeriv_and_rightDeriv_lt_top_iff` — finiteness, and its identification with
  interiority of `dom f`.
* `mem_subgradient_iff_le_rightDeriv` — `∂f(x)` is the interval `[f'₋(x), f'₊(x)]`.
* `iInf_rightDeriv_Ioi`, `iSup_leftDeriv_Iio`, `iInf_leftDeriv_Ioi`, `iSup_rightDeriv_Iio` and
  their `Tendsto` forms `tendsto_rightDeriv_nhdsWithin_Ioi` and companions — the four limit
  formulas, for a closed proper convex `f`.
* `iInf_Ioi_eq_rightDeriv`, `iSup_Iio_eq_leftDeriv` — a nondecreasing `φ` between `f'₋` and `f'₊`
  has the same one-sided limits.
* `exists_eq_add_coe_of_deriv_eq`, `exists_eq_add_coe_of_le_le` — two closed proper convex
  functions with the same one-sided derivatives, or squeezed around a common `φ`, differ by a
  constant.
* `tendsto_nhdsWithin_Ioi_of_monotone`, `tendsto_nhdsWithin_Iio_of_monotone` — the general fact
  that a monotone map into a complete linear order has one-sided limits, equal to the obvious
  infimum and supremum.

## Design notes

**The two definitions are guarded infima and suprema.** `f'₊(x)` is `f'(x; 1)` *provided* some
point of `dom f` lies to the right of `x`, and `+∞` otherwise; the guard is written
`⨅ _ : ∃ z > x, f z < ⊤, f'(x; 1)`, which is the guarded value on one branch and `⊤` on the other.
It is genuinely needed: where `f x = ⊤` every difference quotient is `⊤ - ⊤ = ⊥`, so the unguarded
infimum would be `-∞` on *both* sides of `dom f`, whereas the two sides must be told apart. Where
`f` is finite the guard is inert (`rightDeriv_eq_dirDeriv`).

**`f'₊` is `f'(x; 1)` and `f'₋` is `-f'(x; -1)`**, so the whole theory of `dirDeriv` from §23 —
monotone difference quotients, convexity, the link with `∂f` — is available and nothing is
redefined. The sign in `f'₋` is because the increment `z - x` is negative there.

**The limit formulas need `f` closed and nothing else.** They fail for
`f = 1 at 0, 0 on (0, ∞), ⊤ on (-∞, 0)`, which is convex and proper but not closed: `f'₊` jumps at
`0`. The proof is Rockafellar's: a real `μ` below every `f'₊(z)`, `z > x`, bounds `f` above by an
affine function of slope `μ` on the segment approaching `x`, and closedness (Corollary 7.5.1)
carries that bound to `x` itself.

**Monotonicity is cheaper than it looks.** `f'₊(y) ≤ f'₋(z)` for `y < z` needs only properness:
`dirDeriv` is an *infimum* of difference quotients, and the two quotients across `[y, z]` bound it
whatever `f` is. Convexity enters only in `f'₋(x) ≤ f'₊(x)` at a single point.

## What is not here

**The construction of `f` from `φ` by integration**, `f(x) = ∫ₐˣ φ(t) dt`, and with it the
identification of the graphs of one-dimensional subdifferentials as the *complete nondecreasing
curves*. It needs the integral of a nondecreasing `[-∞, +∞]`-valued function, improper at the two
ends of the interval where `φ` is finite, together with the fact that the resulting function is
closed there — real-analysis machinery the project does not have. Only the uniqueness half of that
correspondence is proved here, and it does not go through the integral at all: it goes through
`∂f = ∂g` and the rigidity theorem of `Subgradient/Monotone.lean`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §24 (Theorem 24.1, the
  remark following it, and the uniqueness clause of Theorem 24.2); §23 (Theorems 23.1, 23.2).
-/

open Set Filter Topology

namespace Tdaf.ConvexAnalysis

/-! ### The directional derivative at a point outside the effective domain -/

section Outside

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {x : E}

/-- Where `f` is `+∞` every difference quotient is `-∞`, so the directional derivative is `-∞` in
every direction. This is the value Rockafellar wants to the *left* of `dom f` and the value he
overrides to the right. -/
theorem dirDeriv_eq_bot_of_eq_top (hx : f x = ⊤) (y : E) : dirDeriv f x y = ⊥ := by
  refine le_antisymm ?_ bot_le
  refine (dirDeriv_le f x y one_pos).trans ?_
  rw [hx, _root_.EReal.sub_top,
    _root_.EReal.bot_div_of_pos_ne_top (by exact_mod_cast one_pos) (_root_.EReal.coe_ne_top 1)]

end Outside

/-! ### The right and left derivatives -/

section Defs

variable {f : ℝ → EReal} {x : ℝ}

/-- The **right derivative** of an extended-real-valued function on the line,

```
f'₊(x) = lim_{z ↓ x} (f z - f x) / (z - x),
```

with the convention that it is `+∞` at every point lying to the right of `dom f`. Without that
override the difference quotients would all be `-∞` there, which is the value belonging to the
points on the *left*; the two sides have to be told apart by hand, and the guard
`∃ z > x, f z < ⊤` is what does it. -/
noncomputable def rightDeriv (f : ℝ → EReal) (x : ℝ) : EReal :=
  ⨅ _ : ∃ z, x < z ∧ f z < ⊤, dirDeriv f x 1

/-- The **left derivative**

```
f'₋(x) = lim_{z ↑ x} (f z - f x) / (z - x),
```

`-∞` at every point lying to the left of `dom f`. It is `-f'(x; -1)` because the increment
`z - x` is negative. -/
noncomputable def leftDeriv (f : ℝ → EReal) (x : ℝ) : EReal :=
  ⨆ _ : ∃ z, z < x ∧ f z < ⊤, -dirDeriv f x (-1)

theorem rightDeriv_of_exists (h : ∃ z, x < z ∧ f z < ⊤) :
    rightDeriv f x = dirDeriv f x 1 := iInf_pos h

theorem rightDeriv_of_not_exists (h : ¬∃ z, x < z ∧ f z < ⊤) : rightDeriv f x = ⊤ := iInf_neg h

theorem leftDeriv_of_exists (h : ∃ z, z < x ∧ f z < ⊤) :
    leftDeriv f x = -dirDeriv f x (-1) := iSup_pos h

theorem leftDeriv_of_not_exists (h : ¬∃ z, z < x ∧ f z < ⊤) : leftDeriv f x = ⊥ := iSup_neg h

/-- To the right of `dom f` the right derivative is `+∞` by fiat; to the left of it, `-∞`. -/
theorem rightDeriv_eq_bot_of_eq_top (hx : f x = ⊤) (h : ∃ z, x < z ∧ f z < ⊤) :
    rightDeriv f x = ⊥ := by
  rw [rightDeriv_of_exists h, dirDeriv_eq_bot_of_eq_top hx]

/-- To the left of `dom f` the left derivative is `-∞` by fiat; to the right of it, `+∞`. -/
theorem leftDeriv_eq_top_of_eq_top (hx : f x = ⊤) (h : ∃ z, z < x ∧ f z < ⊤) :
    leftDeriv f x = ⊤ := by
  rw [leftDeriv_of_exists h, dirDeriv_eq_bot_of_eq_top hx, _root_.EReal.neg_bot]

end Defs

/-! ### Monotonicity -/

section Order

variable {f : ℝ → EReal} {x : ℝ}

/-- On the line, the effective domain of a convex function is an interval: a point between two
points of `dom f` lies in `dom f`. -/
theorem ConvexFn.lt_top_of_le_of_le (hf : ConvexFn f) {z₁ z₂ : ℝ} (h₁ : f z₁ < ⊤) (h₂ : f z₂ < ⊤)
    (hz₁ : z₁ ≤ x) (hz₂ : x ≤ z₂) : f x < ⊤ :=
  hf.convex_dom.ordConnected.out (mem_dom.2 h₁) (mem_dom.2 h₂) (mem_Icc.2 ⟨hz₁, hz₂⟩)

theorem leftDeriv_le_neg_dirDeriv (f : ℝ → EReal) (x : ℝ) :
    leftDeriv f x ≤ -dirDeriv f x (-1) := by
  rcases em (∃ z, z < x ∧ f z < ⊤) with h | h
  · exact le_of_eq (leftDeriv_of_exists h)
  · rw [leftDeriv_of_not_exists h]; exact bot_le

theorem dirDeriv_le_rightDeriv (f : ℝ → EReal) (x : ℝ) :
    dirDeriv f x 1 ≤ rightDeriv f x := by
  rcases em (∃ z, x < z ∧ f z < ⊤) with h | h
  · exact le_of_eq (rightDeriv_of_exists h).symm
  · rw [rightDeriv_of_not_exists h]; exact le_top

/-- `f'₋(x) ≤ f'₊(x)` at every point of the line. -/
theorem leftDeriv_le_rightDeriv (hf : ConvexFn f) (hp : Proper f) (x : ℝ) :
    leftDeriv f x ≤ rightDeriv f x := by
  rcases lt_or_ge (f x) ⊤ with hx | hx
  · exact (leftDeriv_le_neg_dirDeriv f x).trans
      ((neg_dirDeriv_neg_le hf hx.ne (hp.ne_bot x) 1).trans (dirDeriv_le_rightDeriv f x))
  have hxt : f x = ⊤ := top_le_iff.1 hx
  rcases em (∃ z, x < z ∧ f z < ⊤) with h₂ | h₂
  · rcases em (∃ z, z < x ∧ f z < ⊤) with h₁ | h₁
    · obtain ⟨z₁, hz₁, hfz₁⟩ := h₁
      obtain ⟨z₂, hz₂, hfz₂⟩ := h₂
      exact absurd (hf.lt_top_of_le_of_le hfz₁ hfz₂ hz₁.le hz₂.le) (by rw [hxt]; simp)
    · rw [leftDeriv_of_not_exists h₁]; exact bot_le
  · rw [rightDeriv_of_not_exists h₂]; exact le_top

/-- The right derivative at the left end of an interval is at most the slope across it. This is
one instance of the defining infimum, with the step `z - y`. -/
theorem dirDeriv_one_le_slope {y z p q : ℝ} (hyz : y < z) (hfy : f y = (p : EReal))
    (hfz : f z = (q : EReal)) : dirDeriv f y 1 ≤ (((q - p) / (z - y) : ℝ) : EReal) := by
  have hle := dirDeriv_le f y 1 (by linarith : (0 : ℝ) < z - y)
  rwa [show y + (z - y) • (1 : ℝ) = z by rw [smul_eq_mul]; ring, hfy, hfz,
    ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div] at hle

/-- The mirror image of `dirDeriv_one_le_slope`, at the right end of the interval. -/
theorem dirDeriv_neg_one_le_slope {y z p q : ℝ} (hyz : y < z) (hfy : f y = (p : EReal))
    (hfz : f z = (q : EReal)) : dirDeriv f z (-1) ≤ (((p - q) / (z - y) : ℝ) : EReal) := by
  have hle := dirDeriv_le f z (-1) (by linarith : (0 : ℝ) < z - y)
  rwa [show z + (z - y) • (-1 : ℝ) = y by rw [smul_eq_mul]; ring, hfy, hfz,
    ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div] at hle

/-- **The step from one point to the next**: `f'₊(y) ≤ f'₋(z)` whenever `y < z`. Together with
`f'₋ ≤ f'₊` this is Rockafellar's chain `f'₊(z₁) ≤ f'₋(x) ≤ f'₊(x) ≤ f'₋(z₂)` for `z₁ < x < z₂`,
and it is what makes both functions nondecreasing.

Convexity is *not* needed: `dirDeriv` is an infimum of difference quotients rather than a limit of
them, so the two quotients across `[y, z]` bound it from above whatever `f` is. Only `f'₋ ≤ f'₊`
at a single point uses convexity. -/
theorem rightDeriv_le_leftDeriv (hp : Proper f) {y z : ℝ} (hyz : y < z) :
    rightDeriv f y ≤ leftDeriv f z := by
  rcases em (∃ w, y < w ∧ f w < ⊤) with h₂ | h₂
  swap
  · -- nothing of `dom f` lies to the right of `y`, so `f'₊(y) = ⊤` and `z` sits beyond `dom f`
    obtain ⟨w₀, hw₀⟩ := hp.dom_nonempty
    have hw₀y : w₀ ≤ y := not_lt.1 fun hlt => h₂ ⟨w₀, hlt, mem_dom.1 hw₀⟩
    rw [leftDeriv_eq_top_of_eq_top (top_le_iff.1 (not_lt.1 fun hlt => h₂ ⟨z, hyz, hlt⟩))
      ⟨w₀, lt_of_le_of_lt hw₀y hyz, mem_dom.1 hw₀⟩]
    exact le_top
  rcases em (∃ w, w < z ∧ f w < ⊤) with h₁ | h₁
  swap
  · -- nothing of `dom f` lies to the left of `z`, so `f'₋(z) = ⊥` and `y` sits before `dom f`
    obtain ⟨w₀, hw₀⟩ := hp.dom_nonempty
    have hzw₀ : z ≤ w₀ := not_lt.1 fun hlt => h₁ ⟨w₀, hlt, mem_dom.1 hw₀⟩
    rw [rightDeriv_eq_bot_of_eq_top (top_le_iff.1 (not_lt.1 fun hlt => h₁ ⟨y, hyz, hlt⟩))
      ⟨w₀, lt_of_lt_of_le hyz hzw₀, mem_dom.1 hw₀⟩]
    exact bot_le
  rw [rightDeriv_of_exists h₂, leftDeriv_of_exists h₁]
  rcases lt_or_ge (f y) ⊤ with hfy | hfy
  swap
  · rw [dirDeriv_eq_bot_of_eq_top (top_le_iff.1 hfy)]; exact bot_le
  rcases lt_or_ge (f z) ⊤ with hfz | hfz
  swap
  · rw [dirDeriv_eq_bot_of_eq_top (top_le_iff.1 hfz), _root_.EReal.neg_bot]; exact le_top
  obtain ⟨p, hp'⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot y) hfy
  obtain ⟨q, hq'⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot z) hfz
  calc dirDeriv f y 1 ≤ (((q - p) / (z - y) : ℝ) : EReal) := dirDeriv_one_le_slope hyz hp' hq'
    _ = -(((p - q) / (z - y) : ℝ) : EReal) := by
        rw [← _root_.EReal.coe_neg]; congr 1; ring
    _ ≤ -dirDeriv f z (-1) :=
        _root_.EReal.neg_le_neg_iff.2 (dirDeriv_neg_one_le_slope hyz hp' hq')

/-- `f'₊` is nondecreasing on the whole line. -/
theorem monotone_rightDeriv (hf : ConvexFn f) (hp : Proper f) : Monotone (rightDeriv f) := by
  intro y z hyz
  rcases eq_or_lt_of_le hyz with rfl | hlt
  · exact le_rfl
  exact (rightDeriv_le_leftDeriv hp hlt).trans (leftDeriv_le_rightDeriv hf hp z)

/-- `f'₋` is nondecreasing on the whole line. -/
theorem monotone_leftDeriv (hf : ConvexFn f) (hp : Proper f) : Monotone (leftDeriv f) := by
  intro y z hyz
  rcases eq_or_lt_of_le hyz with rfl | hlt
  · exact le_rfl
  exact (leftDeriv_le_rightDeriv hf hp y).trans (rightDeriv_le_leftDeriv hp hlt)

end Order

/-! ### Finiteness -/

section Finite

variable {f : ℝ → EReal} {x : ℝ}

/-- `f'₊(x)` is `< +∞` exactly when some point of `dom f` lies to the right of `x` — that is,
exactly when `x` lies strictly to the left of the right endpoint of `dom f`. -/
theorem rightDeriv_lt_top_iff (hp : Proper f) :
    rightDeriv f x < ⊤ ↔ ∃ z, x < z ∧ f z < ⊤ := by
  refine ⟨fun h => by_contra fun hcon => ?_, fun h => ?_⟩
  · rw [rightDeriv_of_not_exists hcon] at h
    exact lt_irrefl _ h
  obtain ⟨z, hz, hfz⟩ := h
  rw [rightDeriv_of_exists ⟨z, hz, hfz⟩]
  rcases lt_or_ge (f x) ⊤ with hx | hx
  · obtain ⟨p, hp'⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
    obtain ⟨q, hq'⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot z) hfz
    exact lt_of_le_of_lt (dirDeriv_one_le_slope hz hp' hq') (_root_.EReal.coe_lt_top _)
  · rw [dirDeriv_eq_bot_of_eq_top (top_le_iff.1 hx)]
    exact bot_lt_top

/-- `f'₋(x)` is `> -∞` exactly when some point of `dom f` lies to the left of `x`. -/
theorem bot_lt_leftDeriv_iff (hp : Proper f) :
    ⊥ < leftDeriv f x ↔ ∃ z, z < x ∧ f z < ⊤ := by
  refine ⟨fun h => by_contra fun hcon => ?_, fun h => ?_⟩
  · rw [leftDeriv_of_not_exists hcon] at h
    exact lt_irrefl _ h
  obtain ⟨z, hz, hfz⟩ := h
  rw [leftDeriv_of_exists ⟨z, hz, hfz⟩]
  rcases lt_or_ge (f x) ⊤ with hx | hx
  · obtain ⟨q, hq'⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
    obtain ⟨p, hp'⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot z) hfz
    refine lt_of_lt_of_le ?_ (_root_.EReal.neg_le_neg_iff.2 (dirDeriv_neg_one_le_slope hz hp' hq'))
    rw [← _root_.EReal.coe_neg]
    exact _root_.EReal.bot_lt_coe _
  · rw [dirDeriv_eq_bot_of_eq_top (top_le_iff.1 hx), _root_.EReal.neg_bot]
    exact bot_lt_top

/-- **Both one-sided derivatives are finite exactly on the interior of `dom f`.** Rockafellar
states the two halves separately, as `f'₊ < +∞` to the left of the right endpoint and `f'₋ > -∞`
to the right of the left endpoint; on the line those two conditions together *are* interiority. -/
theorem bot_lt_leftDeriv_and_rightDeriv_lt_top_iff (hf : ConvexFn f) (hp : Proper f) :
    (⊥ < leftDeriv f x ∧ rightDeriv f x < ⊤) ↔ x ∈ interior (dom f) := by
  rw [bot_lt_leftDeriv_iff hp, rightDeriv_lt_top_iff hp]
  constructor
  · rintro ⟨⟨z₁, hz₁, hfz₁⟩, ⟨z₂, hz₂, hfz₂⟩⟩
    refine mem_interior.2 ⟨Ioo z₁ z₂, fun w hw => ?_, isOpen_Ioo, ⟨hz₁, hz₂⟩⟩
    exact mem_dom.2 (hf.lt_top_of_le_of_le hfz₁ hfz₂ hw.1.le hw.2.le)
  · intro hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx)
    have hmem : ∀ w : ℝ, |w - x| < ε → f w < ⊤ := fun w hw =>
      mem_dom.1 (interior_subset (hball (by rwa [Metric.mem_ball, Real.dist_eq])))
    exact ⟨⟨x - ε / 2, by linarith, hmem _ (by rw [abs_of_nonpos (by linarith)]; linarith)⟩,
      ⟨x + ε / 2, by linarith, hmem _ (by rw [abs_of_nonneg (by linarith)]; linarith)⟩⟩

/-- Both one-sided derivatives are real at an interior point of `dom f`. -/
theorem leftDeriv_finite_of_mem_interior_dom (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) : leftDeriv f x ≠ ⊥ ∧ leftDeriv f x ≠ ⊤ := by
  obtain ⟨h1, h2⟩ := (bot_lt_leftDeriv_and_rightDeriv_lt_top_iff hf hp).2 hx
  exact ⟨h1.ne', ((leftDeriv_le_rightDeriv hf hp x).trans_lt h2).ne⟩

/-- Both one-sided derivatives are real at an interior point of `dom f`. -/
theorem rightDeriv_finite_of_mem_interior_dom (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) : rightDeriv f x ≠ ⊥ ∧ rightDeriv f x ≠ ⊤ := by
  obtain ⟨h1, h2⟩ := (bot_lt_leftDeriv_and_rightDeriv_lt_top_iff hf hp).2 hx
  exact ⟨(h1.trans_le (leftDeriv_le_rightDeriv hf hp x)).ne', h2.ne⟩

end Finite

/-! ### The subdifferential on the line -/

section Subgradient

variable {f : ℝ → EReal} {x : ℝ}

/-- Where `f` is finite the guard in the definition of `f'₊` is inert: the difference quotients
already produce `+∞` beyond the right end of `dom f`. -/
theorem rightDeriv_eq_dirDeriv (hx : f x < ⊤) (hb : f x ≠ ⊥) :
    rightDeriv f x = dirDeriv f x 1 := by
  rcases em (∃ z, x < z ∧ f z < ⊤) with h | h
  · exact rightDeriv_of_exists h
  obtain ⟨p, hp'⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top hb hx
  rw [rightDeriv_of_not_exists h]
  refine (top_le_iff.1 (le_dirDeriv fun a ha => ?_)).symm
  have hz : f (x + a • (1 : ℝ)) = ⊤ := by
    rw [show x + a • (1 : ℝ) = x + a by rw [smul_eq_mul]; ring]
    exact top_le_iff.1 (not_lt.1 fun hlt => h ⟨x + a, by linarith, hlt⟩)
  rw [hz, hp', _root_.EReal.top_sub_coe,
    _root_.EReal.top_div_of_pos_ne_top (by exact_mod_cast ha) (_root_.EReal.coe_ne_top a)]

/-- The mirror image: where `f` is finite, `f'₋(x) = -f'(x; -1)` with no guard. -/
theorem leftDeriv_eq_neg_dirDeriv (hx : f x < ⊤) (hb : f x ≠ ⊥) :
    leftDeriv f x = -dirDeriv f x (-1) := by
  rcases em (∃ z, z < x ∧ f z < ⊤) with h | h
  · exact leftDeriv_of_exists h
  obtain ⟨p, hp'⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top hb hx
  have htop : dirDeriv f x (-1) = ⊤ := by
    refine top_le_iff.1 (le_dirDeriv fun a ha => ?_)
    have hz : f (x + a • (-1 : ℝ)) = ⊤ := by
      rw [show x + a • (-1 : ℝ) = x - a by rw [smul_eq_mul]; ring]
      exact top_le_iff.1 (not_lt.1 fun hlt => h ⟨x - a, by linarith, hlt⟩)
    rw [hz, hp', _root_.EReal.top_sub_coe,
      _root_.EReal.top_div_of_pos_ne_top (by exact_mod_cast ha) (_root_.EReal.coe_ne_top a)]
  rw [leftDeriv_of_not_exists h, htop, _root_.EReal.neg_top]

/-- **The subdifferential on the line is the interval between the one-sided derivatives**:

```
∂f(x) = {x* ∈ ℝ | f'₋(x) ≤ x* ≤ f'₊(x)}.
```

Rockafellar records this immediately after Theorem 24.1, as a consequence of Theorem 23.2. Only
the two directions `+1` and `-1` carry information, because `f'(x; ·)` is positively
homogeneous. -/
theorem mem_subgradient_iff_le_rightDeriv_of_lt_top (hx : f x < ⊤) (hb : f x ≠ ⊥) {y : ℝ} :
    y ∈ subgradient (innerₗ ℝ) f x ↔
      leftDeriv f x ≤ (y : EReal) ∧ (y : EReal) ≤ rightDeriv f x := by
  have hpair : ∀ v : ℝ, (innerₗ ℝ) v y = y * v := fun v => by simp [innerₗ_apply_apply]
  rw [mem_subgradient_iff_le_dirDeriv hx.ne hb, rightDeriv_eq_dirDeriv hx hb,
    leftDeriv_eq_neg_dirDeriv hx hb]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := h (-1)
      rw [hpair, mul_neg_one] at h1
      have h2 := _root_.EReal.neg_le_neg_iff.2 h1
      rwa [← _root_.EReal.coe_neg, neg_neg] at h2
    · have h1 := h 1
      rwa [hpair, mul_one] at h1
  · rintro ⟨hl, hr⟩ v
    rw [hpair]
    rcases lt_trichotomy v 0 with hv | rfl | hv
    · have hw : (0 : ℝ) < -v := by linarith
      have hv1 : dirDeriv f x v = ((-v : ℝ) : EReal) * dirDeriv f x (-1) := by
        have hph := posHomogeneous_dirDeriv f x (-v) hw (-1)
        rwa [show (-v) • (-1 : ℝ) = v by rw [smul_eq_mul]; ring] at hph
      have hy : ((y * v : ℝ) : EReal) = ((-v : ℝ) : EReal) * ((-y : ℝ) : EReal) := by
        rw [← _root_.EReal.coe_mul]; congr 1; ring
      rw [hv1, hy, Tdaf.EReal.coe_mul_le_coe_mul_iff hw, _root_.EReal.coe_neg]
      have h2 := _root_.EReal.neg_le_neg_iff.2 hl
      rwa [neg_neg] at h2
    · rw [dirDeriv_zero hx.ne hb]
      simp
    · have hv1 : dirDeriv f x v = ((v : ℝ) : EReal) * dirDeriv f x 1 := by
        have hph := posHomogeneous_dirDeriv f x v hv 1
        rwa [smul_eq_mul, mul_one] at hph
      have hy : ((y * v : ℝ) : EReal) = ((v : ℝ) : EReal) * ((y : ℝ) : EReal) := by
        rw [← _root_.EReal.coe_mul]; congr 1; ring
      rw [hv1, hy, Tdaf.EReal.coe_mul_le_coe_mul_iff hv]
      exact hr

/-- A real number squeezed between the two one-sided derivatives forces `x` into `dom f`: outside
`dom f` one of the two is `±∞` on the wrong side. -/
theorem lt_top_of_leftDeriv_le_of_le_rightDeriv (hp : Proper f) {y : ℝ}
    (h₁ : leftDeriv f x ≤ (y : EReal)) (h₂ : (y : EReal) ≤ rightDeriv f x) : f x < ⊤ := by
  by_contra hcon
  have hxt : f x = ⊤ := top_le_iff.1 (not_lt.1 hcon)
  rcases em (∃ z, z < x ∧ f z < ⊤) with hl | hl
  · rw [leftDeriv_eq_top_of_eq_top hxt hl] at h₁
    exact absurd (top_le_iff.1 h₁) (_root_.EReal.coe_ne_top y)
  rcases em (∃ z, x < z ∧ f z < ⊤) with hr | hr
  · rw [rightDeriv_eq_bot_of_eq_top hxt hr] at h₂
    exact absurd (le_bot_iff.1 h₂) (_root_.EReal.coe_ne_bot y)
  obtain ⟨w, hw⟩ := hp.dom_nonempty
  rcases lt_trichotomy w x with h | h | h
  · exact hl ⟨w, h, mem_dom.1 hw⟩
  · rw [h] at hw; exact absurd (mem_dom.1 hw) (by rw [hxt]; simp)
  · exact hr ⟨w, h, mem_dom.1 hw⟩

/-- **The subdifferential on the line**, with no hypothesis on `x`: outside `dom f` both sides are
false. -/
theorem mem_subgradient_iff_le_rightDeriv (hp : Proper f) {y : ℝ} :
    y ∈ subgradient (innerₗ ℝ) f x ↔
      leftDeriv f x ≤ (y : EReal) ∧ (y : EReal) ≤ rightDeriv f x := by
  rcases lt_or_ge (f x) ⊤ with hx | hx
  · exact mem_subgradient_iff_le_rightDeriv_of_lt_top hx (hp.ne_bot x)
  refine ⟨fun hmem => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · rw [subgradient_eq_empty_of_notMem_dom hp (by rwa [mem_dom, not_lt])] at hmem
    exact absurd hmem (notMem_empty y)
  · exact absurd (lt_top_of_leftDeriv_le_of_le_rightDeriv hp h₁ h₂) (not_lt.2 hx)

end Subgradient

/-! ### One-sided limits of a monotone function -/

section MonotoneLimit

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {g : α → β}

/-- A monotone map into a complete linear order converges from the right, to the infimum of its
values there. -/
theorem tendsto_nhdsWithin_Ioi_of_monotone (hg : Monotone g) (x : α) :
    Tendsto g (𝓝[>] x) (𝓝 (⨅ z ∈ Ioi x, g z)) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact lt_of_lt_of_le hb (iInf₂_le z hz)
  · obtain ⟨z₀, hz₀, hlt⟩ : ∃ z₀ ∈ Ioi x, g z₀ < b := by
      by_contra hcon
      push Not at hcon
      exact absurd (le_iInf₂ fun z hz => hcon z hz) (not_le.2 hb)
    filter_upwards [Ioo_mem_nhdsGT hz₀] with z hz
    exact lt_of_le_of_lt (hg hz.2.le) hlt

/-- A monotone map into a complete linear order converges from the left, to the supremum of its
values there. -/
theorem tendsto_nhdsWithin_Iio_of_monotone (hg : Monotone g) (x : α) :
    Tendsto g (𝓝[<] x) (𝓝 (⨆ z ∈ Iio x, g z)) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨z₀, hz₀, hlt⟩ : ∃ z₀ ∈ Iio x, b < g z₀ := by
      by_contra hcon
      push Not at hcon
      exact absurd (iSup₂_le fun z hz => hcon z hz) (not_le.2 hb)
    filter_upwards [Ioo_mem_nhdsLT hz₀] with z hz
    exact lt_of_lt_of_le hlt (hg hz.1.le)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    refine lt_of_le_of_lt ?_ hb
    exact le_iSup₂ (f := fun z (_ : z ∈ Iio x) => g z) z hz

end MonotoneLimit

/-! ### The limit formulas -/

section Limits

variable {f : ℝ → EReal} {x : ℝ}

/-- **The estimate behind the right-hand limit formulas.** If a real `μ` lies strictly below
`f'₊(z)` for every `z > x`, then `f` itself is bounded by the affine function of slope `μ` through
`(y, f y)`, at `x`.

Along the segment from `y` down to `x`, each interior point `z` has `μ < f'₊(z) ≤` the slope from
`z` to `y`, which bounds `f z` from above; closedness lets the bound pass to the endpoint `x`
(Corollary 7.5.1). -/
theorem le_coe_of_lt_rightDeriv (hf : ClosedProperConvexFn f) {y : ℝ} (hxy : x < y) {q : ℝ}
    (hq : f y = (q : EReal)) {μ : ℝ} (hμ : ∀ z, x < z → (μ : EReal) < rightDeriv f z) :
    f x ≤ ((q - μ * (y - x) : ℝ) : EReal) := by
  have hydom : y ∈ dom f := mem_dom.2 (by rw [hq]; exact _root_.EReal.coe_lt_top q)
  have hseg := tendsto_along_segment_of_closed_proper hf hydom x
  have hzeq : ∀ t : ℝ, (1 - t) • y + t • x = y + t * (x - y) := by
    intro t; rw [smul_eq_mul, smul_eq_mul]; ring
  have hest : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      f ((1 - t) • y + t • x) ≤ ((q - μ * (t * (y - x)) : ℝ) : EReal) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with t ht1 ht0
    have ht1' : t < 1 := ht1
    rw [hzeq t]
    set w : ℝ := y + t * (x - y) with hw
    have hxw : x < w := by rw [hw]; nlinarith
    have hwy : w < y := by rw [hw]; nlinarith
    have hd : (0 : ℝ) < t * (y - x) := by nlinarith
    have hgap : y - w = t * (y - x) := by rw [hw]; ring
    have hlt := hμ w hxw
    rcases lt_or_ge (f w) ⊤ with hfw | hfw
    · obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot w) hfw
      rw [rightDeriv_eq_dirDeriv hfw (hf.proper.ne_bot w)] at hlt
      have hslope := dirDeriv_one_le_slope hwy hr hq
      rw [hgap] at hslope
      have : (μ : EReal) < (((q - r) / (t * (y - x)) : ℝ) : EReal) := lt_of_lt_of_le hlt hslope
      rw [_root_.EReal.coe_lt_coe_iff, lt_div_iff₀ hd] at this
      rw [hr, _root_.EReal.coe_le_coe_iff]
      linarith
    · rw [rightDeriv_eq_bot_of_eq_top (top_le_iff.1 hfw)
        ⟨y, hwy, by rw [hq]; exact _root_.EReal.coe_lt_top q⟩] at hlt
      exact absurd hlt (by simp)
  have hlim2 : Tendsto (fun t : ℝ => ((q - μ * (t * (y - x)) : ℝ) : EReal)) (𝓝[<] (1 : ℝ))
      (𝓝 (((q - μ * (1 * (y - x)) : ℝ) : EReal))) := by
    have hcont : Continuous fun t : ℝ => ((q - μ * (t * (y - x)) : ℝ) : EReal) :=
      _root_.EReal.continuous_coe_iff.2 (by fun_prop)
    exact (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hle := le_of_tendsto_of_tendsto hseg hlim2 hest
  rwa [one_mul] at hle

/-- **Right-continuity of `f'₊`.** For a closed proper convex function on the line the right
derivative is the limit of its own values from the right, in the monotone sense
`f'₊(x) = ⨅ {f'₊(z) | z > x}`. -/
theorem iInf_rightDeriv_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    ⨅ z ∈ Ioi x, rightDeriv f z = rightDeriv f x := by
  refine le_antisymm ?_ (le_iInf₂ fun z hz => monotone_rightDeriv hf.convex hf.proper hz.le)
  rcases em (∃ w, x < w ∧ f w < ⊤) with hex | hex
  swap
  · rw [rightDeriv_of_not_exists hex]; exact le_top
  obtain ⟨w₀, hw₀, hfw₀⟩ := hex
  obtain ⟨q₀, hq₀⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot w₀) hfw₀
  by_contra hcon
  obtain ⟨μ, hμ₁, hμ₂⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 (not_le.1 hcon)
  have hμ : ∀ z, x < z → (μ : EReal) < rightDeriv f z := fun z hz =>
    lt_of_lt_of_le hμ₂ (iInf₂_le z hz)
  have hx : f x < ⊤ :=
    lt_of_le_of_lt (le_coe_of_lt_rightDeriv hf hw₀ hq₀ hμ) (_root_.EReal.coe_lt_top _)
  obtain ⟨p, hp⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x) hx
  refine absurd hμ₁ (not_lt.2 ?_)
  rw [rightDeriv_eq_dirDeriv hx (hf.proper.ne_bot x)]
  refine le_dirDeriv fun a ha => ?_
  rw [show x + a • (1 : ℝ) = x + a by rw [smul_eq_mul]; ring]
  rcases lt_or_ge (f (x + a)) ⊤ with hfa | hfa
  · obtain ⟨q, hq⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot _) hfa
    have hbound := le_coe_of_lt_rightDeriv hf (by linarith : x < x + a) hq hμ
    rw [hp, _root_.EReal.coe_le_coe_iff] at hbound
    rw [hp, hq, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div, _root_.EReal.coe_le_coe_iff,
      le_div_iff₀ ha]
    nlinarith
  · rw [top_le_iff.1 hfa, hp, _root_.EReal.top_sub_coe,
      _root_.EReal.top_div_of_pos_ne_top (by exact_mod_cast ha) (_root_.EReal.coe_ne_top a)]
    exact le_top

/-- **The estimate behind the left-hand limit formulas**, the mirror image of
`le_coe_of_lt_rightDeriv`. -/
theorem le_coe_of_leftDeriv_lt (hf : ClosedProperConvexFn f) {y : ℝ} (hyx : y < x) {q : ℝ}
    (hq : f y = (q : EReal)) {μ : ℝ} (hμ : ∀ z, z < x → leftDeriv f z < (μ : EReal)) :
    f x ≤ ((q + μ * (x - y) : ℝ) : EReal) := by
  have hydom : y ∈ dom f := mem_dom.2 (by rw [hq]; exact _root_.EReal.coe_lt_top q)
  have hseg := tendsto_along_segment_of_closed_proper hf hydom x
  have hzeq : ∀ t : ℝ, (1 - t) • y + t • x = y + t * (x - y) := by
    intro t; rw [smul_eq_mul, smul_eq_mul]; ring
  have hest : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      f ((1 - t) • y + t • x) ≤ ((q + μ * (t * (x - y)) : ℝ) : EReal) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with t ht1 ht0
    have ht1' : t < 1 := ht1
    rw [hzeq t]
    set w : ℝ := y + t * (x - y) with hw
    have hyw : y < w := by rw [hw]; nlinarith
    have hwx : w < x := by rw [hw]; nlinarith
    have hd : (0 : ℝ) < t * (x - y) := by nlinarith
    have hgap : w - y = t * (x - y) := by rw [hw]; ring
    have hlt := hμ w hwx
    rcases lt_or_ge (f w) ⊤ with hfw | hfw
    · obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot w) hfw
      rw [leftDeriv_eq_neg_dirDeriv hfw (hf.proper.ne_bot w)] at hlt
      have hslope := dirDeriv_neg_one_le_slope hyw hq hr
      rw [hgap] at hslope
      have hneg : ((-((q - r) / (t * (x - y))) : ℝ) : EReal) < (μ : EReal) := by
        refine lt_of_le_of_lt ?_ hlt
        rw [_root_.EReal.coe_neg]
        exact _root_.EReal.neg_le_neg_iff.2 hslope
      rw [_root_.EReal.coe_lt_coe_iff, neg_lt, lt_div_iff₀ hd] at hneg
      rw [hr, _root_.EReal.coe_le_coe_iff]
      linarith
    · rw [leftDeriv_eq_top_of_eq_top (top_le_iff.1 hfw)
        ⟨y, hyw, by rw [hq]; exact _root_.EReal.coe_lt_top q⟩] at hlt
      exact absurd hlt (by simp)
  have hlim2 : Tendsto (fun t : ℝ => ((q + μ * (t * (x - y)) : ℝ) : EReal)) (𝓝[<] (1 : ℝ))
      (𝓝 (((q + μ * (1 * (x - y)) : ℝ) : EReal))) := by
    have hcont : Continuous fun t : ℝ => ((q + μ * (t * (x - y)) : ℝ) : EReal) :=
      _root_.EReal.continuous_coe_iff.2 (by fun_prop)
    exact (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hle := le_of_tendsto_of_tendsto hseg hlim2 hest
  rwa [one_mul] at hle

/-- **Left-continuity of `f'₋`**: `f'₋(x) = ⨆ {f'₋(z) | z < x}` for a closed proper convex
function on the line. -/
theorem iSup_leftDeriv_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    ⨆ z ∈ Iio x, leftDeriv f z = leftDeriv f x := by
  refine le_antisymm (iSup₂_le fun z hz => monotone_leftDeriv hf.convex hf.proper hz.le) ?_
  rcases em (∃ w, w < x ∧ f w < ⊤) with hex | hex
  swap
  · rw [leftDeriv_of_not_exists hex]; exact bot_le
  obtain ⟨w₀, hw₀, hfw₀⟩ := hex
  obtain ⟨q₀, hq₀⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot w₀) hfw₀
  by_contra hcon
  obtain ⟨μ, hμ₁, hμ₂⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 (not_le.1 hcon)
  have hμ : ∀ z, z < x → leftDeriv f z < (μ : EReal) := by
    intro z hz
    refine lt_of_le_of_lt ?_ hμ₁
    exact le_iSup₂ (f := fun z (_ : z ∈ Iio x) => leftDeriv f z) z hz
  have hx : f x < ⊤ :=
    lt_of_le_of_lt (le_coe_of_leftDeriv_lt hf hw₀ hq₀ hμ) (_root_.EReal.coe_lt_top _)
  obtain ⟨p, hp⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x) hx
  refine absurd hμ₂ (not_lt.2 ?_)
  rw [leftDeriv_eq_neg_dirDeriv hx (hf.proper.ne_bot x)]
  have hkey : ((-μ : ℝ) : EReal) ≤ dirDeriv f x (-1) := by
    refine le_dirDeriv fun a ha => ?_
    rw [show x + a • (-1 : ℝ) = x - a by rw [smul_eq_mul]; ring]
    rcases lt_or_ge (f (x - a)) ⊤ with hfa | hfa
    · obtain ⟨q, hq⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot _) hfa
      have hbound := le_coe_of_leftDeriv_lt hf (by linarith : x - a < x) hq hμ
      rw [hp, _root_.EReal.coe_le_coe_iff] at hbound
      rw [hp, hq, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div, _root_.EReal.coe_le_coe_iff,
        le_div_iff₀ ha]
      nlinarith
    · rw [top_le_iff.1 hfa, hp, _root_.EReal.top_sub_coe,
        _root_.EReal.top_div_of_pos_ne_top (by exact_mod_cast ha) (_root_.EReal.coe_ne_top a)]
      exact le_top
  have h2 := _root_.EReal.neg_le_neg_iff.2 hkey
  rwa [← _root_.EReal.coe_neg, neg_neg] at h2

/-- **The crossed limit formula**: the *left* derivative also has `f'₊(x)` as its limit from the
right. -/
theorem iInf_leftDeriv_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    ⨅ z ∈ Ioi x, leftDeriv f z = rightDeriv f x := by
  refine le_antisymm ?_ (le_iInf₂ fun z hz => rightDeriv_le_leftDeriv hf.proper hz)
  rw [← iInf_rightDeriv_Ioi hf x]
  exact iInf₂_mono fun z _ => leftDeriv_le_rightDeriv hf.convex hf.proper z

/-- **The crossed limit formula**: the *right* derivative has `f'₋(x)` as its limit from the
left. -/
theorem iSup_rightDeriv_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    ⨆ z ∈ Iio x, rightDeriv f z = leftDeriv f x := by
  refine le_antisymm (iSup₂_le fun z hz => rightDeriv_le_leftDeriv hf.proper hz) ?_
  rw [← iSup_leftDeriv_Iio hf x]
  exact iSup₂_mono fun z _ => leftDeriv_le_rightDeriv hf.convex hf.proper z

/-! ### Rockafellar's four limit formulas, as limits -/

/-- `lim_{z ↓ x} f'₊(z) = f'₊(x)`. -/
theorem tendsto_rightDeriv_nhdsWithin_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (rightDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) := by
  rw [← iInf_rightDeriv_Ioi hf x]
  exact tendsto_nhdsWithin_Ioi_of_monotone (monotone_rightDeriv hf.convex hf.proper) x

/-- `lim_{z ↑ x} f'₊(z) = f'₋(x)`. -/
theorem tendsto_rightDeriv_nhdsWithin_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (rightDeriv f) (𝓝[<] x) (𝓝 (leftDeriv f x)) := by
  rw [← iSup_rightDeriv_Iio hf x]
  exact tendsto_nhdsWithin_Iio_of_monotone (monotone_rightDeriv hf.convex hf.proper) x

/-- `lim_{z ↓ x} f'₋(z) = f'₊(x)`. -/
theorem tendsto_leftDeriv_nhdsWithin_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (leftDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) := by
  rw [← iInf_leftDeriv_Ioi hf x]
  exact tendsto_nhdsWithin_Ioi_of_monotone (monotone_leftDeriv hf.convex hf.proper) x

/-- `lim_{z ↑ x} f'₋(z) = f'₋(x)`. -/
theorem tendsto_leftDeriv_nhdsWithin_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (leftDeriv f) (𝓝[<] x) (𝓝 (leftDeriv f x)) := by
  rw [← iSup_leftDeriv_Iio hf x]
  exact tendsto_nhdsWithin_Iio_of_monotone (monotone_leftDeriv hf.convex hf.proper) x

end Limits

/-! ### A nondecreasing function between the two derivatives -/

section Determination

variable {f g : ℝ → EReal}

/-- Any `φ` squeezed between the two one-sided derivatives is nondecreasing — immediately from
`f'₊(y) ≤ f'₋(z)` for `y < z`. -/
theorem monotone_of_leftDeriv_le_of_le_rightDeriv (hp : Proper f) {φ : ℝ → EReal}
    (h₁ : ∀ z, leftDeriv f z ≤ φ z) (h₂ : ∀ z, φ z ≤ rightDeriv f z) : Monotone φ := by
  intro y z hyz
  rcases eq_or_lt_of_le hyz with rfl | hlt
  · exact le_rfl
  exact (h₂ y).trans ((rightDeriv_le_leftDeriv hp hlt).trans (h₁ z))

/-- **`φ` determines `f'₊`**: any nondecreasing `φ` between `f'₋` and `f'₊` has `f'₊` as its limit
from the right. Rockafellar's remark between Theorems 24.1 and 24.2. -/
theorem iInf_Ioi_eq_rightDeriv (hf : ClosedProperConvexFn f) {φ : ℝ → EReal}
    (h₁ : ∀ z, leftDeriv f z ≤ φ z) (h₂ : ∀ z, φ z ≤ rightDeriv f z) (x : ℝ) :
    ⨅ z ∈ Ioi x, φ z = rightDeriv f x := by
  refine le_antisymm ?_ ?_
  · rw [← iInf_rightDeriv_Ioi hf x]
    exact iInf₂_mono fun z _ => h₂ z
  · rw [← iInf_leftDeriv_Ioi hf x]
    exact iInf₂_mono fun z _ => h₁ z

/-- **`φ` determines `f'₋`**: it has `f'₋` as its limit from the left. -/
theorem iSup_Iio_eq_leftDeriv (hf : ClosedProperConvexFn f) {φ : ℝ → EReal}
    (h₁ : ∀ z, leftDeriv f z ≤ φ z) (h₂ : ∀ z, φ z ≤ rightDeriv f z) (x : ℝ) :
    ⨆ z ∈ Iio x, φ z = leftDeriv f x := by
  refine le_antisymm ?_ ?_
  · rw [← iSup_rightDeriv_Iio hf x]
    exact iSup₂_mono fun z _ => h₂ z
  · rw [← iSup_leftDeriv_Iio hf x]
    exact iSup₂_mono fun z _ => h₁ z

/-- Two proper functions on the line with the same one-sided derivatives have the same
subdifferential — the subdifferential is the interval between them. -/
theorem subgradientRel_eq_of_deriv_eq (hpf : Proper f) (hpg : Proper g)
    (hr : ∀ x, rightDeriv f x = rightDeriv g x) (hl : ∀ x, leftDeriv f x = leftDeriv g x) :
    subgradientRel (innerₗ ℝ) f = subgradientRel (innerₗ ℝ) g := by
  ext p
  change p.2 ∈ subgradient (innerₗ ℝ) f p.1 ↔ p.2 ∈ subgradient (innerₗ ℝ) g p.1
  rw [mem_subgradient_iff_le_rightDeriv hpf, mem_subgradient_iff_le_rightDeriv hpg, hr, hl]

/-- **Two closed proper convex functions on the line with the same one-sided derivatives differ by
a constant.** -/
theorem exists_eq_add_coe_of_deriv_eq (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    (hr : ∀ x, rightDeriv f x = rightDeriv g x) (hl : ∀ x, leftDeriv f x = leftDeriv g x) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) := by
  have : IsCompatiblePairing ((innerₗ ℝ).flip) := by rw [flip_innerₗ]; infer_instance
  exact eq_add_coe_of_subgradientRel_subset hf hg
    (subgradientRel_eq_of_deriv_eq hf.proper hg.proper hr hl).subset

/-- **Rockafellar, Theorem 24.2**, uniqueness clause: a nondecreasing `φ` pins down a closed
proper convex function on the line up to an additive constant. -/
theorem exists_eq_add_coe_of_le_le (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    {φ : ℝ → EReal} (hf₁ : ∀ z, leftDeriv f z ≤ φ z) (hf₂ : ∀ z, φ z ≤ rightDeriv f z)
    (hg₁ : ∀ z, leftDeriv g z ≤ φ z) (hg₂ : ∀ z, φ z ≤ rightDeriv g z) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) :=
  exists_eq_add_coe_of_deriv_eq hf hg
    (fun x => by rw [← iInf_Ioi_eq_rightDeriv hf hf₁ hf₂ x, iInf_Ioi_eq_rightDeriv hg hg₁ hg₂ x])
    (fun x => by rw [← iSup_Iio_eq_leftDeriv hf hf₁ hf₂ x, iSup_Iio_eq_leftDeriv hg hg₁ hg₂ x])

end Determination

end Tdaf.ConvexAnalysis
