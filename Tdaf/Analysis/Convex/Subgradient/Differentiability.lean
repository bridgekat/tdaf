/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Order.Monotone
import Tdaf.Analysis.Convex.Subgradient.Convergence
import Tdaf.Analysis.Convex.Subgradient.Gradient
import Tdaf.Analysis.Convex.Subgradient.OneDim

/-!
# Where a convex function is differentiable

Rockafellar's §25, the part that reads the continuity theory of §24 as an existence theory for
derivatives. **Theorem 25.3**: a convex function on the line has a two-sided derivative off a
countable set, and that derivative is continuous and nondecreasing there.

## Main results

* `continuousAt_rightDeriv_iff` — **Theorem 24.1** read as a continuity criterion: `f'₊` is
  continuous at `x` exactly when `f'₋(x) = f'₊(x)`.
* `countable_leftDeriv_ne_rightDeriv` — the jump set of `f'₊` is countable.
* `differentiableAtFn_iff_leftDeriv_eq_rightDeriv` — on the line, differentiability at an interior
  point of `dom f` *is* the equality of the two one-sided derivatives.
* `countable_not_differentiableAtFn`, `continuousAt_rightDeriv_of_differentiableAtFn`,
  `subset_closure_differentiableAtFn` — **Theorem 25.3**, its three assertions.

## Design notes

**`f'₊` is the derivative, and it is a function on the whole line.** Rockafellar's `f'` is defined
only on `D`, so his continuity assertion is "continuous relative to `D`"; here the object is
`rightDeriv f`, defined everywhere and agreeing with `f'` on `D`, and what Theorem 24.1 proves is
the *stronger* `ContinuousAt (rightDeriv f) x` for `x ∈ D`. Monotonicity is likewise global
(`monotone_rightDeriv`), so no restricted statement is needed for it either.

**Countability comes from Mathlib, not from a jump argument.** `Monotone.countable_not_continuousAt`
covers a monotone map into any second-countable order topology, and `EReal` is one; the only work
is the criterion `continuousAt_rightDeriv_iff`, which is `tendsto_rightDeriv_nhdsWithin_Iio` and
`tendsto_rightDeriv_nhdsWithin_Ioi` together with the decomposition
`𝓝 x = (𝓝[<] x ⊔ 𝓝[>] x) ⊔ pure x`.

**Differentiability is the two-sided derivative, via Theorem 25.2.** On the line, `f'₋(x) = f'₊(x)`
makes `f'(x; ·)` the linear function `v ↦ c v`, so `hasGradientAt_of_dirDeriv_eq` upgrades it to
Fréchet differentiability; interiority of `x` in `dom f` is what makes `c` finite.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §25 (Theorem 25.3).
-/

open Set Filter Topology

namespace Tdaf.ConvexAnalysis

/-! ### Theorem 24.1 as a continuity criterion -/

section Line

variable {f : ℝ → EReal} {x : ℝ}

/-- **Rockafellar, Theorem 24.1**, read as a continuity criterion: for a closed proper convex
function on the line, the nondecreasing function `f'₊` is continuous at `x` exactly when it agrees
with `f'₋` there.

Both directions are the two one-sided limit formulas of §24: `f'₊` tends to `f'₊(x)` from the right
and to `f'₋(x)` from the left, and `𝓝 x` is the supremum of those two filters with `pure x`. -/
theorem continuousAt_rightDeriv_iff (hf : ClosedProperConvexFn f) (x : ℝ) :
    ContinuousAt (rightDeriv f) x ↔ leftDeriv f x = rightDeriv f x := by
  constructor
  · intro hc
    exact tendsto_nhds_unique (tendsto_rightDeriv_nhdsWithin_Iio hf x)
      (Filter.Tendsto.mono_left hc nhdsWithin_le_nhds)
  · intro h
    have h1 : Tendsto (rightDeriv f) (𝓝[<] x) (𝓝 (rightDeriv f x)) := by
      rw [← h]
      exact tendsto_rightDeriv_nhdsWithin_Iio hf x
    have h2 : Tendsto (rightDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) :=
      tendsto_rightDeriv_nhdsWithin_Ioi hf x
    have h3 : Tendsto (rightDeriv f) (pure x) (𝓝 (rightDeriv f x)) := tendsto_pure_nhds _ x
    have hsup : Tendsto (rightDeriv f) (𝓝[≠] x ⊔ pure x) (𝓝 (rightDeriv f x)) := by
      rw [← nhdsLT_sup_nhdsGT]
      exact (h1.sup h2).sup h3
    rwa [nhdsNE_sup_pure] at hsup

/-- **The jump set of `f'₊` is countable.** `f'₊` is nondecreasing and `EReal` is a second-countable
order topology, so `Monotone.countable_not_continuousAt` applies; the previous theorem identifies
its discontinuity set with the set where the two one-sided derivatives differ. -/
theorem countable_leftDeriv_ne_rightDeriv (hf : ClosedProperConvexFn f) :
    {x : ℝ | leftDeriv f x ≠ rightDeriv f x}.Countable := by
  refine Set.Countable.mono ?_ (monotone_rightDeriv hf.convex hf.proper).countable_not_continuousAt
  intro z hz
  have hz' : leftDeriv f z ≠ rightDeriv f z := hz
  exact fun hc => hz' ((continuousAt_rightDeriv_iff hf z).1 hc)

/-! ### The two-sided derivative on the line -/

/-- **On the line a two-sided derivative makes `f'(x; ·)` linear.** Positive homogeneity reduces
`f'(x; v)` to the two directions `±1`, where the values are `f'₊(x)` and `-f'₋(x)`; interiority of
`x` in `dom f` makes both real. -/
theorem dirDeriv_eq_of_leftDeriv_eq_rightDeriv (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) (h : leftDeriv f x = rightDeriv f x) (v : ℝ) :
    dirDeriv f x v = (((rightDeriv f x).toReal * v : ℝ) : EReal) := by
  obtain ⟨hbot, htop⟩ := rightDeriv_finite_of_mem_interior_dom hf hp hx
  set c : ℝ := (rightDeriv f x).toReal with hcdef
  have hrc : rightDeriv f x = (c : EReal) := (_root_.EReal.coe_toReal htop hbot).symm
  have hfx : f x < ⊤ := mem_dom.1 (interior_subset hx)
  have hfb : f x ≠ ⊥ := hp.ne_bot x
  have h1 : dirDeriv f x 1 = (c : EReal) := by rw [← rightDeriv_eq_dirDeriv hfx hfb, hrc]
  have hm1 : dirDeriv f x (-1) = ((-c : ℝ) : EReal) := by
    have hL := leftDeriv_eq_neg_dirDeriv hfx hfb
    rw [h, hrc] at hL
    rw [_root_.EReal.coe_neg, hL, neg_neg]
  rcases lt_trichotomy v 0 with hv | rfl | hv
  · have hvv : v = (-v) • (-1 : ℝ) := by rw [smul_eq_mul]; ring
    rw [hvv, posHomogeneous_dirDeriv f x (-v) (by linarith) (-1), hm1, EReal.coe_mul_coe]
    congr 1
    ring
  · rw [dirDeriv_zero hfx.ne hfb]
    simp
  · have hvv : v = v • (1 : ℝ) := by rw [smul_eq_mul]; ring
    rw [hvv, posHomogeneous_dirDeriv f x v hv 1, h1, EReal.coe_mul_coe]
    congr 1
    ring

/-- **Rockafellar, Theorems 25.2 and 25.3 together**: on the line, a convex function is
differentiable at an interior point of its effective domain exactly when its two one-sided
derivatives agree there.

Sufficiency is `hasGradientAt_of_dirDeriv_eq` fed with the linear `f'(x; ·)` produced by
`dirDeriv_eq_of_leftDeriv_eq_rightDeriv`; necessity reads that linear function at `±1`. -/
theorem differentiableAtFn_iff_leftDeriv_eq_rightDeriv (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) :
    DifferentiableAtFn f x ↔ leftDeriv f x = rightDeriv f x := by
  have hfx : f x < ⊤ := mem_dom.1 (interior_subset hx)
  have hfb : f x ≠ ⊥ := hp.ne_bot x
  constructor
  · rintro ⟨y₀, hy₀⟩
    have hd := hy₀.dirDeriv_eq hf
    rw [rightDeriv_eq_dirDeriv hfx hfb, leftDeriv_eq_neg_dirDeriv hfx hfb, hd 1, hd (-1),
      ← _root_.EReal.coe_neg]
    congr 1
    have : y₀ (-1 : ℝ) = -y₀ (1 : ℝ) := by rw [← map_neg]
    rw [this, neg_neg]
  · intro h
    exact ⟨(rightDeriv f x).toReal • ContinuousLinearMap.id ℝ ℝ,
      hasGradientAt_of_dirDeriv_eq hf hfx.ne hfb fun v => by
        rw [dirDeriv_eq_of_leftDeriv_eq_rightDeriv hf hp hx h v]
        norm_num⟩

/-! ### Theorem 25.3 -/

/-- **Rockafellar, Theorem 25.3**, first assertion: a convex function on the line is differentiable
at all but countably many points of the interior of its effective domain.

Rockafellar's `I` is an open interval on which `f` is finite; extending `f` by `+∞` makes it a
closed proper convex function whose `int (dom f)` contains `I`, which is his own first move. -/
theorem countable_not_differentiableAtFn (hf : ClosedProperConvexFn f) :
    {x ∈ interior (dom f) | ¬DifferentiableAtFn f x}.Countable := by
  refine Set.Countable.mono ?_ (countable_leftDeriv_ne_rightDeriv hf)
  rintro z ⟨hz, hzd⟩
  exact fun hcon =>
    hzd ((differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf.convex hf.proper hz).2 hcon)

/-- **Rockafellar, Theorem 25.3**, second assertion: the derivative is continuous where it exists.

This is stronger than the book's "continuous relative to `D`": `rightDeriv f` is defined on the
whole line and is continuous at `x` in the ordinary sense. -/
theorem continuousAt_rightDeriv_of_differentiableAtFn (hf : ClosedProperConvexFn f)
    (hx : x ∈ interior (dom f)) (hd : DifferentiableAtFn f x) :
    ContinuousAt (rightDeriv f) x :=
  (continuousAt_rightDeriv_iff hf x).2
    ((differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf.convex hf.proper hx).1 hd)

/-- **Rockafellar, Theorem 25.3**, third assertion: the points of differentiability are dense in
the interior of the effective domain.

A countable subset of `ℝ` has dense complement (`Set.Countable.dense_compl`), so every non-empty
open subset of `int (dom f)` meets the set where the two one-sided derivatives agree. -/
theorem subset_closure_differentiableAtFn (hf : ClosedProperConvexFn f) :
    interior (dom f) ⊆ closure {z : ℝ | DifferentiableAtFn f z} := by
  intro z hz
  rw [mem_closure_iff]
  intro U hU hzU
  obtain ⟨w, hw, hwU⟩ :=
    (Set.Countable.dense_compl ℝ (countable_leftDeriv_ne_rightDeriv hf)).exists_mem_open
      (hU.inter isOpen_interior) ⟨z, hzU, hz⟩
  refine ⟨w, hwU.1, ?_⟩
  exact (differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf.convex hf.proper hwU.2).2
    (not_not.1 hw)

end Line

end Tdaf.ConvexAnalysis
