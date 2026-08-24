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
countable set, and that derivative is continuous and nondecreasing there. **Theorem 25.4**: in any
fixed direction `y`, the two-sided directional derivative exists exactly where `x ↦ f'(x; y)` is
continuous, and that happens on a dense subset of `int (dom f)`.

## Main results

* `leftDeriv_eq_rightDeriv_of_continuousAt`, `continuousAt_rightDeriv_iff` — **Theorem 24.1** read
  as a continuity criterion: `f'₊` is continuous at `x` exactly when `f'₋(x) = f'₊(x)`.
* `countable_leftDeriv_ne_rightDeriv` — the jump set of `f'₊` is countable.
* `differentiableAtFn_iff_leftDeriv_eq_rightDeriv` — on the line, differentiability at an interior
  point of `dom f` *is* the equality of the two one-sided derivatives.
* `countable_not_differentiableAtFn`, `continuousAt_rightDeriv_of_differentiableAtFn`,
  `subset_closure_differentiableAtFn` — **Theorem 25.3**, its three assertions.
* `dirDeriv_lineRestrict` — the directional derivative of `t ↦ f (x + t • y)` is the directional
  derivative of `f` along the line.
* `continuousAt_dirDeriv_iff` — **Theorem 25.4**, first assertion: on `int (dom f)`, continuity of
  `x ↦ f'(x; y)` is exactly the existence of the two-sided derivative `f'(x; y) = -f'(x; -y)`.
* `subset_closure_twoSided_dirDeriv` — **Theorem 25.4**, density.

## Design notes

**`f'₊` is the derivative, and it is a function on the whole line.** Rockafellar's `f'` is defined
only on `D`, so his continuity assertion is "continuous relative to `D`"; here the object is
`rightDeriv f`, defined everywhere and agreeing with `f'` on `D`, and what Theorem 24.1 proves is
the *stronger* `ContinuousAt (rightDeriv f) x` for `x ∈ D`. Monotonicity is likewise global
(`monotone_rightDeriv`), so no restricted statement is needed for it either.

**Countability comes from Mathlib, not from a jump argument.** `Monotone.countable_not_continuousAt`
covers a monotone map into any second-countable order topology, and `EReal` is one. What it is fed
is the *easy* half of the continuity criterion — continuity of `f'₊` at `x` forces
`f'₋(x) = f'₊(x)` — and that half needs neither closedness of `f` nor the limit formulas: the chain

```
⨆ {f'₊(z) | z < x} ≤ f'₋(x) ≤ f'₊(x)
```

collapses as soon as the left end equals `f'₊(x)`, and the two inequalities are
`rightDeriv_le_leftDeriv` (properness only) and `leftDeriv_le_rightDeriv`. Closedness is needed
only for the converse, where the limit formulas of §24 come in.

**Theorem 25.4 needs no one-dimensional limit theory, and no `y ≠ 0`.** Rockafellar identifies
`liminf_{z → x} f'(z; y)` with `-f'(x; -y)` by restricting to the line and invoking Theorem 24.1.
The inequality that is actually used is available for free at every `λ > 0`:

```
f'(x - λ y; y) ≤ (f x - f (x - λ y)) / λ ≤ -f'(x; -y),
```

the first step being one term of the defining infimum at `x - λ y` and the second one term of the
defining infimum at `x` in the direction `-y`. Continuity at `x` then transports the bound to
`f'(x; y)`, and Theorem 23.1 supplies the opposite inequality. The other direction is Corollary
24.5.1 applied twice, at `y` and at `-y`. The hypothesis `y ≠ 0` is never used — for `y = 0` both
sides of the equivalence hold trivially.

**Density is Theorem 25.3 on a line, not a measure-zero argument.** Restricting `f` to the line
`t ↦ x + t y` gives a proper convex function of one variable whose one-sided derivatives are
`f'(x + t y; ±y)`, so the countability of *its* jump set already places points of `D` arbitrarily
close to `x`. This replaces Rockafellar's route through Lebesgue measure, and it is why the density
clause here needs neither finite dimension nor the `Sₖ` decomposition.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §25 (Theorems 25.3 and
  25.4, except the measure-zero clause of the latter).
-/

open Set Filter Topology

namespace Tdaf.ConvexAnalysis

/-! ### Theorem 24.1 as a continuity criterion -/

section Line

variable {f : ℝ → EReal} {x : ℝ}

/-- **Continuity of `f'₊` at `x` forces the two-sided derivative.** Monotonicity gives
`f'₊(z) → ⨆ {f'₊(z) | z < x}` as `z ↑ x`, so continuity identifies that supremum with `f'₊(x)`;
and every `f'₊(z)` with `z < x` is below `f'₋(x)` (`rightDeriv_le_leftDeriv`, which needs only
properness). The sandwich `f'₊(x) ≤ f'₋(x) ≤ f'₊(x)` closes it.

Unlike the converse this needs no closedness, which is what makes Theorem 25.3's countability and
density clauses hold for every proper convex function. -/
theorem leftDeriv_eq_rightDeriv_of_continuousAt (hf : ConvexFn f) (hp : Proper f)
    (hc : ContinuousAt (rightDeriv f) x) : leftDeriv f x = rightDeriv f x := by
  have hsup : ⨆ z ∈ Iio x, rightDeriv f z = rightDeriv f x :=
    tendsto_nhds_unique (tendsto_nhdsWithin_Iio_of_monotone (monotone_rightDeriv hf hp) x)
      (Filter.Tendsto.mono_left hc nhdsWithin_le_nhds)
  refine le_antisymm (leftDeriv_le_rightDeriv hf hp x) ?_
  rw [← hsup]
  exact iSup₂_le fun z hz => rightDeriv_le_leftDeriv hp hz

/-- **Rockafellar, Theorem 24.1**, read as a continuity criterion: for a closed proper convex
function on the line, the nondecreasing function `f'₊` is continuous at `x` exactly when it agrees
with `f'₋` there.

The converse direction is where closedness enters: it is the pair of one-sided limit formulas of
§24, `f'₊(z) → f'₊(x)` as `z ↓ x` and `f'₊(z) → f'₋(x)` as `z ↑ x`, glued along
`𝓝 x = (𝓝[<] x ⊔ 𝓝[>] x) ⊔ pure x`. -/
theorem continuousAt_rightDeriv_iff (hf : ClosedProperConvexFn f) (x : ℝ) :
    ContinuousAt (rightDeriv f) x ↔ leftDeriv f x = rightDeriv f x := by
  refine ⟨leftDeriv_eq_rightDeriv_of_continuousAt hf.convex hf.proper, fun h => ?_⟩
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
order topology, so `Monotone.countable_not_continuousAt` applies;
`leftDeriv_eq_rightDeriv_of_continuousAt` places the set where the one-sided derivatives differ
inside the discontinuity set. -/
theorem countable_leftDeriv_ne_rightDeriv (hf : ConvexFn f) (hp : Proper f) :
    {x : ℝ | leftDeriv f x ≠ rightDeriv f x}.Countable := by
  refine Set.Countable.mono ?_ (monotone_rightDeriv hf hp).countable_not_continuousAt
  intro z hz
  have hz' : leftDeriv f z ≠ rightDeriv f z := hz
  exact fun hcon => hz' (leftDeriv_eq_rightDeriv_of_continuousAt hf hp hcon)

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
    have hneg : y₀ (-1 : ℝ) = -y₀ (1 : ℝ) := by rw [← map_neg]
    rw [hneg, neg_neg]
  · intro h
    exact ⟨(rightDeriv f x).toReal • ContinuousLinearMap.id ℝ ℝ,
      hasGradientAt_of_dirDeriv_eq hf hfx.ne hfb fun v => by
        rw [dirDeriv_eq_of_leftDeriv_eq_rightDeriv hf hp hx h v]
        norm_num⟩

/-! ### Theorem 25.3 -/

/-- **Rockafellar, Theorem 25.3**, first assertion: a convex function on the line is differentiable
at all but countably many points of the interior of its effective domain.

Rockafellar's `I` is an open interval on which `f` is finite and his first move is to extend `f` to
a closed proper convex function on `ℝ`; that extension is unnecessary here, because the countability
half of the continuity criterion needs no closedness. -/
theorem countable_not_differentiableAtFn (hf : ConvexFn f) (hp : Proper f) :
    {x ∈ interior (dom f) | ¬DifferentiableAtFn f x}.Countable := by
  refine Set.Countable.mono ?_ (countable_leftDeriv_ne_rightDeriv hf hp)
  rintro z ⟨hz, hzd⟩
  exact fun hcon => hzd ((differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf hp hz).2 hcon)

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
theorem subset_closure_differentiableAtFn (hf : ConvexFn f) (hp : Proper f) :
    interior (dom f) ⊆ closure {z : ℝ | DifferentiableAtFn f z} := by
  intro z hz
  rw [mem_closure_iff]
  intro U hU hzU
  obtain ⟨w, hw, hwU⟩ :=
    (Set.Countable.dense_compl ℝ (countable_leftDeriv_ne_rightDeriv hf hp)).exists_mem_open
      (hU.inter isOpen_interior) ⟨z, hzU, hz⟩
  exact ⟨w, hwU.1,
    (differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf hp hwU.2).2 (not_not.1 hw)⟩

end Line

/-! ### Restriction to a line -/

section Restrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {x y : E}

/-- The restriction of `f` to the line `t ↦ x + t • y` is convex. -/
theorem convexFn_lineRestrict (hf : ConvexFn f) (x y : E) :
    ConvexFn fun t : ℝ => f (x + t • y) := by
  refine convexFn_of_epi_combo fun t₁ t₂ μ ν h₁ h₂ a b ha hb hab => ?_
  have hpt : x + (a • t₁ + b • t₂) • y = a • (x + t₁ • y) + b • (x + t₂ • y) := by
    rw [smul_eq_mul, smul_eq_mul]
    match_scalars <;> linarith [hab]
  rw [hpt]
  exact hf.epi_combo h₁ h₂ ha hb hab

/-- The restriction of `f` to a line through a point of `dom f` is proper. -/
theorem proper_lineRestrict (hp : Proper f) (hx : x ∈ dom f) (y : E) :
    Proper fun t : ℝ => f (x + t • y) :=
  ⟨⟨0, by simpa using hx⟩, fun t => hp.ne_bot _⟩

/-- **The one-dimensional restriction computes the directional derivative along the line.** Both
sides are the same infimum of difference quotients, because `x + (t + a v) y = (x + t y) + a (v y)`.
This is what lets §25's one-dimensional theory be applied in a fixed direction. -/
theorem dirDeriv_lineRestrict (f : E → EReal) (x y : E) (t v : ℝ) :
    dirDeriv (fun s : ℝ => f (x + s • y)) t v = dirDeriv f (x + t • y) (v • y) := by
  have harg : ∀ a : ℝ, x + (t + a • v) • y = x + t • y + a • (v • y) := by
    intro a
    rw [smul_eq_mul, smul_smul]
    module
  simp only [dirDeriv_apply, harg]

end Restrict

/-! ### Theorem 25.4 -/

section TwoSided

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {x : E}

/-- **Corollary 24.5.1 in one variable**: for a fixed direction `y`, the function `z ↦ f'(z; y)` is
upper semicontinuous at every interior point of `dom f`. This is
`upperSemicontinuousAt_dirDeriv` restricted to the slice `z ↦ (z, y)`. -/
theorem upperSemicontinuousAt_dirDeriv_left [FiniteDimensional ℝ E] (hf : ConvexFn f)
    (hp : Proper f) (hx : x ∈ interior (dom f)) (y : E) :
    UpperSemicontinuousAt (fun z => dirDeriv f z y) x := by
  intro c hc
  have hcont : Continuous fun z : E => (z, y) := by fun_prop
  exact (hcont.tendsto x).eventually (upperSemicontinuousAt_dirDeriv hf hp hx y c hc)

/-- **The backward step of Rockafellar's `liminf` identity, without any limit.** For every `λ > 0`,

```
f'(x - λ y; y) ≤ (f x - f (x - λ y)) / λ ≤ -f'(x; -y).
```

The first inequality is the term of the defining infimum at `x - λ y` with step `λ`, which lands
exactly on `x`; the second is the term of the defining infimum at `x` in the direction `-y` with the
same step, negated. No convexity and no interiority are used — only properness, to keep `f` away
from `-∞`. -/
theorem dirDeriv_sub_smul_le (hp : Proper f) (hfx : f x < ⊤) (y : E) {l : ℝ} (hl : 0 < l) :
    dirDeriv f (x - l • y) y ≤ -dirDeriv f x (-y) := by
  rcases eq_or_lt_of_le (le_top : f (x - l • y) ≤ ⊤) with hu | hu
  · rw [dirDeriv_eq_bot_of_eq_top hu]
    exact bot_le
  obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hfx
  obtain ⟨s, hs⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot (x - l • y)) hu
  have h1 : dirDeriv f (x - l • y) y ≤ (((r - s) / l : ℝ) : EReal) := by
    have hq := dirDeriv_le f (x - l • y) y hl
    rwa [show x - l • y + l • y = x from by abel, hr, hs, ← _root_.EReal.coe_sub,
      ← _root_.EReal.coe_div] at hq
  have h2 : dirDeriv f x (-y) ≤ (((s - r) / l : ℝ) : EReal) := by
    have hq := dirDeriv_le f x (-y) hl
    rwa [show x + l • (-y) = x - l • y from by module, hr, hs, ← _root_.EReal.coe_sub,
      ← _root_.EReal.coe_div] at hq
  refine h1.trans ?_
  have h3 := _root_.EReal.neg_le_neg_iff.2 h2
  rwa [← _root_.EReal.coe_neg, show -((s - r) / l) = (r - s) / l from by ring] at h3

/-- **Rockafellar, Theorem 25.4**, first assertion: on the interior of `dom f`, the set where the
ordinary two-sided directional derivative in the direction `y` exists is exactly the set where
`x ↦ f'(x; y)` is continuous.

Continuity implies the two-sided derivative because `dirDeriv_sub_smul_le` bounds `f'(z; y)` by
`-f'(x; -y)` all along the ray approaching `x` from the direction `-y`, and Theorem 23.1 gives the
reverse inequality. The converse is Corollary 24.5.1 used twice: upper semicontinuity at `y`
handles limits from above, and upper semicontinuity at `-y` combined with `-f'(z; -y) ≤ f'(z; y)`
handles limits from below.

Rockafellar's `y ≠ 0` is not needed: at `y = 0` both sides hold. -/
theorem continuousAt_dirDeriv_iff [FiniteDimensional ℝ E] (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) (y : E) :
    ContinuousAt (fun z => dirDeriv f z y) x ↔ dirDeriv f x y = -dirDeriv f x (-y) := by
  have hfx : f x < ⊤ := mem_dom.1 (interior_subset hx)
  constructor
  · intro hc
    refine le_antisymm ?_ (neg_dirDeriv_neg_le hf hfx.ne (hp.ne_bot x) y)
    have hray : Tendsto (fun l : ℝ => x - l • y) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      have hcont : Continuous fun l : ℝ => x - l • y := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hc' : Tendsto (fun z : E => dirDeriv f z y) (𝓝 x) (𝓝 (dirDeriv f x y)) := hc
    have hlim : Tendsto (fun l : ℝ => dirDeriv f (x - l • y) y) (𝓝[>] (0 : ℝ))
        (𝓝 (dirDeriv f x y)) := hc'.comp hray
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with l hl
    exact dirDeriv_sub_smul_le hp hfx y (mem_Ioi.1 hl)
  · intro h
    refine tendsto_order.2 ⟨fun a ha => ?_, fun c hc => ?_⟩
    · have ha' : a < dirDeriv f x y := ha
      rw [h] at ha'
      have hev := upperSemicontinuousAt_dirDeriv_left hf hp hx (-y) (-a)
        (_root_.EReal.lt_neg_of_lt_neg ha')
      filter_upwards [hev, isOpen_interior.mem_nhds hx] with z hz hzi
      have hz' : dirDeriv f z (-y) < -a := hz
      have hzt : f z < ⊤ := mem_dom.1 (interior_subset hzi)
      exact lt_of_lt_of_le (_root_.EReal.lt_neg_of_lt_neg hz')
        (neg_dirDeriv_neg_le hf hzt.ne (hp.ne_bot z) y)
    · have hc' : dirDeriv f x y < c := hc
      exact upperSemicontinuousAt_dirDeriv_left hf hp hx y c hc'

/-- **Rockafellar, Theorem 25.4**, density: the points of `int (dom f)` at which the two-sided
directional derivative in the direction `y` exists are dense in `int (dom f)`.

Rockafellar deduces this from the complement having Lebesgue measure zero. It is cheaper on a
line: `t ↦ f (x + t • y)` is a proper convex function of one variable whose one-sided derivatives
at `t` are `f'(x + t y; ±y)` (`dirDeriv_lineRestrict`), so `countable_leftDeriv_ne_rightDeriv`
already puts good points of the line arbitrarily close to `t = 0`. Finite-dimensionality plays no
role here. -/
theorem subset_closure_twoSided_dirDeriv (hf : ConvexFn f) (hp : Proper f) (y : E) :
    interior (dom f) ⊆
      closure {z ∈ interior (dom f) | dirDeriv f z y = -dirDeriv f z (-y)} := by
  intro x hx
  rw [mem_closure_iff]
  intro U hU hxU
  have hgc : ConvexFn fun t : ℝ => f (x + t • y) := convexFn_lineRestrict hf x y
  have hgp : Proper fun t : ℝ => f (x + t • y) :=
    proper_lineRestrict hp (interior_subset hx) y
  have hVopen : IsOpen {t : ℝ | x + t • y ∈ U ∩ interior (dom f)} := by
    have hcont : Continuous fun t : ℝ => x + t • y := by fun_prop
    exact hcont.isOpen_preimage _ (hU.inter isOpen_interior)
  have hV0 : (0 : ℝ) ∈ {t : ℝ | x + t • y ∈ U ∩ interior (dom f)} := by
    simpa using And.intro hxU hx
  obtain ⟨t, ht, htV⟩ :=
    (Set.Countable.dense_compl ℝ (countable_leftDeriv_ne_rightDeriv hgc hgp)).exists_mem_open
      hVopen ⟨0, hV0⟩
  have hgt : f (x + t • y) < ⊤ := mem_dom.1 (interior_subset htV.2)
  have hgb : f (x + t • y) ≠ ⊥ := hp.ne_bot _
  have heq : leftDeriv (fun s : ℝ => f (x + s • y)) t
      = rightDeriv (fun s : ℝ => f (x + s • y)) t := not_not.1 ht
  rw [rightDeriv_eq_dirDeriv hgt hgb, leftDeriv_eq_neg_dirDeriv hgt hgb, dirDeriv_lineRestrict,
    dirDeriv_lineRestrict] at heq
  simp only [one_smul, neg_one_smul] at heq
  exact ⟨x + t • y, htV.1, htV.2, heq.symm⟩

end TwoSided

end Tdaf.ConvexAnalysis
