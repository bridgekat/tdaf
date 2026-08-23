/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Tdaf.Analysis.Convex.Subgradient.Defs

/-!
# Gradients and the subdifferential

Rockafellar's §25, the part that does not need measure theory. **Theorem 25.1**: where a convex
function is differentiable, its gradient is its *only* subgradient, and the directional derivative
is the corresponding linear function; conversely, a linear directional derivative forces the
subdifferential to be a single point.

## Main results

* `subgradient_eq_singleton_of_dirDeriv_eq` — **Theorem 25.2**, sufficiency, in its algebraic
  form: if `f'(x; ·)` is the linear function `⟨·, y₀⟩` then `∂f x = {y₀}`.
* `clFn_dirDeriv_eq_of_subgradient_eq_singleton` — the converse at the level of closures: a
  single-valued subdifferential makes `cl f'(x; ·)` linear. This is Theorem 23.2 read backwards.
* `le_of_hasFDerivAt` — **Theorem 25.1**, the gradient inequality `f z ≥ f x + ⟨z - x, ∇f x⟩`.
* `subgradient_eq_singleton_of_hasFDerivAt` — **Theorem 25.1**: `∂f x = {∇f x}` at a point of
  differentiability of a convex function.
* `eq_of_mem_subgradient_of_hasFDerivAt` — the uniqueness half on its own; it needs no convexity.
* `dirDeriv_eq_of_hasFDerivAt` — **Theorem 25.2**, necessity: `f'(x; v) = ⟨v, ∇f x⟩`.
* `proper_of_eventuallyEq_coe`, `mem_interior_dom_of_eventuallyEq_coe` — **Corollary 25.1.1**.
* `HasGradientAt`, `DifferentiableAtFn` — `∇f x = f'` for an `EReal`-valued `f`, with the results
  above repackaged as `HasGradientAt.le`, `.subgradient_eq`, `.dirDeriv_eq`, `.mem_interior_dom`,
  `.proper` and `.unique`. This is the interface §26 uses.

## Design notes

**Two layers, two pairings.** The directional-derivative statements are algebraic and hold over an
arbitrary pairing `B`; uniqueness there needs the pairing to be separating in its second variable,
which is the hypothesis `Function.Injective B.flip`. The Fréchet statements are about a genuine
normed space and are stated for the canonical pairing `(topDualPairing ℝ E).flip`, where a
subgradient *is* a continuous linear functional and `∇f x` is `HasFDerivAt`'s `f'`.

**Differentiability of an `EReal`-valued function is expressed by a local real representative.**
`HasFDerivAt` needs a normed target, so a convex `f : E → EReal` is called differentiable at `x`
when there is a real-valued `g` with `f =ᶠ[𝓝 x] fun z => (g z : EReal)` and `HasFDerivAt g f' x`.
That is exactly Rockafellar's situation: his definition of `∇f x` presupposes `f x` finite, and
differentiability at `x` forces `f` to be finite near `x`, i.e. `x ∈ int (dom f)`
(`mem_interior_dom_of_eventuallyEq_coe`). Restricting instead to `f : E → ℝ` would lose §26, where
the interesting functions are `+∞` outside an open set.

**The proof of Theorem 25.1 never mentions `dirDeriv`.** Rockafellar routes it through
Theorem 23.2, but with a Fréchet derivative in hand the one-sided limit of the difference quotient
along a ray does everything: convexity bounds the quotient above by `f z - f x`, which gives
`∇f x ∈ ∂f x`, and the subgradient inequality bounds it below by `⟨v, y⟩` for any other subgradient
`y`, which gives `⟨v, y⟩ ≤ ⟨v, ∇f x⟩` for every `v` — and hence equality, by applying it to `-v`.
The uniqueness half therefore uses neither convexity nor properness.

## What is not here

**The sufficiency half of Theorem 25.2 is not formalised**, and it is not a mere transcription:
linearity of `f'(x; ·)` gives Gâteaux differentiability, and the upgrade to Fréchet
differentiability is a genuinely finite-dimensional argument (uniform convergence of the difference
quotients over the compact unit sphere). `dirDeriv_eq_of_hasFDerivAt` gives the necessity half, and
`subgradient_eq_singleton_of_dirDeriv_eq` gives what sufficiency is used for.

**Theorems 25.3–25.7 are not formalised.** Theorem 25.3 is one-dimensional and rests on
Theorem 24.1; Theorem 25.4 rests on Theorem 24.5; Theorem 25.5 (a.e. differentiability) is
Rademacher's theorem plus the continuity of `∇f`, which is Theorem 24.4 together with Theorem 25.1
but needs the measure-theoretic statement first; Theorems 25.6 and 25.7 rest on 25.5 and on §24's
convergence theory. Corollaries 25.1.2 and 25.1.3 are about exposed points of `epi f*` and need
§18's exposed-face theory in the `ℝ × E` picture.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §25 (Theorem 25.1,
  Corollary 25.1.1, and the necessity half of Theorem 25.2).
-/

open Set Filter Topology

namespace Tdaf.ConvexAnalysis

/-! ### The algebraic core: a linear directional derivative -/

section Linear

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E}

/-- **Rockafellar, Theorem 25.2**, sufficiency, algebraically: if the directional derivative
`f'(x; ·)` is the linear function `⟨·, y₀⟩`, then `y₀` is the unique subgradient of `f` at `x`.

This is Theorem 23.2 plus the observation that `⟨v, y⟩ ≤ ⟨v, y₀⟩` for *every* `v`, `-v` included,
forces `⟨·, y⟩ = ⟨·, y₀⟩`. The pairing must separate the points of `F`, which for
`(topDualPairing ℝ E).flip` is the injectivity of the coercion of a continuous functional to a
function. -/
theorem subgradient_eq_singleton_of_dirDeriv_eq (hsep : Function.Injective B.flip)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) {y₀ : F}
    (h : ∀ v : E, dirDeriv f x v = ((B v y₀ : ℝ) : EReal)) :
    subgradient B f x = {y₀} := by
  ext y
  rw [mem_subgradient_iff_le_dirDeriv ht hb, Set.mem_singleton_iff]
  constructor
  · intro hy
    refine hsep (LinearMap.ext fun v => ?_)
    have h₁ : B v y ≤ B v y₀ := by
      have hv := hy v
      rw [h v, _root_.EReal.coe_le_coe_iff] at hv
      exact hv
    have h₂ : B (-v) y ≤ B (-v) y₀ := by
      have hv := hy (-v)
      rw [h (-v), _root_.EReal.coe_le_coe_iff] at hv
      exact hv
    rw [map_neg, LinearMap.neg_apply, LinearMap.neg_apply] at h₂
    simp only [LinearMap.flip_apply]
    linarith
  · rintro rfl v
    rw [h v]

/-- The converse of Theorem 25.1 at the level of closures: if `∂f x` is a single point `y₀`, then
`cl f'(x; ·)` is the linear function `⟨·, y₀⟩`. This is the second half of Theorem 23.2, since the
support function of a singleton is a linear function. -/
theorem clFn_dirDeriv_eq_of_subgradient_eq_singleton [TopologicalSpace E] [ContinuousSMul ℝ E]
    [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [IsCompatiblePairing B] (hf : ConvexFn f)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) {y₀ : F} (h : subgradient B f x = {y₀}) :
    clFn (dirDeriv f x) = fun v => ((B v y₀ : ℝ) : EReal) := by
  rw [clFn_dirDeriv (B := B) hf ht hb, h, supportFn_singleton]
  rfl

end Linear

/-! ### Rays and difference quotients -/

section Frechet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {g : E → ℝ}
  {x : E} {f' : E →L[ℝ] ℝ}

/-- The ray `t ↦ x + t • v` tends to `x` as `t ↓ 0`. -/
theorem tendsto_ray_nhdsGT (x v : E) :
    Tendsto (fun t : ℝ => x + t • v) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
  have hc : Continuous fun t : ℝ => x + t • v := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The difference quotient along a ray converges to the derivative in that direction. This is the
only piece of calculus the section uses. -/
theorem tendsto_slope_ray_of_hasFDerivAt (hd : HasFDerivAt g f' x) (v : E) :
    Tendsto (fun t : ℝ => (g (x + t • v) - g x) / t) (𝓝[>] (0 : ℝ)) (𝓝 (f' v)) := by
  have hsmul : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) v
  have hcurve : HasDerivAt (fun t : ℝ => x + t • v) v 0 := HasDerivAt.const_add x hsmul
  have hd' : HasFDerivAt g f' ((fun t : ℝ => x + t • v) 0) := by simpa using hd
  have hcomp : HasDerivAt (fun t : ℝ => g (x + t • v)) (f' v) 0 := by
    simpa [Function.comp_def] using HasFDerivAt.comp_hasDerivAt 0 hd' hcurve
  have hmono : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun t ht => ne_of_gt ht
  refine ((hasDerivAt_iff_tendsto_slope.1 hcomp).mono_left hmono).congr fun t => ?_
  simp [slope_def_field]

/-! ### Corollary 25.1.1 -/

omit [NormedSpace ℝ E] in
/-- **Rockafellar, Corollary 25.1.1**, first half: a function that agrees with a real-valued
function near `x` has `x` in the interior of its effective domain. Neither convexity nor
differentiability plays any role — only local finiteness. -/
theorem mem_interior_dom_of_eventuallyEq_coe
    (hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal)) : x ∈ interior (dom f) :=
  mem_interior_iff_mem_nhds.2
    (hfg.mono fun z hz => mem_dom.2 (by rw [hz]; exact _root_.EReal.coe_lt_top _))

/-- **Rockafellar, Corollary 25.1.1**, second half: a convex function that is finite near a point
is proper.

This is the piece of Theorem 7.2 that differentiability needs, and unlike Theorem 7.2 it holds in
any topological vector space: if `f u = ⊥` then `f` is `⊥` on the half-open segment `[u, x)`
(`ConvexFn.eq_bot_of_lt_one`), whose points approach `x`, where `f` is finite. -/
theorem proper_of_eventuallyEq_coe (hf : ConvexFn f)
    (hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal)) : Proper f := by
  have hx : f x = ((g x : ℝ) : EReal) := hfg.self_of_nhds
  have hxdom : x ∈ dom f := mem_dom.2 (by rw [hx]; exact _root_.EReal.coe_lt_top _)
  refine ⟨⟨x, hxdom⟩, fun u hu => ?_⟩
  have hray : Tendsto (fun a : ℝ => (1 - a) • u + a • x) (𝓝[<] (1 : ℝ)) (𝓝 x) := by
    have hc : Continuous fun a : ℝ => (1 - a) • u + a • x := by fun_prop
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hfin : ∀ᶠ z in 𝓝 x, f z ≠ ⊥ :=
    hfg.mono fun z hz => by rw [hz]; exact _root_.EReal.coe_ne_bot _
  have hne : ∀ᶠ a in 𝓝[<] (1 : ℝ), f ((1 - a) • u + a • x) ≠ ⊥ := hray.eventually hfin
  have hbot : ∀ᶠ a in 𝓝[<] (1 : ℝ), f ((1 - a) • u + a • x) = ⊥ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos), self_mem_nhdsWithin]
      with a ha ha1
    exact hf.eq_bot_of_lt_one hu hxdom ha.le ha1
  obtain ⟨a, hane, hae⟩ := (hne.and hbot).exists
  exact hane hae

/-! ### Theorem 25.1: the gradient is the unique subgradient -/

/-- **Rockafellar, Theorem 25.1**, the gradient inequality: a convex function lies above its
tangent affine function at every point of differentiability. -/
theorem le_of_hasFDerivAt (hf : ConvexFn f) (hp : Proper f)
    (hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal)) (hd : HasFDerivAt g f' x) (z : E) :
    f x + ((f' (z - x) : ℝ) : EReal) ≤ f z := by
  have hx : f x = ((g x : ℝ) : EReal) := hfg.self_of_nhds
  rcases eq_or_ne (f z) ⊤ with hz | hz
  · rw [hz]; exact le_top
  obtain ⟨r, hfz⟩ : ∃ r : ℝ, f z = ((r : ℝ) : EReal) :=
    ⟨(f z).toReal, (_root_.EReal.coe_toReal hz (hp.ne_bot z)).symm⟩
  have hIoc : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [← Set.Ioi_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds one_pos)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (x + t • (z - x)) = ((g (x + t • (z - x)) : ℝ) : EReal) :=
    (tendsto_ray_nhdsGT x (z - x)).eventually hfg
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), (g (x + t • (z - x)) - g x) / t ≤ r - g x := by
    filter_upwards [hIoc, hev] with t ht hteq
    have hcombo := hf.epi_combo (x := x) (y := z) (μ := g x) (ν := r) hx.le hfz.le
      (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
    have hpt : (1 - t) • x + t • z = x + t • (z - x) := by module
    rw [hpt, hteq, _root_.EReal.coe_le_coe_iff] at hcombo
    rw [div_le_iff₀ ht.1]
    nlinarith [hcombo]
  have hle := le_of_tendsto (tendsto_slope_ray_of_hasFDerivAt hd (z - x)) hbound
  rw [hx, hfz, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff]
  linarith

/-- The uniqueness half of **Theorem 25.1**: any subgradient at a point of differentiability is the
derivative. Neither convexity nor properness is used — only the limit of the difference quotient
along the two opposite rays. -/
theorem eq_of_mem_subgradient_of_hasFDerivAt (hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal))
    (hd : HasFDerivAt g f' x) {y : StrongDual ℝ E}
    (hy : y ∈ subgradient (topDualPairing ℝ E).flip f x) : y = f' := by
  have hx : f x = ((g x : ℝ) : EReal) := hfg.self_of_nhds
  have hle : ∀ w : E, y w ≤ f' w := by
    intro w
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (x + t • w) = ((g (x + t • w) : ℝ) : EReal) :=
      (tendsto_ray_nhdsGT x w).eventually hfg
    have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), y w ≤ (g (x + t • w) - g x) / t := by
      filter_upwards [self_mem_nhdsWithin, hev] with t ht hteq
      have hsub := hy (x + t • w)
      have hval : ((topDualPairing ℝ E).flip (x + t • w - x)) y = t * y w := by
        rw [add_sub_cancel_left, LinearMap.flip_apply, topDualPairing_apply, map_smul,
          smul_eq_mul]
      rw [hval, hx, hteq, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at hsub
      rw [le_div_iff₀ ht]
      linarith
    exact ge_of_tendsto (tendsto_slope_ray_of_hasFDerivAt hd w) hbound
  refine ContinuousLinearMap.ext fun w => le_antisymm (hle w) ?_
  have hneg := hle (-w)
  rw [map_neg, map_neg] at hneg
  linarith

/-- **Rockafellar, Theorem 25.1**: at a point where a convex function is differentiable, the
gradient is the unique subgradient. -/
theorem subgradient_eq_singleton_of_hasFDerivAt (hf : ConvexFn f) (hp : Proper f)
    (hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal)) (hd : HasFDerivAt g f' x) :
    subgradient (topDualPairing ℝ E).flip f x = {f'} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨fun z => ?_, fun _ hy =>
    eq_of_mem_subgradient_of_hasFDerivAt hfg hd hy⟩
  have hval : ((topDualPairing ℝ E).flip (z - x)) f' = f' (z - x) := rfl
  rw [hval]
  exact le_of_hasFDerivAt hf hp hfg hd z

/-- **Rockafellar, Theorem 25.2**, necessity: at a point of differentiability the directional
derivative is the linear function `v ↦ ⟨v, ∇f x⟩`.

Both halves come from the defining infimum. The lower bound is the gradient inequality at
`x + a • v` (`EReal.coe_le_sub_div_iff` turns it into the quotient bound); the upper bound is the
limit `a ↓ 0`, extracted through `EReal.lt_iff_exists_real_btwn` so that no `EReal` division has
to be computed. -/
theorem dirDeriv_eq_of_hasFDerivAt (hf : ConvexFn f) (hp : Proper f)
    (hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal)) (hd : HasFDerivAt g f' x) (v : E) :
    dirDeriv f x v = ((f' v : ℝ) : EReal) := by
  have hx : f x = ((g x : ℝ) : EReal) := hfg.self_of_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (x + t • v) = ((g (x + t • v) : ℝ) : EReal) :=
    (tendsto_ray_nhdsGT x v).eventually hfg
  have key : ∀ m : ℝ, f' v < m → dirDeriv f x v ≤ ((m : ℝ) : EReal) := by
    intro m hm
    have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), (g (x + t • v) - g x) / t < m :=
      (tendsto_slope_ray_of_hasFDerivAt hd v).eventually (Iio_mem_nhds hm)
    have hcomb : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧
        f (x + t • v) = ((g (x + t • v) : ℝ) : EReal) ∧ (g (x + t • v) - g x) / t < m := by
      filter_upwards [self_mem_nhdsWithin, hev, hlt] with t ht hteq htlt
      exact ⟨ht, hteq, htlt⟩
    obtain ⟨t, ht, hteq, htlt⟩ := hcomb.exists
    refine (dirDeriv_le f x v ht).trans ?_
    rw [hx, hteq, EReal.sub_div_le_coe_iff ht, _root_.EReal.coe_le_coe_iff]
    rw [div_lt_iff₀ ht] at htlt
    linarith
  refine le_antisymm ?_ (le_dirDeriv fun a ha => ?_)
  · by_contra hcon
    obtain ⟨m, hm1, hm2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 (not_le.1 hcon)
    exact absurd (key m (by exact_mod_cast hm1)) (not_le.2 hm2)
  · rw [hx, EReal.coe_le_sub_div_iff ha]
    have hgrad := le_of_hasFDerivAt hf hp hfg hd (x + a • v)
    rw [hx, add_sub_cancel_left, map_smul, smul_eq_mul, ← _root_.EReal.coe_add] at hgrad
    rwa [mul_comm (f' v) a]

/-! ### Packaging: `∇f` for an `EReal`-valued function -/

/-- `f` **has gradient** `f'` at `x`: near `x`, `f` agrees with a real-valued function that is
Fréchet differentiable at `x` with derivative `f'`.

This is Rockafellar's `∇f x = f'`. An `EReal`-valued function cannot satisfy `HasFDerivAt`
directly — that needs a normed target — and the local real representative is exactly what his
definition presupposes: `f x` finite, hence `f` finite near `x`. -/
def HasGradientAt (f : E → EReal) (f' : StrongDual ℝ E) (x : E) : Prop :=
  ∃ g : E → ℝ, f =ᶠ[𝓝 x] (fun z => ((g z : ℝ) : EReal)) ∧ HasFDerivAt g f' x

/-- `f` is **differentiable** at `x` in the sense of §25. -/
def DifferentiableAtFn (f : E → EReal) (x : E) : Prop :=
  ∃ f' : StrongDual ℝ E, HasGradientAt f f' x

theorem hasGradientAt_coe (hd : HasFDerivAt g f' x) :
    HasGradientAt (fun z => ((g z : ℝ) : EReal)) f' x :=
  ⟨g, EventuallyEq.rfl, hd⟩

/-- **Corollary 25.1.1**, first half, packaged. -/
theorem HasGradientAt.mem_interior_dom (h : HasGradientAt f f' x) : x ∈ interior (dom f) := by
  obtain ⟨g, hfg, -⟩ := h
  exact mem_interior_dom_of_eventuallyEq_coe hfg

/-- **Corollary 25.1.1**, second half, packaged. -/
theorem HasGradientAt.proper (hf : ConvexFn f) (h : HasGradientAt f f' x) : Proper f := by
  obtain ⟨g, hfg, -⟩ := h
  exact proper_of_eventuallyEq_coe hf hfg

/-- **Theorem 25.1**, the gradient inequality, packaged. -/
theorem HasGradientAt.le (hf : ConvexFn f) (h : HasGradientAt f f' x) (z : E) :
    f x + ((f' (z - x) : ℝ) : EReal) ≤ f z := by
  obtain ⟨g, hfg, hd⟩ := h
  exact le_of_hasFDerivAt hf (proper_of_eventuallyEq_coe hf hfg) hfg hd z

/-- **Theorem 25.1**, packaged: the gradient is the only subgradient. -/
theorem HasGradientAt.subgradient_eq (hf : ConvexFn f) (h : HasGradientAt f f' x) :
    subgradient (topDualPairing ℝ E).flip f x = {f'} := by
  obtain ⟨g, hfg, hd⟩ := h
  exact subgradient_eq_singleton_of_hasFDerivAt hf (proper_of_eventuallyEq_coe hf hfg) hfg hd

theorem HasGradientAt.mem_subgradient (hf : ConvexFn f) (h : HasGradientAt f f' x) :
    f' ∈ subgradient (topDualPairing ℝ E).flip f x := by
  rw [h.subgradient_eq hf]
  exact Set.mem_singleton_iff.2 rfl

/-- **Theorem 25.2**, necessity, packaged. -/
theorem HasGradientAt.dirDeriv_eq (hf : ConvexFn f) (h : HasGradientAt f f' x) (v : E) :
    dirDeriv f x v = ((f' v : ℝ) : EReal) := by
  obtain ⟨g, hfg, hd⟩ := h
  exact dirDeriv_eq_of_hasFDerivAt hf (proper_of_eventuallyEq_coe hf hfg) hfg hd v

/-- The gradient is unique where it exists. Rockafellar takes this for granted; here it is the
uniqueness of `HasFDerivAt` for the local real representative, and it needs no convexity. -/
theorem HasGradientAt.unique {f₁' f₂' : StrongDual ℝ E} (h₁ : HasGradientAt f f₁' x)
    (h₂ : HasGradientAt f f₂' x) : f₁' = f₂' := by
  obtain ⟨g₁, hfg₁, hd₁⟩ := h₁
  obtain ⟨g₂, hfg₂, hd₂⟩ := h₂
  have hgg : g₁ =ᶠ[𝓝 x] g₂ := by
    filter_upwards [hfg₁, hfg₂] with z h1 h2
    have h1' : f z = ((g₁ z : ℝ) : EReal) := h1
    have h2' : f z = ((g₂ z : ℝ) : EReal) := h2
    exact_mod_cast h1'.symm.trans h2'
  exact hd₁.unique (hd₂.congr_of_eventuallyEq hgg)

end Frechet

end Tdaf.ConvexAnalysis
