/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Tdaf.Analysis.Convex.Subgradient.Defs

/-!
# Gradients and the subdifferential

Rockafellar's §25, the part that does not need measure theory. **Theorem 25.1**: where a convex
function is differentiable, its gradient is its *only* subgradient, and the directional derivative
is the corresponding linear function; conversely, a linear directional derivative forces the
subdifferential to be a single point. **Theorem 25.2**: for a convex function finite at `x`,
differentiability at `x` is *equivalent* to linearity of `f'(x; ·)`, and in finite dimensions the
two-sided derivatives along a basis already suffice.

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
* `hasGradientAt_of_dirDeriv_eq`, `differentiableAtFn_iff_exists_dirDeriv_eq` — **Theorem 25.2**,
  sufficiency and the resulting equivalence, in finite dimensions.
* `differentiableAtFn_of_forall_basis_dirDeriv_eq` — **Theorem 25.2**, last sentence: the `n`
  two-sided partial derivatives suffice.
* `ConvexFn.sum_le` — Jensen's inequality for a finite convex combination.
* `proper_of_eventuallyEq_coe`, `mem_interior_dom_of_eventuallyEq_coe` — **Corollary 25.1.1**.
* `mem_exposedPoints_epi_conj_iff` — the exposed points of `epi f*` are the points `(y, f* y)`
  such that `y` is the *only* subgradient of `f` at some point. **Corollary 25.1.2** in its
  subgradient form.
* `mem_exposedPoints_supportSet_iff` — **Corollary 25.1.3** in the same form: for a closed proper
  convex positively homogeneous `g`, the exposed points of `{x | ⟨x, y⟩ ≤ g y for all y}` are
  exactly the points that are the unique subgradient of `g` somewhere.
* `mem_exposedPoints_prod_Ici_iff` — the exposed points of a half-cylinder `C ×ˢ [0, ∞)`, which is
  what the epigraph of an indicator function looks like.
* `HasGradientAt`, `DifferentiableAtFn` — `∇f x = f'` for an `EReal`-valued `f`, with the results
  above repackaged as `HasGradientAt.le`, `.subgradient_eq`, `.dirDeriv_eq`, `.mem_interior_dom`,
  `.proper` and `.unique`. This is the interface §26 uses.

## Design notes

**Exposedness is dual to unique subdifferentiability, and that is where the corollaries stop.**
A supporting hyperplane to `epi f*` that touches it at one point only is non-vertical, so it is
the graph of `⟨x, ·⟩ - α`; supporting at `(y, μ)` says `x ∈ ∂f*(y)`, i.e. `y ∈ ∂f x`, and touching
nowhere else says `∂f x = {y}`. That is `mem_exposedPoints_epi_conj_iff`. Rockafellar then
*renames* the conclusion using both halves of Theorem 25.1, arriving at "`f` is differentiable at
`x` with `∇f x = y`"; the half that is missing here is exactly the half of Theorem 25.1 that is
missing here (see "What is not here" below), so the corollaries are stated in the subgradient
form, which is the form the proof produces.

**No finite-dimensionality, but two compatibility hypotheses.** The proof needs a continuous
linear functional on `F` to be `⟨x, ·⟩` for some `x : E`, which for `F = StrongDual ℝ E` is
reflexivity. Rather than assume `[FiniteDimensional ℝ E]` it is stated as
`[IsCompatiblePairing B.flip]`, the pairing-level form of the same thing; `E` finite-dimensional
paired with `StrongDual ℝ E` satisfies it through `instIsCompatiblePairingTopDualFinite`, and so
does any pair of spaces in a compatible duality. The other hypothesis, `[IsCompatiblePairing B]`,
is what makes `∂f*` the inverse of `∂f`.

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

**Gâteaux ⇒ Fréchet is a cross-polytope estimate, not a compactness argument.** The sufficiency
half of Theorem 25.2 is the only genuinely finite-dimensional statement in the file. Rockafellar
gets it from Theorems 23.2, 7.2 and 4.8; the route taken here is quantitative and shorter. Writing
`z - x = ∑ ξ j • b j` in a basis and putting `S = ∑ |ξ j|`, the point `z` is a convex combination
of the `n` points `x + (S * sign (ξ j)) • b j`, each of which lies along a *basis* direction at the
common distance `S` from `x`; the one-sided estimate `f (x + t • b j) ≤ f x + t c j + |t| η`
therefore applies to all of them at once, and Jensen's inequality (`ConvexFn.sum_le`) reassembles
them into `f z ≤ f x + ⟨z - x, y₀⟩ + ε ‖z - x‖`. No compactness, no continuity of `f`, and the
hypothesis consumed is only the `2n` one-sided derivatives along `± b j` — which is exactly
Rockafellar's strengthening.

**The proof of Theorem 25.1 never mentions `dirDeriv`.** Rockafellar routes it through
Theorem 23.2, but with a Fréchet derivative in hand the one-sided limit of the difference quotient
along a ray does everything: convexity bounds the quotient above by `f z - f x`, which gives
`∇f x ∈ ∂f x`, and the subgradient inequality bounds it below by `⟨v, y⟩` for any other subgradient
`y`, which gives `⟨v, y⟩ ≤ ⟨v, ∇f x⟩` for every `v` — and hence equality, by applying it to `-v`.
The uniqueness half therefore uses neither convexity nor properness.

## What is not here

**Theorems 25.5–25.7 are not formalised.** Theorem 25.5 (a.e. differentiability) is Rademacher's
theorem plus the continuity of `∇f`, which is Theorem 24.4 together with Theorem 25.1 but needs the
measure-theoretic statement first; Theorems 25.6 and 25.7 rest on 25.5 and on §24's convergence
theory. Theorems 25.3 and 25.4 are in `Subgradient/Differentiability.lean`, which needs §24.

**Theorem 25.1's converse half is in `Subgradient/Uniqueness.lean`**, not here: turning
`∂f x = {y}` into "`f` is differentiable at `x` with `∇f x = y`" needs `x` to be an *interior* point
of `dom f`, which costs a normal-cone argument and hence `Subgradient/Calculus.lean` and the
finite-dimensional separation of `Subgradient/Existence.lean`. What this module gives is the
subgradient reading of Corollaries 25.1.2 and 25.1.3, `mem_exposedPoints_epi_conj_iff` and
`mem_exposedPoints_supportSet_iff`; the differentiability reading is there too.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §25 (Theorems 25.1 and
  25.2, and Corollaries 25.1.1, 25.1.2 and 25.1.3).
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

/-! ### Jensen's inequality for finite convex combinations -/

section Jensen

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal}

/-- **Jensen's inequality** for a convex `EReal`-valued function, in the form the epigraph supplies
it: a convex combination of points at which `f` is bounded above by reals `m j` is bounded above by
the same combination of the `m j`.

The proof is `Convex.sum_mem` applied to `epi f`; stating it separately keeps the product-space
bookkeeping out of the arguments that consume it. -/
theorem ConvexFn.sum_le {ι : Type*} (hf : ConvexFn f) (t : Finset ι) (u : ι → E) (m wt : ι → ℝ)
    (hm : ∀ j ∈ t, f (u j) ≤ ((m j : ℝ) : EReal)) (hw : ∀ j ∈ t, 0 ≤ wt j)
    (hw1 : ∑ j ∈ t, wt j = 1) :
    f (∑ j ∈ t, wt j • u j) ≤ ((∑ j ∈ t, wt j * m j : ℝ) : EReal) := by
  have hmem := hf.convex_epi.sum_mem hw hw1 (fun j hj => mk_mem_epi.2 (hm j hj))
  have hsum : (∑ j ∈ t, wt j • ((u j, m j) : E × ℝ))
      = ((∑ j ∈ t, wt j • u j, ∑ j ∈ t, wt j * m j) : E × ℝ) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, smul_eq_mul]
  rw [hsum] at hmem
  exact mk_mem_epi.1 hmem

end Jensen

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

/-! ### Theorem 25.2, sufficiency -/

section Sufficiency

variable {ι : Type*} [Finite ι]

/-- The **two-sided one-dimensional estimate** behind Theorem 25.2. If the directional derivatives
of `f` at `x` along `v` and `-v` are `c` and `-c`, then for every `η > 0` there is a step `a₀ > 0`
with

```
f (x + t • v) ≤ f x + t * c + |t| * η        whenever |t| ≤ a₀,
```

for `t` of *either* sign. Both halves are `exists_le_of_dirDeriv_lt`; on the negative side it is
applied in the direction `-v`, and the linear term survives unchanged because `(-t) * (-c) = t * c`
while the error term picks up `|t| = -t`. -/
theorem exists_forall_abs_le_of_dirDeriv_eq (hf : ConvexFn f) {r : ℝ} (hr : f x = (r : EReal))
    {v : E} {c η : ℝ} (hη : 0 < η) (hpos : dirDeriv f x v = (c : EReal))
    (hneg : dirDeriv f x (-v) = ((-c : ℝ) : EReal)) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ t : ℝ, |t| ≤ a₀ →
      f (x + t • v) ≤ ((r + t * c + |t| * η : ℝ) : EReal) := by
  obtain ⟨a₁, ha₁, h₁⟩ := exists_le_of_dirDeriv_lt hf hr (y := v) (m := c + η)
    (by rw [hpos]; exact_mod_cast lt_add_of_pos_right c hη)
  obtain ⟨a₂, ha₂, h₂⟩ := exists_le_of_dirDeriv_lt hf hr (y := -v) (m := -c + η)
    (by rw [hneg]; exact_mod_cast lt_add_of_pos_right (-c) hη)
  refine ⟨min a₁ a₂, lt_min ha₁ ha₂, fun t ht => ?_⟩
  rcases lt_trichotomy t 0 with hlt | rfl | hgt
  · have habs : |t| = -t := abs_of_neg hlt
    rw [habs] at ht
    have hle := h₂ (-t) (by linarith) (ht.trans (min_le_right _ _))
    rw [neg_smul_neg] at hle
    refine hle.trans (le_of_eq ?_)
    rw [_root_.EReal.coe_eq_coe_iff, habs]
    ring
  · rw [zero_smul, add_zero, hr, _root_.EReal.coe_le_coe_iff]
    simp
  · have habs : |t| = t := abs_of_pos hgt
    rw [habs] at ht
    have hle := h₁ t hgt (ht.trans (min_le_left _ _))
    refine hle.trans (le_of_eq ?_)
    rw [_root_.EReal.coe_eq_coe_iff, habs]
    ring

/-- **Rockafellar, Theorem 25.2**, sufficiency, quantitatively: two-sided directional derivatives
along a *basis* already force the tangent affine estimate

```
f z ≤ f x + ⟨z - x, y₀⟩ + ε ‖z - x‖
```

on a ball whose radius depends only on `ε`.

Finite-dimensionality enters through a *cross-polytope* decomposition rather than through
compactness of the unit sphere, which makes the argument quantitative and basis-free at the end.
Writing `z - x = ∑ ξ j • b j` and `S = ∑ |ξ j|`, the point `z` is the convex combination, with
weights `|ξ j| / S`, of the points `x + (S * sign (ξ j)) • b j`; each of those sits at distance `S`
from `x` along a basis direction, where `exists_forall_abs_le_of_dirDeriv_eq` applies. The linear
terms recombine into `⟨z - x, y₀⟩` exactly, and the error term is `S * η`, which is at most
`ε ‖z - x‖` once `η` is scaled by the constant relating `∑ |ξ j|` to `‖z - x‖`. -/
theorem exists_le_of_forall_basis_dirDeriv_eq [FiniteDimensional ℝ E] (b : Module.Basis ι ℝ E)
    (hf : ConvexFn f) {r : ℝ} (hr : f x = (r : EReal)) {y₀ : StrongDual ℝ E}
    (hpos : ∀ j, dirDeriv f x (b j) = ((y₀ (b j) : ℝ) : EReal))
    (hneg : ∀ j, dirDeriv f x (-(b j)) = ((-(y₀ (b j)) : ℝ) : EReal))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : E, ‖z - x‖ ≤ δ →
      f z ≤ ((r + y₀ (z - x) + ε * ‖z - x‖ : ℝ) : EReal) := by
  classical
  obtain ⟨hι⟩ := nonempty_fintype ι
  obtain ⟨K, hK, hcoord⟩ : ∃ K : ℝ, 0 < K ∧ ∀ w : E, ∑ j, |b.repr w j| ≤ K * ‖w‖ := by
    set T : E →L[ℝ] (ι → ℝ) := LinearMap.toContinuousLinearMap (b.equivFun : E →ₗ[ℝ] (ι → ℝ))
      with hT
    refine ⟨(Fintype.card ι : ℝ) * ‖T‖ + 1, by positivity, fun w => ?_⟩
    have hbound : ∀ j : ι, |b.repr w j| ≤ ‖T‖ * ‖w‖ := by
      intro j
      have hTj : T w j = b.repr w j := by rw [hT]; simp [Module.Basis.equivFun_apply]
      have h1 : |b.repr w j| ≤ ‖T w‖ := by
        rw [← hTj]
        simpa using norm_le_pi_norm (T w) j
      exact h1.trans (T.le_opNorm w)
    calc ∑ j, |b.repr w j| ≤ ∑ _j : ι, ‖T‖ * ‖w‖ := Finset.sum_le_sum fun j _ => hbound j
      _ = (Fintype.card ι : ℝ) * (‖T‖ * ‖w‖) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ ((Fintype.card ι : ℝ) * ‖T‖ + 1) * ‖w‖ := by nlinarith [norm_nonneg w]
  set η : ℝ := ε / K with hηdef
  have hη : 0 < η := div_pos hε hK
  have hstep : ∀ j : ι, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ t : ℝ, |t| ≤ a₀ →
      f (x + t • b j) ≤ ((r + t * y₀ (b j) + |t| * η : ℝ) : EReal) := fun j =>
    exists_forall_abs_le_of_dirDeriv_eq hf hr hη (hpos j) (hneg j)
  choose A hA hA' using hstep
  obtain ⟨c, hc, hcA⟩ : ∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ A j := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩
    · obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image (Finset.univ : Finset ι) A
        ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
      exact ⟨A j₀, hA j₀, fun j => hj₀ j (Finset.mem_univ j)⟩
  refine ⟨c / K, div_pos hc hK, fun z hz => ?_⟩
  set w : E := z - x with hwdef
  set ξ : ι → ℝ := fun j => b.repr w j with hξdef
  have hrepr : ∑ j, ξ j • b j = w := by
    simp [hξdef]
  have hy₀w : ∑ j, ξ j * y₀ (b j) = y₀ w := by
    rw [← hrepr, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
  set S : ℝ := ∑ j, |ξ j| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hSK : S ≤ K * ‖w‖ := hcoord w
  have hSc : S ≤ c := by
    refine hSK.trans ?_
    have hle : K * ‖w‖ ≤ K * (c / K) := mul_le_mul_of_nonneg_left hz hK.le
    rwa [mul_div_cancel₀ c hK.ne'] at hle
  rcases hS0.eq_or_lt with hS | hSpos
  · have hzero : ∀ j, ξ j = 0 := by
      intro j
      have h := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => abs_nonneg (ξ j)).1 hS.symm j
        (Finset.mem_univ j)
      exact abs_eq_zero.1 h
    have hw0 : w = 0 := by rw [← hrepr]; simp [hzero]
    have hzx : z = x := by
      rw [hwdef] at hw0
      exact sub_eq_zero.1 hw0
    rw [hzx, hw0, hr]
    simp
  · set σ : ι → ℝ := fun j => if 0 ≤ ξ j then 1 else -1 with hσdef
    have habs : ∀ j, |S * σ j| = S := by
      intro j
      rw [abs_mul, abs_of_pos hSpos, hσdef]
      by_cases hj : 0 ≤ ξ j <;> simp [hj]
    have hmul : ∀ j, |ξ j| * σ j = ξ j := by
      intro j
      rw [hσdef]
      by_cases hj : 0 ≤ ξ j
      · simp [hj, abs_of_nonneg hj]
      · simp [hj, abs_of_neg (not_le.1 hj)]
    have hcoef : ∀ j : ι, (|ξ j| / S) * (S * σ j) = ξ j := by
      intro j
      have h : (|ξ j| / S) * (S * σ j) = (|ξ j| * σ j) * (S / S) := by ring
      rw [h, div_self hSpos.ne', mul_one, hmul j]
    have hw1 : ∑ j, |ξ j| / S = 1 := by
      rw [← Finset.sum_div, ← hSdef]
      exact div_self hSpos.ne'
    have hmem : ∀ j ∈ (Finset.univ : Finset ι),
        f (x + (S * σ j) • b j) ≤ ((r + (S * σ j) * y₀ (b j) + S * η : ℝ) : EReal) := by
      intro j _
      have h := hA' j (S * σ j) (by rw [habs j]; exact hSc.trans (hcA j))
      rwa [habs j] at h
    have hjensen : f (∑ j, (|ξ j| / S) • (x + (S * σ j) • b j)) ≤
        ((∑ j, (|ξ j| / S) * (r + (S * σ j) * y₀ (b j) + S * η) : ℝ) : EReal) :=
      hf.sum_le _ _ _ _ hmem (fun j _ => div_nonneg (abs_nonneg _) hSpos.le) hw1
    have hpt : ∑ j, (|ξ j| / S) • (x + (S * σ j) • b j) = z := by
      have hterm : ∀ j : ι,
          (|ξ j| / S) • (x + (S * σ j) • b j) = (|ξ j| / S) • x + ξ j • b j := by
        intro j
        rw [smul_add, smul_smul, hcoef j]
      calc ∑ j, (|ξ j| / S) • (x + (S * σ j) • b j)
          = ∑ j, ((|ξ j| / S) • x + ξ j • b j) := Finset.sum_congr rfl fun j _ => hterm j
        _ = (∑ j, |ξ j| / S) • x + ∑ j, ξ j • b j := by
            rw [Finset.sum_add_distrib, ← Finset.sum_smul]
        _ = x + w := by rw [hw1, one_smul, hrepr]
        _ = z := by rw [hwdef]; abel
    have hval : ∑ j, (|ξ j| / S) * (r + (S * σ j) * y₀ (b j) + S * η) = r + y₀ w + S * η := by
      have hterm : ∀ j : ι, (|ξ j| / S) * (r + (S * σ j) * y₀ (b j) + S * η)
          = (|ξ j| / S) * r + ξ j * y₀ (b j) + (|ξ j| / S) * (S * η) := by
        intro j
        have h : (|ξ j| / S) * (r + (S * σ j) * y₀ (b j) + S * η)
            = (|ξ j| / S) * r + ((|ξ j| / S) * (S * σ j)) * y₀ (b j) + (|ξ j| / S) * (S * η) := by
          ring
        rw [h, hcoef j]
      calc ∑ j, (|ξ j| / S) * (r + (S * σ j) * y₀ (b j) + S * η)
          = ∑ j, ((|ξ j| / S) * r + ξ j * y₀ (b j) + (|ξ j| / S) * (S * η)) :=
            Finset.sum_congr rfl fun j _ => hterm j
        _ = (∑ j, |ξ j| / S) * r + (∑ j, ξ j * y₀ (b j)) + (∑ j, |ξ j| / S) * (S * η) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        _ = r + y₀ w + S * η := by rw [hw1, one_mul, one_mul, hy₀w]
    rw [hpt, hval] at hjensen
    refine hjensen.trans ?_
    rw [_root_.EReal.coe_le_coe_iff]
    have hSη : S * η ≤ ε * ‖w‖ := by
      calc S * η ≤ (K * ‖w‖) * η := mul_le_mul_of_nonneg_right hSK hη.le
        _ = ε * ‖w‖ := by rw [hηdef]; field_simp
    linarith

/-- The estimate of `exists_le_of_forall_basis_dirDeriv_eq` recovers `f'(x; ·)` in *every*
direction, not only along the basis: it bounds `f'(x; v)` above by `⟨v, y₀⟩`, and Theorem 23.1's
`-f'(x; -v) ≤ f'(x; v)` supplies the matching lower bound. This is the step that turns
Rockafellar's `n` two-sided partial derivatives into the linearity of `f'(x; ·)`; his own route is
through Theorems 7.2 and 4.8, which need `f'(x; ·)` to be proper first. -/
theorem dirDeriv_eq_of_forall_basis_dirDeriv_eq [FiniteDimensional ℝ E]
    (b : Module.Basis ι ℝ E) (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥)
    {y₀ : StrongDual ℝ E} (hpos : ∀ j, dirDeriv f x (b j) = ((y₀ (b j) : ℝ) : EReal))
    (hneg : ∀ j, dirDeriv f x (-(b j)) = ((-(y₀ (b j)) : ℝ) : EReal)) (v : E) :
    dirDeriv f x v = ((y₀ v : ℝ) : EReal) := by
  obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  have hle : ∀ u : E, dirDeriv f x u ≤ ((y₀ u : ℝ) : EReal) := by
    intro u
    rcases eq_or_ne u 0 with rfl | hu
    · rw [dirDeriv_zero ht hb]
      simp
    have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu
    have hnu' : ‖u‖ ≠ 0 := hnu.ne'
    by_contra hcon
    obtain ⟨m, hm₁, hm₂⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 (not_le.1 hcon)
    have hm' : y₀ u < m := by exact_mod_cast hm₁
    obtain ⟨δ, hδ, hup⟩ := exists_le_of_forall_basis_dirDeriv_eq b hf hr hpos hneg
      (div_pos (sub_pos.2 hm') hnu)
    set a : ℝ := min (δ / ‖u‖) 1 with hadef
    have ha : 0 < a := lt_min (div_pos hδ hnu) one_pos
    have hnorm : ‖x + a • u - x‖ ≤ δ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      calc a * ‖u‖ ≤ (δ / ‖u‖) * ‖u‖ := mul_le_mul_of_nonneg_right (min_le_left _ _) hnu.le
        _ = δ := div_mul_cancel₀ δ hnu'
    have hbound := hup (x + a • u) hnorm
    rw [add_sub_cancel_left] at hbound
    have hfinal : dirDeriv f x u ≤ (m : EReal) := by
      refine (dirDeriv_le f x u ha).trans ?_
      rw [hr, Tdaf.EReal.sub_div_le_coe_iff ha]
      refine hbound.trans (le_of_eq ?_)
      rw [_root_.EReal.coe_eq_coe_iff, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
        abs_of_pos ha]
      field_simp
      ring
    exact absurd hfinal (not_le.2 hm₂)
  refine le_antisymm (hle v) ?_
  have hneg' := hle (-v)
  rw [map_neg] at hneg'
  have h2 := _root_.EReal.neg_le_neg_iff.2 hneg'
  rw [← _root_.EReal.coe_neg, neg_neg] at h2
  exact h2.trans (neg_dirDeriv_neg_le hf ht hb v)

/-- **Rockafellar, Theorem 25.2**, sufficiency, from two-sided derivatives along a basis: `f` is
Fréchet differentiable at `x`, with gradient the functional `y₀` whose values along the basis are
the given one-sided derivatives.

The two-sided estimate `f x + ⟨z - x, y₀⟩ ≤ f z ≤ f x + ⟨z - x, y₀⟩ + ε ‖z - x‖` does all three
jobs at once: the lower half comes from `y₀ ∈ ∂f x` (Theorem 23.2), the upper half is
`exists_le_of_forall_basis_dirDeriv_eq`, and together they make `f` finite near `x` — so that the
local real representative `z ↦ (f z).toReal` exists — and exhibit the little-o estimate defining
`HasFDerivAt`. -/
theorem hasGradientAt_of_forall_basis_dirDeriv_eq [FiniteDimensional ℝ E]
    (b : Module.Basis ι ℝ E) (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥)
    {y₀ : StrongDual ℝ E} (hpos : ∀ j, dirDeriv f x (b j) = ((y₀ (b j) : ℝ) : EReal))
    (hneg : ∀ j, dirDeriv f x (-(b j)) = ((-(y₀ (b j)) : ℝ) : EReal)) :
    HasGradientAt f y₀ x := by
  obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  have hall := dirDeriv_eq_of_forall_basis_dirDeriv_eq b hf ht hb hpos hneg
  have hsubg : y₀ ∈ subgradient (topDualPairing ℝ E).flip f x :=
    (mem_subgradient_iff_le_dirDeriv ht hb).2 fun v => le_of_eq (hall v).symm
  have hlow : ∀ z : E, ((r + y₀ (z - x) : ℝ) : EReal) ≤ f z := by
    intro z
    have h := hsubg z
    rwa [hr, show ((topDualPairing ℝ E).flip (z - x)) y₀ = y₀ (z - x) from rfl,
      ← _root_.EReal.coe_add] at h
  obtain ⟨δ₁, hδ₁, hup₁⟩ := exists_le_of_forall_basis_dirDeriv_eq b hf hr hpos hneg one_pos
  have hfin : ∀ z : E, ‖z - x‖ ≤ δ₁ → f z = (((f z).toReal : ℝ) : EReal) := by
    intro z hz
    refine (_root_.EReal.coe_toReal (ne_top_of_le_ne_top (_root_.EReal.coe_ne_top _)
      (hup₁ z hz)) ?_).symm
    intro hbot
    have h := hlow z
    rw [hbot, le_bot_iff] at h
    exact absurd h (_root_.EReal.coe_ne_bot _)
  have hfg : f =ᶠ[𝓝 x] fun z => (((f z).toReal : ℝ) : EReal) := by
    filter_upwards [Metric.closedBall_mem_nhds x hδ₁] with z hz
    exact hfin z (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)
  have hgx : (f x).toReal = r := by rw [hr, _root_.EReal.toReal_coe]
  refine ⟨fun z => (f z).toReal, hfg, ?_⟩
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hup⟩ := exists_le_of_forall_basis_dirDeriv_eq b hf hr hpos hneg hε
  filter_upwards [Metric.closedBall_mem_nhds x (lt_min hδ hδ₁)] with z hz
  have hzn : ‖z - x‖ ≤ min δ δ₁ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 := hup z (hzn.trans (min_le_left _ _))
  have h2 := hlow z
  rw [hfin z (hzn.trans (min_le_right _ _)), _root_.EReal.coe_le_coe_iff] at h1 h2
  rw [hgx, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **Rockafellar, Theorem 25.2**, sufficiency: if the directional derivative `f'(x; ·)` is the
linear function `⟨·, y₀⟩`, then `f` is differentiable at `x` with `∇f x = y₀`.

This is the previous theorem read at any basis; the hypothesis in every direction is more than the
proof consumes. -/
theorem hasGradientAt_of_dirDeriv_eq [FiniteDimensional ℝ E] (hf : ConvexFn f) (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) {y₀ : StrongDual ℝ E}
    (h : ∀ v : E, dirDeriv f x v = ((y₀ v : ℝ) : EReal)) : HasGradientAt f y₀ x :=
  hasGradientAt_of_forall_basis_dirDeriv_eq (Module.finBasis ℝ E) hf ht hb (fun j => h _)
    (fun j => by rw [h, map_neg])

/-- **Rockafellar, Theorem 25.2**, in full: for a convex function finite at `x`, differentiability
at `x` is equivalent to linearity of `f'(x; ·)`. Necessity is `HasGradientAt.dirDeriv_eq` and
sufficiency is `hasGradientAt_of_dirDeriv_eq`. -/
theorem differentiableAtFn_iff_exists_dirDeriv_eq [FiniteDimensional ℝ E] (hf : ConvexFn f)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    DifferentiableAtFn f x ↔
      ∃ y₀ : StrongDual ℝ E, ∀ v : E, dirDeriv f x v = ((y₀ v : ℝ) : EReal) := by
  constructor
  · rintro ⟨y₀, hy₀⟩
    exact ⟨y₀, hy₀.dirDeriv_eq hf⟩
  · rintro ⟨y₀, h⟩
    exact ⟨y₀, hasGradientAt_of_dirDeriv_eq hf ht hb h⟩

/-- **Rockafellar, Theorem 25.2**, last sentence: it is enough that the `n` two-sided partial
derivatives exist and are finite. Here "the `n` partial derivatives" is the pair of one-sided
derivatives along the vectors of a basis, and "two-sided and finite" is the requirement that they
be the negatives of each other and real. The gradient is then `b.constr` of those numbers. -/
theorem differentiableAtFn_of_forall_basis_dirDeriv_eq [FiniteDimensional ℝ E]
    (b : Module.Basis ι ℝ E) (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (c : ι → ℝ)
    (hpos : ∀ j, dirDeriv f x (b j) = ((c j : ℝ) : EReal))
    (hneg : ∀ j, dirDeriv f x (-(b j)) = ((-(c j) : ℝ) : EReal)) :
    DifferentiableAtFn f x := by
  refine ⟨LinearMap.toContinuousLinearMap (b.constr ℝ c), ?_⟩
  have hval : ∀ j, (LinearMap.toContinuousLinearMap (b.constr ℝ c)) (b j) = c j := fun j => by
    simp
  exact hasGradientAt_of_forall_basis_dirDeriv_eq b hf ht hb (fun j => by rw [hpos j, hval j])
    (fun j => by rw [hneg j, hval j])

end Sufficiency

end Frechet


/-! ### Exposed points of a half-cylinder -/

section HalfCylinder

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]

/-- **The exposed points of a half-cylinder** `C ×ˢ [0, ∞)` are the points `(z, 0)` with `z` an
exposed point of `C`.

A functional exposing a point of the cylinder must be *strictly* decreasing in the vertical
direction — otherwise the whole vertical ray attains the maximum — and that forces the height to
be `0` and reduces the functional to one on `C`. This is the epigraph of an indicator function
(`epi_indicatorFn`), so it is how a statement about `epi f*` becomes a statement about a convex
set. -/
theorem mem_exposedPoints_prod_Ici_iff {C : Set X} {z : X} {ν : ℝ} :
    (z, ν) ∈ (C ×ˢ Ici (0 : ℝ)).exposedPoints ℝ ↔ ν = 0 ∧ z ∈ C.exposedPoints ℝ := by
  constructor
  · rintro ⟨⟨hzC, hν⟩, L, hL⟩
    have hν0' : (0 : ℝ) ≤ ν := hν
    set c : ℝ := L (0, 1) with hcdef
    have hsplit : ∀ (w : X) (γ : ℝ), L (w, γ) = L (w, 0) + γ * c := by
      intro w γ
      have h1 : ((w, γ) : X × ℝ) = (w, 0) + (0, γ) := by
        rw [Prod.mk_add_mk, add_zero, zero_add]
      have h2 : ((0, γ) : X × ℝ) = γ • ((0 : X), (1 : ℝ)) := by
        rw [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]
      rw [h1, map_add, h2, map_smul, smul_eq_mul, ← hcdef, mul_comm]
    have hmemup : ((z, ν + 1) : X × ℝ) ∈ C ×ˢ Ici (0 : ℝ) := ⟨hzC, by simp; linarith⟩
    have hcneg : c < 0 := by
      have hle : c ≤ 0 := by
        have h := (hL _ hmemup).1
        rw [hsplit z (ν + 1), hsplit z ν] at h
        nlinarith
      refine lt_of_le_of_ne hle fun h0 => ?_
      have h := (hL _ hmemup).2 (by rw [hsplit z (ν + 1), hsplit z ν, h0]; simp)
      have : ν + 1 = ν := congrArg Prod.snd h
      linarith
    have hν0 : ν = 0 := by
      have h := (hL ((z, (0 : ℝ)) : X × ℝ) ⟨hzC, (mem_Ici.2 le_rfl)⟩).1
      rw [hsplit z 0, hsplit z ν] at h
      nlinarith
    subst hν0
    refine ⟨rfl, hzC, L.comp (ContinuousLinearMap.inl ℝ X ℝ), fun w hw => ⟨?_, fun hge => ?_⟩⟩
    · have h := (hL ((w, (0 : ℝ)) : X × ℝ) ⟨hw, (mem_Ici.2 le_rfl)⟩).1
      simpa using h
    · refine congrArg Prod.fst ((hL ((w, (0 : ℝ)) : X × ℝ) ⟨hw, (mem_Ici.2 le_rfl)⟩).2 ?_)
      simpa using hge
  · rintro ⟨rfl, hzC, l, hl⟩
    refine ⟨⟨hzC, (mem_Ici.2 le_rfl)⟩,
      l.comp (ContinuousLinearMap.fst ℝ X ℝ) - ContinuousLinearMap.snd ℝ X ℝ, ?_⟩
    have hval : ∀ (u : X) (δ : ℝ),
        (l.comp (ContinuousLinearMap.fst ℝ X ℝ) - ContinuousLinearMap.snd ℝ X ℝ) (u, δ)
          = l u - δ := by
      intro u δ
      simp
    rintro ⟨w, γ⟩ ⟨hw, hγ⟩
    have hγ0 : (0 : ℝ) ≤ γ := hγ
    obtain ⟨h1, h2⟩ := hl w hw
    refine ⟨by rw [hval, hval]; linarith, fun hge => ?_⟩
    rw [hval, hval] at hge
    have hγz : γ = 0 := le_antisymm (by linarith) hγ0
    have hwz : w = z := h2 (by linarith)
    rw [hwz, hγz]

end HalfCylinder

/-! ### Exposed points of the epigraph of a conjugate -/

section Exposed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- A subgradient pins down the value: if `y ∈ ∂f x` and `f* y = μ` is finite, then
`f x = ⟨x, y⟩ - μ`. This is Fenchel's equality solved for `f x`, and in particular `f x` is
finite. -/
theorem Proper.eq_sub_of_mem_subgradient (hp : Proper f) {x : E} {y : F} {μ : ℝ}
    (hy : y ∈ subgradient B f x) (hμ : conj B f y = (μ : EReal)) :
    f x = ((B x y - μ : ℝ) : EReal) := by
  have hfx : f x + conj B f y = ((B x y : ℝ) : EReal) :=
    hp.mem_subgradient_iff_add_conj_eq.1 hy
  rw [hμ] at hfx
  have hxb : f x ≠ ⊥ := hp.ne_bot x
  have hxt : f x ≠ ⊤ := by
    intro h
    rw [h, _root_.EReal.top_add_of_ne_bot (_root_.EReal.coe_ne_bot μ)] at hfx
    exact absurd hfx (_root_.EReal.top_ne_coe _)
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (_root_.EReal.coe_toReal hxt hxb).symm
  rw [hxc, ← _root_.EReal.coe_add, _root_.EReal.coe_eq_coe_iff] at hfx
  rw [hxc, _root_.EReal.coe_eq_coe_iff]
  linarith

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [TopologicalSpace F]

/-- **The exposed points of the epigraph of a conjugate.** A point `(y, μ)` is an exposed point of
`epi f*` exactly when `μ = f* y` and `y` is the *only* subgradient of `f` at some point `x`.

Geometrically: a supporting hyperplane to `epi f*` that touches it in a single point is
necessarily non-vertical, so it is the graph of an affine function `⟨x, ·⟩ - α`; that it supports
`epi f*` at `(y, μ)` says `x ∈ ∂f*(y)`, i.e. `y ∈ ∂f x`, and that it touches nowhere else says
`∂f x` is no larger than `{y}`.

Only the forward direction uses closedness — through `∂f* = (∂f)⁻¹` — and neither direction uses
finite-dimensionality: what replaces it is `IsCompatiblePairing B.flip`, which says that a
continuous linear functional on `F` is `⟨x, ·⟩` for some `x : E`. -/
theorem mem_exposedPoints_epi_conj_iff [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ConvexFn f) (hp : Proper f) (hc : ClosedFn f) {y : F} {μ : ℝ} :
    (y, μ) ∈ (epi (conj B f)).exposedPoints ℝ ↔
      conj B f y = (μ : EReal) ∧ ∃ x : E, subgradient B f x = {y} := by
  have hbot : ∀ z : F, conj B f z ≠ ⊥ := conj_ne_bot hp.dom_nonempty
  constructor
  · rintro ⟨hmem, L, hL⟩
    have hmem' : conj B f y ≤ (μ : EReal) := hmem
    -- Split `L` into a functional on `F` and a coefficient of the vertical direction.
    obtain ⟨x₀, hx₀⟩ := exists_pairing_eq B.flip (L.comp (ContinuousLinearMap.inl ℝ F ℝ))
    set c : ℝ := L (0, 1) with hcdef
    have hsplit : ∀ (z : F) (β : ℝ), L (z, β) = B x₀ z + β * c := by
      intro z β
      have h1 : ((z, β) : F × ℝ) = (z, 0) + (0, β) := by
        rw [Prod.mk_add_mk, add_zero, zero_add]
      have h2 : ((0, β) : F × ℝ) = β • ((0 : F), (1 : ℝ)) := by
        rw [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]
      have h3 : L (z, 0) = B x₀ z := by
        simpa [LinearMap.flip_apply] using hx₀ z
      rw [h1, map_add, h3, h2, map_smul, smul_eq_mul, ← hcdef, mul_comm]
    -- The vertical direction is a direction of recession of the epigraph.
    have hup : ∀ t : ℝ, 0 ≤ t → (y, μ + t) ∈ epi (conj B f) := fun t ht =>
      hmem'.trans (by exact_mod_cast le_add_of_nonneg_right ht)
    have hcneg : c < 0 := by
      have hle : c ≤ 0 := by
        have h := (hL _ (hup 1 zero_le_one)).1
        rw [hsplit, hsplit] at h
        nlinarith
      refine lt_of_le_of_ne hle fun h0 => ?_
      have heq : L (y, μ) ≤ L (y, μ + 1) := by rw [hsplit, hsplit, h0]; simp
      have := (hL _ (hup 1 zero_le_one)).2 heq
      have hμ' : μ + 1 = μ := congrArg Prod.snd this
      linarith
    -- Normalise the functional so that the vertical coefficient is `-1`.
    have hcne : c ≠ 0 := ne_of_lt hcneg
    have hpos : (0 : ℝ) < (-c)⁻¹ := inv_pos.2 (neg_pos.2 hcneg)
    set x : E := (-c)⁻¹ • x₀ with hxdef
    have hBx : ∀ z : F, B x z = (-c)⁻¹ * B x₀ z := by
      intro z
      rw [hxdef, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hmax : ∀ (z : F) (β : ℝ), conj B f z ≤ (β : EReal) → B x z - β ≤ B x y - μ := by
      intro z β hzβ
      have h := (hL (z, β) hzβ).1
      rw [hsplit, hsplit] at h
      have h' : (-c)⁻¹ * (B x₀ z + β * c) ≤ (-c)⁻¹ * (B x₀ y + μ * c) :=
        mul_le_mul_of_nonneg_left h hpos.le
      have e1 : (-c)⁻¹ * (β * c) = -β := by field_simp
      have e2 : (-c)⁻¹ * (μ * c) = -μ := by field_simp
      rw [mul_add, mul_add, e1, e2] at h'
      rw [hBx, hBx]
      linarith
    have huniq : ∀ (z : F) (β : ℝ), conj B f z ≤ (β : EReal) →
        B x y - μ ≤ B x z - β → (z, β) = (y, μ) := by
      intro z β hzβ hge
      refine (hL (z, β) hzβ).2 ?_
      rw [hBx, hBx] at hge
      have h' : (-c) * ((-c)⁻¹ * B x₀ y - μ) ≤ (-c) * ((-c)⁻¹ * B x₀ z - β) :=
        mul_le_mul_of_nonneg_left hge (neg_nonneg.2 hcneg.le)
      have e1 : (-c) * ((-c)⁻¹ * B x₀ y) = B x₀ y := by field_simp
      have e2 : (-c) * ((-c)⁻¹ * B x₀ z) = B x₀ z := by field_simp
      rw [mul_sub, mul_sub, e1, e2] at h'
      rw [hsplit, hsplit]
      nlinarith
    -- The value at `y` is `μ`.
    have hyt : conj B f y ≠ ⊤ := ne_top_of_le_ne_top (_root_.EReal.coe_ne_top μ) hmem'
    have hyc : conj B f y = (((conj B f y).toReal : ℝ) : EReal) :=
      (_root_.EReal.coe_toReal hyt (hbot y)).symm
    have hνμ : (conj B f y).toReal ≤ μ := by
      rw [hyc, _root_.EReal.coe_le_coe_iff] at hmem'
      exact hmem'
    have hμν : μ ≤ (conj B f y).toReal := by
      have := hmax y _ (le_of_eq hyc)
      linarith
    have hμeq : conj B f y = (μ : EReal) := by
      rw [hyc, _root_.EReal.coe_eq_coe_iff]
      linarith
    -- `y` is a subgradient at `x`, and the only one.
    have hysub : y ∈ subgradient B f x := by
      rw [← mem_subgradient_conj_iff_of_closedFn hf hc, mem_subgradient_iff_forall_sub_le]
      intro z
      rcases eq_or_ne (conj B f z) ⊤ with hz | hz
      · rw [hz]
        simp
      · have hzc : conj B f z = (((conj B f z).toReal : ℝ) : EReal) :=
          (_root_.EReal.coe_toReal hz (hbot z)).symm
        have h := hmax z _ (le_of_eq hzc)
        rw [LinearMap.flip_apply, LinearMap.flip_apply, hzc, hμeq, ← _root_.EReal.coe_sub,
          ← _root_.EReal.coe_sub, _root_.EReal.coe_le_coe_iff]
        exact h
    refine ⟨hμeq, x, Set.eq_singleton_iff_unique_mem.2 ⟨hysub, fun z hz => ?_⟩⟩
    have hfx : f x = ((B x y - μ : ℝ) : EReal) := hp.eq_sub_of_mem_subgradient hysub hμeq
    have hzc : conj B f z = ((B x z : ℝ) : EReal) - f x := mem_subgradient_iff_conj_eq.1 hz
    rw [hfx, ← _root_.EReal.coe_sub] at hzc
    have := huniq z (B x z - (B x y - μ)) (le_of_eq hzc) (by simp)
    exact congrArg Prod.fst this
  · rintro ⟨hμ, x, hx⟩
    have hy : y ∈ subgradient B f x := by rw [hx]; rfl
    have hfx : f x = ((B x y - μ : ℝ) : EReal) := hp.eq_sub_of_mem_subgradient hy hμ
    refine ⟨le_of_eq hμ, (evalCLM B.flip x).comp (ContinuousLinearMap.fst ℝ F ℝ) -
      ContinuousLinearMap.snd ℝ F ℝ, ?_⟩
    have hval : ∀ (w : F) (γ : ℝ),
        ((evalCLM B.flip x).comp (ContinuousLinearMap.fst ℝ F ℝ) -
          ContinuousLinearMap.snd ℝ F ℝ) (w, γ) = B x w - γ := by
      intro w γ
      simp [LinearMap.flip_apply]
    rintro ⟨z, β⟩ hzβ
    have hzβ' : conj B f z ≤ (β : EReal) := hzβ
    have hzt : conj B f z ≠ ⊤ := ne_top_of_le_ne_top (_root_.EReal.coe_ne_top β) hzβ'
    have hzc : conj B f z = (((conj B f z).toReal : ℝ) : EReal) :=
      (_root_.EReal.coe_toReal hzt (hbot z)).symm
    have hrβ : (conj B f z).toReal ≤ β := by
      rw [hzc, _root_.EReal.coe_le_coe_iff] at hzβ'
      exact hzβ'
    have hfen := hp.le_add_conj (B := B) x z
    rw [hfx, hzc, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at hfen
    refine ⟨?_, fun hge => ?_⟩
    · rw [hval, hval]
      linarith
    · rw [hval, hval] at hge
      have hβr : β = (conj B f z).toReal := by linarith
      have hzsub : z ∈ subgradient B f x := by
        refine mem_subgradient_iff_conj_eq.2 ?_
        rw [hzc, hfx, ← _root_.EReal.coe_sub, _root_.EReal.coe_eq_coe_iff]
        linarith
      have hzy : z = y := by rw [hx] at hzsub; exact hzsub
      subst hzy
      rw [hμ, _root_.EReal.toReal_coe] at hβr
      rw [hβr]

/-! ### Exposed points of a set cut out by a positively homogeneous function -/

section Homogeneous

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- **The exposed points of a set are the values of the subdifferential of any positively
homogeneous function that cuts it out.** If `g` is a closed proper convex positively homogeneous
function and `C = {x | ⟨x, y⟩ ≤ g y for all y}` — for instance the support function of `C` — then
`z` is an exposed point of `C` exactly when `z` is the *only* subgradient of `g` at some `y`.

The conjugate of `g` is the indicator of `C` (`conj_eq_indicatorFn_of_posHomogeneous`), so
`epi g*` is the half-cylinder `C ×ˢ [0, ∞)`, whose exposed points are the exposed points of `C`
sitting at height `0` (`mem_exposedPoints_prod_Ici_iff`). The statement is then
`mem_exposedPoints_epi_conj_iff` read at height `0`. -/
theorem mem_exposedPoints_supportSet_iff [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    {g : F → EReal} (hgh : PosHomogeneous g) (hgc : ConvexFn g) (hgp : Proper g)
    (hgcl : ClosedFn g) {z : E} :
    z ∈ (supportSet B.flip g).exposedPoints ℝ ↔ ∃ y : F, subgradient B.flip g y = {z} := by
  have hne : ∃ w, g w ≠ ⊤ := by
    obtain ⟨w, hw⟩ := hgp.dom_nonempty
    exact ⟨w, hw.ne⟩
  have hind : conj B.flip g = indicatorFn (supportSet B.flip g) :=
    conj_eq_indicatorFn_of_posHomogeneous hgh hne
  have hepi : epi (conj B.flip g) = supportSet B.flip g ×ˢ Ici (0 : ℝ) := by
    rw [hind, epi_indicatorFn]
  constructor
  · intro hz
    have h1 : ((z, (0 : ℝ)) : E × ℝ) ∈ (epi (conj B.flip g)).exposedPoints ℝ := by
      rw [hepi]
      exact mem_exposedPoints_prod_Ici_iff.2 ⟨rfl, hz⟩
    exact ((mem_exposedPoints_epi_conj_iff (B := B.flip) hgc hgp hgcl).1 h1).2
  · rintro ⟨y, hy⟩
    have hzsub : z ∈ subgradient B.flip g y := by rw [hy]; rfl
    have hzt : conj B.flip g z ≠ ⊤ := by
      intro htop
      have heq := hgp.mem_subgradient_iff_add_conj_eq.1 hzsub
      rw [htop, add_comm, _root_.EReal.top_add_of_ne_bot (hgp.ne_bot y)] at heq
      exact absurd heq (_root_.EReal.top_ne_coe _)
    have hzC : z ∈ supportSet B.flip g := by
      by_contra hzn
      rw [hind, indicatorFn_of_notMem hzn] at hzt
      exact hzt rfl
    have hz0 : conj B.flip g z = ((0 : ℝ) : EReal) := by
      rw [hind, indicatorFn_of_mem hzC, _root_.EReal.coe_zero]
    have h1 := (mem_exposedPoints_epi_conj_iff (B := B.flip) hgc hgp hgcl
      (y := z) (μ := (0 : ℝ))).2 ⟨hz0, y, hy⟩
    rw [hepi] at h1
    exact (mem_exposedPoints_prod_Ici_iff.1 h1).2

end Homogeneous

end Topology

end Exposed

end Tdaf.ConvexAnalysis
