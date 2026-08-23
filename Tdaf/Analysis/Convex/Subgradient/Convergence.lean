/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Convergence
import Tdaf.Analysis.Convex.Subgradient.Bounded

/-!
# Convergence of directional derivatives and of subgradients

Convex functions `f i`, finite on an open convex set `U` and converging pointwise there to `g`,
converge in a much stronger sense than the hypothesis suggests: uniformly on compact subsets, hence
*continuously* — `f i (x i) → g x` along any `x i → x` in `U`. This file carries that strength over
to the first-order data.

Differentiation does **not** pass to the limit: only the one-sided inequality survives, and it is
the `limsup` one. For `x i → x` in `U` and `y i → y`,

```
limsup_i (f i)'(x i; y i)  ≤  g'(x; y),        ∂(f i)(x i)  ⊆  ∂g(x) + ε B  eventually.
```

Equality can fail: for `f i x = |x|^{p i}` with `p i ↓ 1` on `U = ℝ`, every `(f i)'(0; 1)` is `0`
while `g'(0; 1) = 1`. Taking the family constant turns the two statements into upper semicontinuity
of `f'(x; y)` in `(x, y)` and of `∂f` in `x`.

## Main results

* `tendsto_eval_of_tendsto` — continuous convergence: `f i (x i) → g x`.
* `eventually_dirDeriv_lt` — the `limsup` inequality for directional derivatives, spelled without
  junk values: every real `μ` above `g'(x; y)` eventually bounds `(f i)'(x i; y i)`.
* `eventually_subgradient_subset_add_closedBall` — the inclusion `∂(f i)(x i) ⊆ ∂g(x) + ε B`.
* `upperSemicontinuousAt_dirDeriv`, `eventually_nhds_subgradient_subset_add_closedBall` — the
  constant-family case: `f'(x; y)` is upper semicontinuous in `(x, y)` on `int (dom f) × E`, and
  `∂f z ⊆ ∂f x + ε B` for `z` near `x`.
* `supportFn_closedBall` — `δ*(y | ε B) = ε ‖y‖`, the set-side identity the inclusion needs.
* `dirDeriv_eq_coe_toReal_of_mem_interior_dom`, `convexOn_toReal_dirDeriv`,
  `toReal_dirDeriv_smul` — `f'(x; ·)` at an interior point of `dom f` as a finite sublinear
  function, which is the object the uniformity theorems consume.

## Design notes

**Two currencies.** The convergence theory for families of convex functions is stated for
real-valued `ConvexOn ℝ U (f i)`, while subgradients and directional derivatives are stated for
`EReal`-valued `ConvexFn`. The bridge is `ConvexFn.convexOn_toReal_dom` together with
`EReal.coe_toReal` at points where the function is finite, and it is crossed twice: once for the
`f i` themselves on `U`, once for the sublinear functions `(f i)'(x i; ·)` on the whole space.

**Sequences, not filters.** Both theorems are about sequences, because the uniformity they rest on
— pointwise convergence of convex functions is uniform on compacta — is a statement about
sequences. The local corollaries are nevertheless stated for the neighbourhood filter, since
`𝓝 (x, y)` is countably generated and `Filter.eventually_iff_seq_eventually` converts.

**No membership hypothesis on the sequence.** Rockafellar asks for a sequence *in* `C`; here only
`x i → x ∈ U` is assumed, and the proof replaces `x i` by `x` at the finitely many indices outside
`U`. That keeps the theorem usable when the sequence is produced by some other construction.

**`ε B` needs a norm on the dual side**, so the subgradient statement is for a real inner-product
space paired with itself. The directional-derivative statement needs no such thing and is stated
for a finite-dimensional normed space.

## What is not here

**The refinement in which `x i` approaches `x` from one fixed direction** — where the limit set is
not all of `∂f(x)` but the face of `∂f(x)` exposed by that direction, and the bounding function is
the second-order derivative `f'(x; y; ·)`. It needs the identity
`δ*(· | face of C exposed by y) = (δ*(· | C))'(y; ·)`, continuity of a convex function relative to
a polytope, and a simplex around a prescribed interior direction.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §24 (Theorem 24.5,
  Corollary 24.5.1). Theorem 24.6 is the refinement described above.
-/

open Set Filter Topology
open scoped NNReal Pointwise RealInnerProductSpace

namespace Tdaf.ConvexAnalysis

/-! ### Support function of a ball -/

section Ball

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support function of the ball of radius `ε` about the origin is `ε ‖·‖`. -/
theorem supportFn_closedBall {ε : ℝ} (hε : 0 ≤ ε) (y : E) :
    supportFn (innerₗ E) (Metric.closedBall (0 : E) ε) y = ((ε * ‖y‖ : ℝ) : EReal) := by
  refine le_antisymm (supportFn_le_coe_iff.2 fun z hz => ?_) ?_
  · rw [Metric.mem_closedBall, dist_zero_right] at hz
    have hcs : (innerₗ E) z y ≤ ‖z‖ * ‖y‖ := by
      rw [innerₗ_apply_apply]; exact real_inner_le_norm z y
    exact hcs.trans (by gcongr)
  · rcases eq_or_ne y 0 with rfl | hy
    · have h0 : (0 : E) ∈ Metric.closedBall (0 : E) ε := Metric.mem_closedBall_self hε
      have h := le_supportFn (B := innerₗ E) h0 (0 : E)
      simpa using h
    have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hmem : (ε / ‖y‖) • y ∈ Metric.closedBall (0 : E) ε := by
      have hpos : (0 : ℝ) ≤ ε / ‖y‖ := by positivity
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hpos]
      field_simp
      exact le_rfl
    have h := le_supportFn (B := innerₗ E) hmem y
    have hval : (innerₗ E) ((ε / ‖y‖) • y) y = ε * ‖y‖ := by
      rw [innerₗ_apply_apply, real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
      field_simp
    rwa [hval] at h

end Ball

/-! ### The directional derivative at an interior point -/

section Interior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {g : E → EReal} {x : E}

/-- At an interior point of `dom f` the directional derivative is finite in every direction, so it
is the coercion of its own real value. -/
theorem dirDeriv_eq_coe_toReal_of_mem_interior_dom (hg : ConvexFn g) (hgp : Proper g)
    (hx : x ∈ interior (dom g)) (z : E) :
    dirDeriv g x z = (((dirDeriv g x z).toReal : ℝ) : EReal) := by
  have hri : x ∈ ri (dom g) := Convex.interior_subset_relint hg.convex_dom ⟨x, hx⟩ hx
  have hbot : dirDeriv g x z ≠ ⊥ := (proper_dirDeriv_of_mem_relint_dom hg hgp hri).ne_bot z
  have hdom := (dom_dirDeriv_eq_univ_iff_mem_interior_dom hg hgp hri).2 hx
  have htop : dirDeriv g x z ≠ ⊤ := (mem_dom.1 (hdom ▸ Set.mem_univ z)).ne
  exact (_root_.EReal.coe_toReal htop hbot).symm

/-- At an interior point of `dom f` the directional derivative is a *finite* convex function on the
whole space. -/
theorem convexOn_toReal_dirDeriv (hg : ConvexFn g) (hgp : Proper g)
    (hx : x ∈ interior (dom g)) :
    ConvexOn ℝ (univ : Set E) fun z => (dirDeriv g x z).toReal := by
  have hri : x ∈ ri (dom g) := Convex.interior_subset_relint hg.convex_dom ⟨x, hx⟩ hx
  have hdom := (dom_dirDeriv_eq_univ_iff_mem_interior_dom hg hgp hri).2 hx
  have hxdom : x ∈ dom g := interior_subset hx
  have h := (convexFn_dirDeriv hg (mem_dom.1 hxdom).ne (hgp.ne_bot x)).convexOn_toReal_dom
    (proper_dirDeriv_of_mem_relint_dom hg hgp hri)
  rwa [hdom] at h

/-- Positive homogeneity of the directional derivative, read on real values. -/
theorem toReal_dirDeriv_smul (hg : ConvexFn g) (hgp : Proper g) (hx : x ∈ interior (dom g))
    {c : ℝ} (hc : 0 < c) (z : E) :
    (dirDeriv g x (c • z)).toReal = c * (dirDeriv g x z).toReal := by
  have h := posHomogeneous_dirDeriv g x c hc z
  rw [dirDeriv_eq_coe_toReal_of_mem_interior_dom hg hgp hx z, ← _root_.EReal.coe_mul] at h
  rw [h, _root_.EReal.toReal_coe]

end Interior

/-! ### Continuous convergence -/

section Eval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Set E} {f : ℕ → E → ℝ} {g : E → ℝ}

/-- Convex functions converging pointwise on an open convex set converge **continuously** there:
the values `f i (x i)` along any sequence `x i → x` converge to `g x`.

This is the practical form of the theorem that pointwise convergence of convex functions is
uniform on compact subsets: a closed ball around `x` inside `U` is compact, uniform convergence
holds on it, and the limit is continuous. -/
theorem tendsto_eval_of_tendsto (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexOn ℝ U (f i)) (hg : ConvexOn ℝ U g)
    (hconv : ∀ z ∈ U, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    {x : E} (hx : x ∈ U) {xs : ℕ → E} (hxs : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun i => f i (xs i)) atTop (𝓝 (g x)) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hhalf : 0 < r / 2 := by linarith
  have hSU : Metric.closedBall x (r / 2) ⊆ U := fun z hz =>
    hball (Metric.closedBall_subset_ball (by linarith) hz)
  have huc := tendstoUniformlyOn_of_tendsto hU hUc hf hconv
    (isCompact_closedBall x (r / 2)) hSU
  have hcont : ContinuousWithinAt g (Metric.closedBall x (r / 2)) x := by
    have hgU : ContinuousOn g U := by
      rw [← hU.interior_eq]; exact hg.continuousOn_interior
    exact ((hgU.continuousAt (hU.mem_nhds hx)).continuousWithinAt)
  have hnw : Tendsto xs atTop (𝓝[Metric.closedBall x (r / 2)] x) :=
    tendsto_nhdsWithin_iff.2 ⟨hxs, hxs.eventually_mem (Metric.closedBall_mem_nhds x hhalf)⟩
  exact huc.tendsto_comp hcont hnw

end Eval

/-! ### Upper semicontinuity of the directional derivative -/

section DirDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Set E} {f : ℕ → E → EReal} {g : E → EReal}

/-- **Directional derivatives are upper semicontinuous under pointwise convergence.** If convex
functions `f i`, finite on an open convex `U`, converge pointwise there to `g`, and if
`x i → x ∈ U` and `y i → y`, then

```
limsup_i (f i)'(x i; y i) ≤ g'(x; y).
```

The `limsup` is spelled without junk values: every real `μ` above `g'(x; y)` eventually bounds
`(f i)'(x i; y i)`.

The proof is Rockafellar's. A single step `a > 0` with `x + a y ∈ U` realises a difference quotient
of `g` below `μ`; continuous convergence transports it to `f i` at the moving points `x i` and
`x i + a y i`; and the difference quotient dominates the directional derivative. -/
theorem eventually_dirDeriv_lt (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexFn (f i)) (hfp : ∀ i, Proper (f i)) (hfU : ∀ i, U ⊆ dom (f i))
    (hg : ConvexFn g) (hgp : Proper g) (hgU : U ⊆ dom g)
    (hconv : ∀ z ∈ U, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    {x : E} (hx : x ∈ U) {xs : ℕ → E} (hxs : Tendsto xs atTop (𝓝 x))
    {y : E} {ys : ℕ → E} (hys : Tendsto ys atTop (𝓝 y))
    {μ : ℝ} (hμ : dirDeriv g x y < (μ : EReal)) :
    ∀ᶠ i in atTop, dirDeriv (f i) (xs i) (ys i) < (μ : EReal) := by
  set F : ℕ → E → ℝ := fun i z => (f i z).toReal with hFdef
  set G : E → ℝ := fun z => (g z).toReal with hGdef
  have hgeq : ∀ z ∈ U, g z = ((G z : ℝ) : EReal) := fun z hz =>
    (_root_.EReal.coe_toReal (mem_dom.1 (hgU hz)).ne (hgp.ne_bot z)).symm
  have hfeq : ∀ i, ∀ z ∈ U, f i z = ((F i z : ℝ) : EReal) := fun i z hz =>
    (_root_.EReal.coe_toReal (mem_dom.1 (hfU i hz)).ne ((hfp i).ne_bot z)).symm
  have hFconv : ∀ i, ConvexOn ℝ U (F i) := fun i =>
    ((hf i).convexOn_toReal_dom (hfp i)).subset (hfU i) hUc
  have hGconv : ConvexOn ℝ U G := (hg.convexOn_toReal_dom hgp).subset hgU hUc
  have hconvR : ∀ z ∈ U, Tendsto (fun i => F i z) atTop (𝓝 (G z)) := by
    intro z hz
    rw [← _root_.EReal.tendsto_coe]
    have hfun : (fun i => ((F i z : ℝ) : EReal)) = fun i => f i z := by
      funext i; exact (hfeq i z hz).symm
    rw [hfun, ← hgeq z hz]
    exact hconv z hz
  -- A step `a > 0` small enough to stay in `U` and to realise a quotient below `μ`.
  obtain ⟨a₀, ha₀, hlt0⟩ := dirDeriv_lt_iff.1 hμ
  have hmemU : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • y ∈ U := by
    have hc : Continuous fun t : ℝ => x + t • y := by fun_prop
    have hc0 := hc.tendsto 0
    simp only [zero_smul, add_zero] at hc0
    exact hc0.eventually_mem (hU.mem_nhds hx)
  obtain ⟨δ, hδ, hδU⟩ := Metric.eventually_nhds_iff.1 hmemU
  set a : ℝ := min a₀ (δ / 2) with hadef
  have ha : 0 < a := lt_min ha₀ (by linarith)
  have haU : x + a • y ∈ U := by
    refine hδU ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos ha]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hq : (g (x + a • y) - g x) / (a : EReal) < (μ : EReal) :=
    lt_of_le_of_lt (monotoneOn_sub_div hg (hgeq x hx) y (mem_Ioi.2 ha) (mem_Ioi.2 ha₀)
      (min_le_left _ _)) hlt0
  have hquotR : (G (x + a • y) - G x) / a < μ := by
    rw [hgeq _ haU, hgeq x hx, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div,
      _root_.EReal.coe_lt_coe_iff] at hq
    exact hq
  -- Continuous convergence at the two moving points.
  have hzs : Tendsto (fun i => xs i + a • ys i) atTop (𝓝 (x + a • y)) := hxs.add (hys.const_smul a)
  have hev1 : Tendsto (fun i => F i (xs i)) atTop (𝓝 (G x)) :=
    tendsto_eval_of_tendsto hU hUc hFconv hGconv hconvR hx hxs
  have hev2 : Tendsto (fun i => F i (xs i + a • ys i)) atTop (𝓝 (G (x + a • y))) :=
    tendsto_eval_of_tendsto hU hUc hFconv hGconv hconvR haU hzs
  have hevlt : ∀ᶠ i in atTop, (F i (xs i + a • ys i) - F i (xs i)) / a < μ :=
    ((hev2.sub hev1).div_const a).eventually_lt_const hquotR
  filter_upwards [hevlt, hxs.eventually_mem (hU.mem_nhds hx),
    hzs.eventually_mem (hU.mem_nhds haU)] with i hi hiU hiU'
  calc dirDeriv (f i) (xs i) (ys i)
      ≤ (f i (xs i + a • ys i) - f i (xs i)) / (a : EReal) := dirDeriv_le _ _ _ ha
    _ = (((F i (xs i + a • ys i) - F i (xs i)) / a : ℝ) : EReal) := by
        rw [hfeq i _ hiU', hfeq i _ hiU, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div]
    _ < (μ : EReal) := by exact_mod_cast hi

end DirDeriv

/-! ### The local form, for a single function -/

section LocalDirDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- **`f'(x; y)` is upper semicontinuous in `(x, y)` on `int (dom f) × E`.**

This is the previous theorem for the constant sequence `f, f, f, …`: a convex function converges
pointwise to itself. Only the value at `(x, y)` moves, so the conclusion is a statement about the
neighbourhood filter, obtained from the sequential one because `𝓝 (x, y)` is countably
generated. -/
theorem upperSemicontinuousAt_dirDeriv (hf : ConvexFn f) (hfp : Proper f)
    (hx : x ∈ interior (dom f)) (y : E) :
    UpperSemicontinuousAt (fun p : E × E => dirDeriv f p.1 p.2) (x, y) := by
  intro c hc
  obtain ⟨μ, hμ₁, hμ₂⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hc
  have h : ∀ᶠ p : E × E in 𝓝 (x, y), dirDeriv f p.1 p.2 < (μ : EReal) := by
    rw [Filter.eventually_iff_seq_eventually]
    intro ps hps
    rw [nhds_prod_eq] at hps
    exact eventually_dirDeriv_lt isOpen_interior hf.convex_dom.interior (fun _ => hf)
      (fun _ => hfp) (fun _ => interior_subset) hf hfp interior_subset
      (fun z _ => tendsto_const_nhds) hx hps.fst hps.snd hμ₁
  exact h.mono fun p hp => hp.trans hμ₂

end LocalDirDeriv

/-! ### Upper semicontinuity of the subdifferential -/

section Subgradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Set E} {f : ℕ → E → EReal} {g : E → EReal} {x : E}

/-- The support function of `∂f x` is `f'(x; ·)`, for a real inner-product space paired with
itself. This is Theorem 23.4 with `⟨·, ·⟩` in place of a general pairing. -/
theorem supportFn_subgradient (hg : ConvexFn g) (hgp : Proper g) (hx : x ∈ ri (dom g)) :
    supportFn (innerₗ E) (subgradient (innerₗ E) g x) = dirDeriv g x := by
  rw [dirDeriv_eq_supportFn_of_mem_relint_dom (B := innerₗ E) hg hgp hx, flip_innerₗ]

/-- **Subdifferentials are upper semicontinuous under pointwise convergence.** If convex functions
`f i`, finite on an open convex `U`, converge pointwise there to `g`, and `x i → x` inside `U`,
then for every `ε > 0`

```
∂(f i)(x i) ⊆ ∂g(x) + ε B
```

for all large `i`, where `B` is the closed unit ball.

The subdifferentials are the support sets of the directional derivatives, and the previous theorem
bounds those pointwise. On the compact unit ball the bound becomes uniform — this is the step where
Theorem 10.8 is used a second time, now for the sublinear functions `f i'(x i; ·)` — and positive
homogeneity spreads it to `f i'(x i; y) ≤ g'(x; y) + ε ‖y‖` everywhere. Since `ε ‖·‖` is the
support function of `ε B`, the right-hand side is the support function of `∂g(x) + ε B`, and
support functions order closed convex sets. -/
theorem eventually_subgradient_subset_add_closedBall (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexFn (f i)) (hfp : ∀ i, Proper (f i)) (hfU : ∀ i, U ⊆ dom (f i))
    (hg : ConvexFn g) (hgp : Proper g) (hgU : U ⊆ dom g)
    (hconv : ∀ z ∈ U, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    (hx : x ∈ U) {xs : ℕ → E} (hxs : Tendsto xs atTop (𝓝 x)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, subgradient (innerₗ E) (f i) (xs i)
      ⊆ subgradient (innerₗ E) g x + Metric.closedBall (0 : E) ε := by
  classical
  -- Replace `xs` by a sequence lying in `U` for *every* index; the two agree eventually.
  have hxsU : ∀ᶠ i in atTop, xs i ∈ U := hxs.eventually_mem (hU.mem_nhds hx)
  set xs' : ℕ → E := fun i => if xs i ∈ U then xs i else x with hxs'def
  have hxs'eq : ∀ᶠ i in atTop, xs' i = xs i :=
    hxsU.mono fun i hi => by simp only [hxs'def, hi, ite_true]
  have hxsU' : ∀ i, xs' i ∈ U := fun i => by
    simp only [hxs'def]
    split
    · assumption
    · exact hx
  have hxs' : Tendsto xs' atTop (𝓝 x) := hxs.congr' (hxs'eq.mono fun i hi => hi.symm)
  suffices h : ∀ᶠ i in atTop, subgradient (innerₗ E) (f i) (xs' i)
      ⊆ subgradient (innerₗ E) g x + Metric.closedBall (0 : E) ε by
    filter_upwards [h, hxs'eq] with i hi hieq
    rwa [hieq] at hi
  have hxint : x ∈ interior (dom g) := interior_maximal hgU hU hx
  have hxsint : ∀ i, xs' i ∈ interior (dom (f i)) := fun i => interior_maximal (hfU i) hU (hxsU' i)
  have hxri : x ∈ ri (dom g) := Convex.interior_subset_relint hg.convex_dom ⟨x, hxint⟩ hxint
  have hxsri : ∀ i, xs' i ∈ ri (dom (f i)) := fun i =>
    Convex.interior_subset_relint (hf i).convex_dom ⟨_, hxsint i⟩ (hxsint i)
  -- The pointwise bound of the previous theorem, in real form.
  have hle : ∀ z ∈ (univ : Set E), ∀ δ > 0, ∀ᶠ i in atTop,
      (dirDeriv (f i) (xs' i) z).toReal ≤ (dirDeriv g x z).toReal + δ := by
    intro z _ δ hδ
    have hlt : dirDeriv g x z < (((dirDeriv g x z).toReal + δ : ℝ) : EReal) :=
      lt_of_eq_of_lt (dirDeriv_eq_coe_toReal_of_mem_interior_dom hg hgp hxint z)
        (_root_.EReal.coe_lt_coe_iff.2 (by linarith))
    filter_upwards [eventually_dirDeriv_lt hU hUc hf hfp hfU hg hgp hgU hconv hx hxs'
      (ys := fun _ => z) tendsto_const_nhds hlt] with i hi
    rw [dirDeriv_eq_coe_toReal_of_mem_interior_dom (hf i) (hfp i) (hxsint i) z] at hi
    exact (_root_.EReal.coe_lt_coe_iff.1 hi).le
  -- Made uniform on the unit ball.
  have hunif : ∀ᶠ i in atTop, ∀ z ∈ Metric.closedBall (0 : E) 1,
      (dirDeriv (f i) (xs' i) z).toReal ≤ (dirDeriv g x z).toReal + ε :=
    eventually_forall_le_add_of_eventually_le isOpen_univ convex_univ
      (fun i => convexOn_toReal_dirDeriv (hf i) (hfp i) (hxsint i))
      (convexOn_toReal_dirDeriv hg hgp hxint) hle (isCompact_closedBall (0 : E) 1)
      (subset_univ _) hε
  filter_upwards [hunif] with i hi
  -- Spread over all directions by positive homogeneity.
  have hhom : ∀ z : E,
      dirDeriv (f i) (xs' i) z ≤ (((dirDeriv g x z).toReal + ε * ‖z‖ : ℝ) : EReal) := by
    intro z
    have hreal : (dirDeriv (f i) (xs' i) z).toReal ≤ (dirDeriv g x z).toReal + ε * ‖z‖ := by
      rcases eq_or_ne z 0 with rfl | hz
      · have h1 : dirDeriv (f i) (xs' i) 0 = 0 :=
          dirDeriv_zero (mem_dom.1 (hfU i (hxsU' i))).ne ((hfp i).ne_bot _)
        have h2 : dirDeriv g x 0 = 0 := dirDeriv_zero (mem_dom.1 (hgU hx)).ne (hgp.ne_bot _)
        simp [h1, h2]
      have hc : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
      have hwz : ‖z‖ • (‖z‖⁻¹ • z) = z := by
        rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
      have hwnorm : ‖(‖z‖⁻¹ : ℝ) • z‖ = 1 := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hc, inv_mul_cancel₀ hc.ne']
      have hb := hi ((‖z‖⁻¹ : ℝ) • z) (by rw [Metric.mem_closedBall, dist_zero_right, hwnorm])
      have hfz := toReal_dirDeriv_smul (hf i) (hfp i) (hxsint i) hc ((‖z‖⁻¹ : ℝ) • z)
      have hgz := toReal_dirDeriv_smul hg hgp hxint hc ((‖z‖⁻¹ : ℝ) • z)
      rw [hwz] at hfz hgz
      calc (dirDeriv (f i) (xs' i) z).toReal
          = ‖z‖ * (dirDeriv (f i) (xs' i) ((‖z‖⁻¹ : ℝ) • z)).toReal := hfz
        _ ≤ ‖z‖ * ((dirDeriv g x ((‖z‖⁻¹ : ℝ) • z)).toReal + ε) := by
            exact mul_le_mul_of_nonneg_left hb (norm_nonneg z)
        _ = ‖z‖ * (dirDeriv g x ((‖z‖⁻¹ : ℝ) • z)).toReal + ε * ‖z‖ := by ring
        _ = (dirDeriv g x z).toReal + ε * ‖z‖ := by rw [← hgz]
    rw [dirDeriv_eq_coe_toReal_of_mem_interior_dom (hf i) (hfp i) (hxsint i) z]
    exact_mod_cast hreal
  -- Support functions order the two sets.
  have hcpt : IsCompact (subgradient (innerₗ E) g x) := isCompact_subgradient hg hgp hxint
  have hcvx : Convex ℝ (subgradient (innerₗ E) g x + Metric.closedBall (0 : E) ε) :=
    (convex_subgradient _ _ _).add (convex_closedBall _ _)
  have hcptsum : IsCompact (subgradient (innerₗ E) g x + Metric.closedBall (0 : E) ε) :=
    hcpt.add (isCompact_closedBall _ _)
  have hsupple : supportFn (innerₗ E) (subgradient (innerₗ E) (f i) (xs' i))
      ≤ supportFn (innerₗ E) (subgradient (innerₗ E) g x + Metric.closedBall (0 : E) ε) := by
    intro z
    rw [supportFn_add, Pi.add_apply, supportFn_subgradient (hf i) (hfp i) (hxsri i),
      supportFn_subgradient hg hgp hxri, supportFn_closedBall hε.le]
    calc dirDeriv (f i) (xs' i) z ≤ (((dirDeriv g x z).toReal + ε * ‖z‖ : ℝ) : EReal) := hhom z
      _ = dirDeriv g x z + ((ε * ‖z‖ : ℝ) : EReal) := by
          rw [_root_.EReal.coe_add, ← dirDeriv_eq_coe_toReal_of_mem_interior_dom hg hgp hxint z]
  have hincl := (closure_convexHull_subset_iff_supportFn_le (B := innerₗ E) _ _).2 hsupple
  rw [hcvx.convexHull_eq, hcptsum.isClosed.closure_eq] at hincl
  exact fun w hw => hincl (subset_closure (subset_convexHull ℝ _ hw))

end Subgradient

/-! ### The local form of the subgradient statement -/

section LocalSubgradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- **`∂f` is upper semicontinuous at every interior point of `dom f`**: for every `ε > 0` the
inclusion `∂f z ⊆ ∂f x + ε B` holds for all `z` in a neighbourhood of `x`.

The constant-sequence case of the previous theorem, transported from sequences to the
neighbourhood filter. -/
theorem eventually_nhds_subgradient_subset_add_closedBall (hf : ConvexFn f) (hfp : Proper f)
    (hx : x ∈ interior (dom f)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 x, subgradient (innerₗ E) f z
      ⊆ subgradient (innerₗ E) f x + Metric.closedBall (0 : E) ε := by
  rw [Filter.eventually_iff_seq_eventually]
  intro zs hzs
  exact eventually_subgradient_subset_add_closedBall isOpen_interior hf.convex_dom.interior
    (fun _ => hf) (fun _ => hfp) (fun _ => interior_subset) hf hfp interior_subset
    (fun z _ => tendsto_const_nhds) hx hzs hε

end LocalSubgradient

end Tdaf.ConvexAnalysis
