/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Subgradient.Differentiability
import Tdaf.Analysis.Convex.Subgradient.EssentiallySmooth

/-!
# Condition (c) of essential smoothness, in directional-derivative form

Rockafellar's **Lemma 26.2**. Condition (c) in the definition of essential smoothness — the norms
of the gradients blow up at the boundary of `C = int (dom f)` — may be replaced, given (a) and (b),
by

```
(c')  f'(x + λ(a − x); a − x) ↓ −∞ as λ ↓ 0,   for every a ∈ C and every x ∉ C.
```

Both conditions say the same thing at a single point `x`, namely that `∂f x = ∅`: (c) does so by
Theorems 24.4 and 25.6, and (c') does so by Theorem 23.3 read through the one-dimensional
restriction of `f` to the line through `x` and `a` (Theorem 24.1).

## Main results

* `closedFn_lineRestrict`, `proper_lineRestrict_of_mem_dom`,
  `closedProperConvexFn_lineRestrict` — the restriction of a closed proper convex function to a
  line is closed proper convex, based at *any* point of the line, not only a point of `dom f`.
* `rightDeriv_lineRestrict_eq_dirDeriv` — `g'₊(t) = f'(x + t y; y)` for the restriction `g`, valid
  also where `g t = ⊤` (both sides are `−∞` there).
* `tendsto_dirDeriv_lineRestrict` — **Theorem 24.1** transported to the line: the directional
  derivative along the segment tends to `g'₊(0)` as the parameter decreases to `0`.
* `rightDeriv_lineRestrict_zero_eq_bot_iff` — `g'₊(0) = −∞` exactly when `∂f x = ∅`. This is the
  two-line case distinction of Rockafellar's proof, on whether `x ∈ dom f`.
* `subgradient_eq_empty_iff_tendsto_dirDeriv` — condition (c') at `x` is `∂f x = ∅`.
* `subgradient_eq_empty_iff_tendsto_norm_fderiv` — condition (c) at `x` is `∂f x = ∅`.
* `tendsto_norm_fderiv_iff_tendsto_dirDeriv` — **Lemma 26.2** at a single boundary point.
* `essentiallySmooth_iff_tendsto_dirDeriv` — **Rockafellar, Lemma 26.2**.

## Design notes

**`f` is assumed closed here, where Rockafellar assumes it "without loss of generality".** The book
observes that (c) and (c') see only the values of `f` on the open set `C`, and replaces `f` by its
closure. Formalising that reduction means transporting both conditions across `cl f`, which costs
more than it saves: every consumer in §26 — Theorem 26.1, Theorem 26.3, Corollary 26.4.1 — already
carries `ClosedFn f`, because Theorems 24.4 and 25.6 do.

**Condition (c') is a `Tendsto` to `𝓝 ⊥`, not a monotone-decrease statement.** Rockafellar's `↓`
records that `λ ↦ f'(x + λ(a−x); a−x)` is nondecreasing, which is `monotone_rightDeriv` for the
restriction; the *content* of (c') is the value of the limit, and separating the two keeps the
statement free of a monotonicity hypothesis that the equivalence does not use.

**The pivot is `∂f x = ∅`, not a direct implication.** Rockafellar's proof also runs through it,
but only implicitly ("as demonstrated in the proof of Theorem 26.1"); here the two halves are
separate named theorems, so that either can be used on its own — condition (c) as a criterion for
subdifferentiability is what Theorem 26.1's own proof wants, and condition (c') is what a user with
a concrete `f` can check.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §26 (Lemma 26.2).
-/

namespace Tdaf.ConvexAnalysis

open Filter Metric Topology

/-! ### The restriction to a line, based at an arbitrary point -/

section LineRestrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {x y : E}

/-- The restriction of a closed function to a line is closed: it is the composite with a continuous
map, and lower semicontinuity survives that. -/
theorem closedFn_lineRestrict (hp : Proper f) (hcl : ClosedFn f) (x y : E) :
    ClosedFn fun t : ℝ => f (x + t • y) := by
  have hcont : Continuous fun s : ℝ => x + s • y := by fun_prop
  exact (closedFn_iff_lowerSemicontinuous fun _ => hp.ne_bot _).2 fun t c hc =>
    (hcont.tendsto t).eventually (hcl.lowerSemicontinuous _ c hc)

/-- The restriction of a proper function to a line is proper as soon as the line meets `dom f`.

`proper_lineRestrict` asks for the *base point* to lie in `dom f`; Lemma 26.2 restricts along a
segment whose base point `x` is precisely the one that may fail to. -/
theorem proper_lineRestrict_of_mem_dom (hp : Proper f) {t₀ : ℝ} (ht : x + t₀ • y ∈ dom f) :
    Proper fun t : ℝ => f (x + t • y) :=
  ⟨⟨t₀, ht⟩, fun _ => hp.ne_bot _⟩

/-- The restriction of a closed proper convex function to a line meeting `dom f` is closed proper
convex — which is what the one-dimensional theory of `Subgradient/OneDim.lean` runs on. -/
theorem closedProperConvexFn_lineRestrict (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    {t₀ : ℝ} (ht : x + t₀ • y ∈ dom f) :
    ClosedProperConvexFn fun t : ℝ => f (x + t • y) :=
  ⟨convexFn_lineRestrict hf x y, closedFn_lineRestrict hp hcl x y,
    proper_lineRestrict_of_mem_dom hp ht⟩

/-- **The right derivative of the restriction is the directional derivative along the line.**

Both sides are `−∞` where `f (x + t y) = ⊤`, so the only hypothesis needed is that the line meets
`dom f` somewhere to the right of `t` — without it `g'₊(t)` is `+∞` by fiat while the directional
derivative is not. -/
theorem rightDeriv_lineRestrict_eq_dirDeriv (hp : Proper f) (x y : E) {t : ℝ}
    (ht : ∃ s, t < s ∧ f (x + s • y) < ⊤) :
    rightDeriv (fun s : ℝ => f (x + s • y)) t = dirDeriv f (x + t • y) y := by
  rcases eq_or_lt_of_le (le_top : f (x + t • y) ≤ ⊤) with htop | htop
  · rw [rightDeriv_eq_bot_of_eq_top htop ht, dirDeriv_eq_bot_of_eq_top htop y]
  · rw [rightDeriv_eq_dirDeriv htop (hp.ne_bot _), dirDeriv_lineRestrict, one_smul]

end LineRestrict

/-! ### Theorem 24.1 along a segment -/

section LineSegment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {a : E}

/-- **Rockafellar's Theorem 24.1 along the segment from `x` to `a`.** The directional derivative
`f'(x + t(a − x); a − x)` tends, as `t` decreases to `0`, to the right derivative at `0` of the
restriction of `f` to that line.

The two functions agree on `(0, 1)` — where the line still meets `dom f` to the right — which is a
neighbourhood of `0` inside `(0, ∞)`, so the limit transfers. -/
theorem tendsto_dirDeriv_lineRestrict (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (ha : a ∈ dom f) (x : E) :
    Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0)
      (𝓝 (rightDeriv (fun s : ℝ => f (x + s • (a - x))) 0)) := by
  set y : E := a - x with hy
  have hone : x + (1 : ℝ) • y = a := by rw [hy]; module
  have hcpc : ClosedProperConvexFn fun s : ℝ => f (x + s • y) :=
    closedProperConvexFn_lineRestrict hf hp hcl (t₀ := 1) (by rw [hone]; exact ha)
  refine (tendsto_rightDeriv_nhdsWithin_Ioi hcpc 0).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  exact rightDeriv_lineRestrict_eq_dirDeriv hp x y ⟨1, ht.2, by rw [hone]; exact mem_dom.1 ha⟩

end LineSegment

/-! ### Condition (c') at a single point -/

section Condition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {a x : E}


/-- **`g'₊(0) = −∞` exactly when `f` has no subgradient at `x`**, where `g` is the restriction of
`f` to the line from `x` towards a relative interior point `a` of `dom f`.

Rockafellar's case distinction: off `dom f` the right derivative of the restriction is `−∞` by fiat
and there is no subgradient either; on `dom f` the right derivative is `f'(x; a − x)`, and
Theorem 23.3 with Theorem 7.2 — packaged as `dirDeriv_eq_bot_of_subgradient_eq_empty` — makes that
value `−∞` exactly when `∂f x` is empty. -/
theorem rightDeriv_lineRestrict_zero_eq_bot_iff (hf : ConvexFn f) (hp : Proper f)
    (ha : a ∈ ri (dom f)) (x : E) :
    rightDeriv (fun s : ℝ => f (x + s • (a - x))) 0 = ⊥ ↔ subgradient (innerₗ E) f x = ∅ := by
  set y : E := a - x with hy
  have hone : x + (1 : ℝ) • y = a := by rw [hy]; module
  have hex : ∃ s, (0 : ℝ) < s ∧ f (x + s • y) < ⊤ :=
    ⟨1, zero_lt_one, by rw [hone]; exact mem_dom.1 (intrinsicInterior_subset ha)⟩
  rw [rightDeriv_lineRestrict_eq_dirDeriv hp x y hex, zero_smul, add_zero]
  rcases eq_or_lt_of_le (le_top : f x ≤ ⊤) with htop | htop
  · refine ⟨fun _ => ?_, fun _ => dirDeriv_eq_bot_of_eq_top htop y⟩
    refine Set.eq_empty_of_forall_notMem fun v hv => ?_
    exact absurd (mem_dom.1 (mem_dom_of_mem_subgradient hp hv)) (by rw [htop]; simp)
  · refine ⟨fun hbot => ?_, fun hempty => ?_⟩
    · exact (subgradient_eq_empty_iff_exists_dirDeriv_eq_bot (B := innerₗ E) hf htop.ne
        (hp.ne_bot x)).2 ⟨y, hbot⟩
    · have h := dirDeriv_eq_bot_of_subgradient_eq_empty (B := innerₗ E) hf htop.ne
        (hp.ne_bot x) hempty ha
      rwa [hy]

/-- **Condition (c') at `x` says exactly that `f` has no subgradient at `x`.** -/
theorem subgradient_eq_empty_iff_tendsto_dirDeriv (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) (ha : a ∈ ri (dom f)) (x : E) :
    subgradient (innerₗ E) f x = ∅ ↔
      Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥) := by
  have htend := tendsto_dirDeriv_lineRestrict hf hp hcl (intrinsicInterior_subset ha) x
  refine ⟨fun hempty => ?_, fun hlim => ?_⟩
  · rwa [(rightDeriv_lineRestrict_zero_eq_bot_iff hf hp ha x).2 hempty] at htend
  · exact (rightDeriv_lineRestrict_zero_eq_bot_iff hf hp ha x).1
      (tendsto_nhds_unique htend hlim)

/-- **Condition (c) at `x` says exactly that `f` has no subgradient at `x`.**

Forwards is Theorem 24.4: a bounded subsequence of gradients has a convergent sub-subsequence,
whose limit is a subgradient at `x`. Backwards is Theorem 25.6 in its weak form: a subgradient at
`x` makes `S(x)` non-empty, i.e. produces a *convergent* sequence of gradients, which condition (c)
forbids. -/
theorem subgradient_eq_empty_iff_tendsto_norm_fderiv (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) (hne : (interior (dom f)).Nonempty)
    (hdiff : ∀ ⦃z : E⦄, z ∈ interior (dom f) → DifferentiableAtFn f z) (x : E) :
    subgradient (innerₗ E) f x = ∅ ↔
      ∀ zs : ℕ → E, (∀ i, zs i ∈ interior (dom f)) → Tendsto zs atTop (𝓝 x) →
        Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop := by
  constructor
  · intro hempty zs hzs hlim
    by_contra hcon
    -- A bounded subsequence of gradients, converging after a second extraction.
    obtain ⟨b, hb⟩ := not_forall.1 (Filter.tendsto_atTop.not.1 hcon)
    obtain ⟨φ, hφ, hφb⟩ := Filter.extraction_of_frequently_atTop (Filter.not_eventually.1 hb)
    set vs : ℕ → E := fun i => (InnerProductSpace.toDual ℝ E).symm
      (fderiv ℝ (fun w => (f w).toReal) (zs i)) with hvsdef
    have hgrad : ∀ i, HasGradientAt f (InnerProductSpace.toDual ℝ E (vs i)) (zs i) := fun i => by
      rw [hvsdef, LinearIsometryEquiv.apply_symm_apply]
      exact (hdiff (hzs i)).hasGradientAt_fderiv
    have hvsb : ∀ n, vs (φ n) ∈ closedBall (0 : E) b := fun n => by
      rw [mem_closedBall_zero_iff, hvsdef, LinearIsometryEquiv.norm_map]
      exact (not_le.1 (hφb n)).le
    obtain ⟨w, -, ψ, hψ, hψlim⟩ := (isCompact_closedBall (0 : E) b).tendsto_subseq hvsb
    have hmem : w ∈ gradientLimits f x :=
      ⟨fun n => zs (φ (ψ n)), fun n => vs (φ (ψ n)), hlim.comp (hφ.comp hψ).tendsto_atTop,
        fun n => hgrad (φ (ψ n)), hψlim⟩
    exact absurd (gradientLimits_subset_subgradient hf hp hcl hmem) (by rw [hempty]; simp)
  · intro hc
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨v, hv⟩
    -- Theorem 25.6 turns a subgradient into a limit of gradients.
    rw [subgradient_eq_closure_convexHull_gradientLimits_add_normalCone hf hp hcl hne] at hv
    obtain ⟨u, hu, -, -, -⟩ := hv
    obtain ⟨w, xs, vs, hxs, hgrad, hvs⟩ : (gradientLimits f x).Nonempty := by
      rcases (gradientLimits f x).eq_empty_or_nonempty with hempty | hne'
      · rw [hempty, convexHull_empty, closure_empty] at hu
        exact absurd hu (Set.notMem_empty u)
      · exact hne'
    have hnorm : ∀ i, ‖fderiv ℝ (fun z => (f z).toReal) (xs i)‖ = ‖vs i‖ := fun i => by
      rw [(hgrad i).fderiv_toReal_eq, LinearIsometryEquiv.norm_map]
    have htop := hc xs (fun i => (hgrad i).mem_interior_dom) hxs
    rw [tendsto_congr hnorm] at htop
    exact not_tendsto_atTop_of_tendsto_nhds hvs.norm htop

/-- **Rockafellar, Lemma 26.2**, at a single point: given (a) and (b), condition (c) at `x` and
condition (c') at `x` in the direction of any `a ∈ C` say the same thing. -/
theorem tendsto_norm_fderiv_iff_tendsto_dirDeriv (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) (hne : (interior (dom f)).Nonempty)
    (hdiff : ∀ ⦃z : E⦄, z ∈ interior (dom f) → DifferentiableAtFn f z)
    (ha : a ∈ interior (dom f)) (x : E) :
    (∀ zs : ℕ → E, (∀ i, zs i ∈ interior (dom f)) → Tendsto zs atTop (𝓝 x) →
        Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop)
      ↔ Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥) :=
  (subgradient_eq_empty_iff_tendsto_norm_fderiv hf hp hcl hne hdiff x).symm.trans
    (subgradient_eq_empty_iff_tendsto_dirDeriv hf hp hcl
      (Convex.interior_subset_relint hf.convex_dom hne ha) x)

/-- **Rockafellar, Lemma 26.2**: for a closed proper convex function satisfying (a) and (b),
essential smoothness is condition (c'), the collapse of the directional derivative to `−∞` along
every segment reaching a point outside `C = int (dom f)`. -/
theorem essentiallySmooth_iff_tendsto_dirDeriv (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hne : (interior (dom f)).Nonempty)
    (hdiff : ∀ ⦃z : E⦄, z ∈ interior (dom f) → DifferentiableAtFn f z) :
    EssentiallySmooth f ↔ ∀ x ∉ interior (dom f), ∀ a ∈ interior (dom f),
      Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥) := by
  constructor
  · intro hes x hx a haC
    exact (tendsto_norm_fderiv_iff_tendsto_dirDeriv hf hp hcl hne hdiff haC x).1
      (hes.tendsto_norm_fderiv hx)
  · intro hc
    obtain ⟨a, haC⟩ := id hne
    exact ⟨hne, hdiff, fun z hz =>
      (tendsto_norm_fderiv_iff_tendsto_dirDeriv hf hp hcl hne hdiff haC z).2 (hc z hz a haC)⟩

end Condition

end Tdaf.ConvexAnalysis
