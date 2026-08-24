/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Level
import Tdaf.Analysis.Convex.Subgradient.LegendreType

/-!
# Co-finiteness and the blow-up of the gradient

Rockafellar's **Lemma 26.7**: a finite differentiable convex function on `Rⁿ` is *co-finite*
exactly when

```
‖∇f xᵢ‖ → ∞   for every sequence with   ‖xᵢ‖ → ∞.
```

This is the criterion that makes Theorem 26.6 usable: it turns the co-finiteness hypothesis, which
is about the recession function — equivalently about `dom f*` — into a statement one can check on
the gradient mapping alone.

## Main results

* `forall_tendsto_norm_atTop_iff_isBounded` — the sequential condition is the statement that every
  sublevel set `{x | ‖g x‖ ≤ b}` of `‖g‖` is bounded. Pure metric bookkeeping, for an arbitrary
  `g`, and it is what removes all sequence extraction from the two halves below.
* `isBounded_setOf_norm_gradient_le_of_dom_conj_eq_univ` — the easy half, from **Theorem 24.7**:
  when `dom f* = E`, the set of points whose gradient lies in a ball is `∂f*` of that ball, hence
  compact.
* `gradientRange_subset_interior_dom_conj_of_isBounded` — the hard half, first step: `∇f(E)` is
  contained in `int (dom f*)`, because a non-zero normal to `dom f*` at a point of `∇f(E)` would
  produce a half-line of points carrying the *same* gradient.
* `isClosed_gradientRange_of_isBounded` — the hard half, second step: `∇f(E)` is closed.
* `dom_conj_eq_univ_of_isBounded` — the hard half: `∇f(E)` is a non-empty clopen subset of `E`,
  hence everything.
* `cofinite_iff_forall_tendsto_norm_gradient_atTop` — **Rockafellar, Lemma 26.7**.

## Design notes

**The proof of the hard half is not Rockafellar's, and the difference is deliberate.** The book
argues at a boundary point `x*` of `dom f*` and splits on whether `∂f*(x*)` is empty or unbounded.
Producing such a boundary point means running the "the segment from an interior point to an
exterior point crosses the boundary" argument, and the empty case then needs a sequence in
`ri (dom f*)` converging to `x*` together with Theorem 24.4. Both are avoided here: `D = ∇f(E)` is
shown to be open (Corollary 11.6.1, through the normal cone) and closed (Theorem 25.5, continuity
of `∇f`), and `E` is connected. The book's two cases are exactly the two ways `D` could fail to be
clopen.

**The half-line is what replaces "`∂f*(x*)` is unbounded".** If `n ≠ 0` is normal to `dom f*` at
`x* ∈ D`, then `∂f*(x*) + N_{dom f*}(x*) ⊆ ∂f*(x*)` (`subgradient_add_normalCone_dom_subset`) puts
a whole half-line `x + t n`, `t ≥ 0`, inside `∂f*(x*)`; every point of it has gradient `x*`, so the
sublevel set `{y | ‖∇f y‖ ≤ ‖x*‖}` is unbounded. No appeal to Theorem 23.4's boundedness clause is
needed, and in particular the `x ∈ ri (dom f)` hypothesis that clause carries never has to be
supplied for `f*`.

**Co-finiteness is `Cofinite` from §13, not `dom f* = E`.** Theorem 26.6 in `LegendreType.lean`
states its co-finiteness hypothesis as `dom f* = E` because the recession function does not appear
in its proof; here the recession-function form is the *statement*, so `Cofinite` is used and
Corollary 13.3.1 (`cofinite_iff_dom_conj_eq_univ`) does the translation once.

## What is not here

**Nothing is claimed for a merely essentially smooth `f`.** Rockafellar states Lemma 26.7 for a
*finite* differentiable convex function, and the finiteness is not decoration: it is what makes
`∇f` defined at every point, so that "`‖xᵢ‖ → ∞` implies `‖∇f xᵢ‖ → ∞`" quantifies over all
sequences rather than over sequences inside `int (dom f)`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §26 (Lemma 26.7).
-/

namespace Tdaf.ConvexAnalysis

open Filter Metric Topology Set

/-! ### Sequences going to infinity versus bounded sublevel sets -/

section Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- **`‖g xᵢ‖ → ∞` along every sequence with `‖xᵢ‖ → ∞` is boundedness of every sublevel set of
`‖g‖`.** No convexity and no linearity: this is the translation between Rockafellar's sequential
phrasing of Lemma 26.7 and the phrasing the two halves of its proof actually use. -/
theorem forall_tendsto_norm_atTop_iff_isBounded (g : E → F) :
    (∀ xs : ℕ → E, Tendsto (fun i => ‖xs i‖) atTop atTop →
        Tendsto (fun i => ‖g (xs i)‖) atTop atTop)
      ↔ ∀ b : ℝ, Bornology.IsBounded {x : E | ‖g x‖ ≤ b} := by
  constructor
  · intro h b
    by_contra hcon
    rw [isBounded_iff_forall_norm_le] at hcon
    push Not at hcon
    choose xs hxs hxn using fun n : ℕ => hcon (n : ℝ)
    have hxtop : Tendsto (fun i => ‖xs i‖) atTop atTop :=
      tendsto_atTop_mono (fun i => (hxn i).le) tendsto_natCast_atTop_atTop
    obtain ⟨i, hi⟩ := ((h xs hxtop).eventually_ge_atTop (b + 1)).exists
    have hbi : ‖g (xs i)‖ ≤ b := hxs i
    linarith
  · intro h xs hxs
    rw [Filter.tendsto_atTop]
    intro b
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (h b)
    filter_upwards [hxs.eventually_gt_atTop R] with i hi
    by_contra hcon
    exact absurd (hR (xs i) (not_le.1 hcon).le) (by linarith)

end Metric

/-! ### Lemma 26.7 -/

section Lemma267

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- **The easy half of Lemma 26.7.** If `dom f* = E` then `{x | ‖∇f x‖ ≤ b}` is bounded.

The set is contained in `∂f*` of the closed ball of radius `b`, because `∇f x = v` says
`x ∈ ∂f*(v)` (Corollary 23.5.1), and Theorem 24.7 makes that image compact. -/
theorem isBounded_setOf_norm_gradient_le_of_dom_conj_eq_univ (hf : ConvexFn f) (hp : Proper f)
    (hdom : dom f = univ) (hdiff : ∀ z : E, DifferentiableAtFn f z)
    (hdc : dom (conj (innerₗ E) f) = univ) (b : ℝ) :
    Bornology.IsBounded {x : E | ‖gradient (fun w => (f w).toReal) x‖ ≤ b} := by
  have hcl : ClosedFn f := closedFn_of_dom_eq_univ hf hp hdom
  have hes : EssentiallySmooth f := essentiallySmooth_of_dom_eq_univ hdom hdiff
  have hgcpc : ClosedProperConvexFn (conj (innerₗ E) f) :=
    ⟨convexFn_conj _ f, closedFn_conj, proper_conj ⟨hf, hcl, hp⟩⟩
  have hcomp := isCompact_image_subgradientRel hgcpc (isCompact_closedBall (0 : E) b)
    (by rw [hdc, interior_univ]; exact subset_univ _)
  refine hcomp.isBounded.subset fun x hx => ⟨gradient (fun w => (f w).toReal) x, ?_, ?_⟩
  · exact mem_closedBall_zero_iff.2 hx
  · rw [mem_subgradientRel, mem_subgradient_conj_innerL_iff hf hcl,
      ← hasGradientAt_toDual_iff_mem_subgradient hf hp hcl hes]
    exact (hdiff x).hasGradientAt_gradient

/-- **The hard half of Lemma 26.7, first step**: the range of `∇f` lies inside `int (dom f*)`.

A non-zero `n` normal to `dom f*` at `v = ∇f x` may be added to `x` with any non-negative
coefficient without leaving `∂f*(v)`, so the whole half-line `x + t n` has gradient `v` — and then
`{y | ‖∇f y‖ ≤ ‖v‖}` is unbounded. With the normal cone trivial, Corollary 11.6.1
(`mem_interior_of_normalCone_eq_zero`) puts `v` in the interior. -/
theorem gradientRange_subset_interior_dom_conj_of_isBounded (hf : ConvexFn f) (hp : Proper f)
    (hdom : dom f = univ) (hdiff : ∀ z : E, DifferentiableAtFn f z)
    (hbd : ∀ b : ℝ, Bornology.IsBounded {x : E | ‖gradient (fun w => (f w).toReal) x‖ ≤ b}) :
    gradientRange f ⊆ interior (dom (conj (innerₗ E) f)) := by
  have hcl : ClosedFn f := closedFn_of_dom_eq_univ hf hp hdom
  have hes : EssentiallySmooth f := essentiallySmooth_of_dom_eq_univ hdom hdiff
  intro v hv
  refine mem_interior_of_normalCone_eq_zero (B := innerₗ E) (convexFn_conj _ f).convex_dom
    (gradientRange_subset_dom_conj hf hp hcl hes hv) ?_
  refine eq_singleton_iff_unique_mem.2 ⟨fun z _ => by simp, fun n hn => ?_⟩
  by_contra hn0
  -- A point of `∂f*(v)`, supplied by Corollary 26.4.1.
  obtain ⟨x, hx⟩ : (subgradient (innerₗ E) (conj (innerₗ E) f) v).Nonempty := by
    rw [← mem_domSubgradient, ← gradientRange_eq_domSubgradient_conj hf hp hcl hes]
    exact hv
  -- The half-line `x + t n` stays inside `∂f*(v)`, so its gradient is constantly `v`.
  have hline : ∀ t : ℝ, 0 ≤ t → ‖gradient (fun w => (f w).toReal) (x + t • n)‖ = ‖v‖ := by
    intro t ht
    have hsmul : t • n ∈ normalCone (innerₗ E) (dom (conj (innerₗ E) f)) v := by
      intro z hz
      rw [map_smul, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos ht (hn z hz)
    have hmem := subgradient_add_normalCone_dom_subset (innerₗ E) (conj (innerₗ E) f) v
      (Set.add_mem_add hx hsmul)
    rw [mem_subgradient_conj_innerL_iff hf hcl,
      ← hasGradientAt_toDual_iff_mem_subgradient hf hp hcl hes] at hmem
    rw [hmem.gradient_toReal_eq, LinearIsometryEquiv.symm_apply_apply]
  -- Which contradicts boundedness of the sublevel set at height `‖v‖`.
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (hbd ‖v‖)
  have hx0 : ‖gradient (fun w => (f w).toReal) x‖ = ‖v‖ := by simpa using hline 0 le_rfl
  have hxR : ‖x‖ ≤ R := hR x hx0.le
  have hnpos : 0 < ‖n‖ := norm_pos_iff.2 hn0
  have hRnn : 0 ≤ R := le_trans (norm_nonneg x) hxR
  set t : ℝ := (R + ‖x‖ + 1) / ‖n‖ with ht
  have htpos : 0 ≤ t := div_nonneg (by linarith [norm_nonneg x]) hnpos.le
  have hle := hR (x + t • n) (le_of_eq (hline t htpos))
  have hnorm : ‖t • n‖ = R + ‖x‖ + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htpos, ht, div_mul_cancel₀ _ hnpos.ne']
  have hsub : ‖t • n‖ ≤ ‖x + t • n‖ + ‖x‖ := by
    simpa using norm_sub_le (x + t • n) x
  rw [hnorm] at hsub
  linarith

/-- **The hard half of Lemma 26.7, second step**: the range of `∇f` is closed.

A convergent sequence of gradients is bounded, so the points carrying them lie in one sublevel set,
which the hypothesis makes bounded; a convergent subsequence of those points has the limit gradient
as its gradient, by continuity of `∇f` (Theorem 25.5). -/
theorem isClosed_gradientRange_of_isBounded (hf : ConvexFn f) (hp : Proper f)
    (hdom : dom f = univ) (hdiff : ∀ z : E, DifferentiableAtFn f z)
    (hbd : ∀ b : ℝ, Bornology.IsBounded {x : E | ‖gradient (fun w => (f w).toReal) x‖ ≤ b}) :
    IsClosed (gradientRange f) := by
  have hes : EssentiallySmooth f := essentiallySmooth_of_dom_eq_univ hdom hdiff
  have hcont : Continuous (gradient fun w => (f w).toReal) := by
    rw [← continuousOn_univ, ← interior_univ, ← hdom]
    exact continuousOn_gradient_interior_dom hf hp hes
  refine IsSeqClosed.isClosed fun {vs v} hvs hlim => ?_
  choose xs hxs using hvs
  have hgrad : ∀ n, gradient (fun w => (f w).toReal) (xs n) = vs n := fun n => by
    rw [(hxs n).gradient_toReal_eq, LinearIsometryEquiv.symm_apply_apply]
  obtain ⟨b, hb⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto vs hlim)
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : E)).1 (hbd b)
  have hmem : ∀ n, xs n ∈ closedBall (0 : E) R := fun n =>
    hR (show ‖gradient (fun w => (f w).toReal) (xs n)‖ ≤ b by
      rw [hgrad n]; exact hb _ ⟨n, rfl⟩)
  obtain ⟨a, -, φ, hφ, hφlim⟩ := (isCompact_closedBall (0 : E) R).tendsto_subseq hmem
  have hva : gradient (fun w => (f w).toReal) a = v := by
    refine tendsto_nhds_unique ((hcont.tendsto a).comp hφlim) ?_
    exact (hlim.comp hφ.tendsto_atTop).congr fun n => (hgrad (φ n)).symm
  exact ⟨a, hva ▸ (hdiff a).hasGradientAt_gradient⟩

/-- **The hard half of Lemma 26.7**: bounded sublevel sets of `‖∇f‖` force `dom f* = E`.

`D = ∇f(E)` is non-empty, open (`gradientRange_subset_interior_dom_conj_of_isBounded` together with
`ri (dom f*) ⊆ D` from Corollary 26.4.1) and closed (`isClosed_gradientRange_of_isBounded`), and
`E` is connected. -/
theorem dom_conj_eq_univ_of_isBounded (hf : ConvexFn f) (hp : Proper f) (hdom : dom f = univ)
    (hdiff : ∀ z : E, DifferentiableAtFn f z)
    (hbd : ∀ b : ℝ, Bornology.IsBounded {x : E | ‖gradient (fun w => (f w).toReal) x‖ ≤ b}) :
    dom (conj (innerₗ E) f) = univ := by
  have hcl : ClosedFn f := closedFn_of_dom_eq_univ hf hp hdom
  have hes : EssentiallySmooth f := essentiallySmooth_of_dom_eq_univ hdom hdiff
  have hne : (gradientRange f).Nonempty := ⟨_, (hdiff 0).hasGradientAt_gradient.mem_gradientRange⟩
  have hsub := gradientRange_subset_interior_dom_conj_of_isBounded hf hp hdom hdiff hbd
  have heq : gradientRange f = interior (dom (conj (innerₗ E) f)) :=
    Subset.antisymm hsub
      ((Convex.interior_subset_relint (convexFn_conj _ f).convex_dom (hne.mono hsub)).trans
        (relint_dom_conj_subset_gradientRange hf hp hcl hes))
  have hclopen : IsClopen (gradientRange f) :=
    ⟨isClosed_gradientRange_of_isBounded hf hp hdom hdiff hbd, heq ▸ isOpen_interior⟩
  have huniv : interior (dom (conj (innerₗ E) f)) = univ := heq ▸ hclopen.eq_univ hne
  exact eq_univ_of_univ_subset (huniv.ge.trans interior_subset)

/-- **Rockafellar, Lemma 26.7**: a finite differentiable convex function is co-finite exactly when
the norm of its gradient tends to infinity along every sequence tending to infinity. -/
theorem cofinite_iff_forall_tendsto_norm_gradient_atTop (hf : ConvexFn f) (hp : Proper f)
    (hdom : dom f = univ) (hdiff : ∀ z : E, DifferentiableAtFn f z) :
    Cofinite f ↔ ∀ xs : ℕ → E, Tendsto (fun i => ‖xs i‖) atTop atTop →
      Tendsto (fun i => ‖gradient (fun w => (f w).toReal) (xs i)‖) atTop atTop := by
  have hcl : ClosedFn f := closedFn_of_dom_eq_univ hf hp hdom
  rw [cofinite_iff_dom_conj_eq_univ (B := innerₗ E) ⟨hf, hcl, hp⟩,
    forall_tendsto_norm_atTop_iff_isBounded]
  exact ⟨fun h => isBounded_setOf_norm_gradient_le_of_dom_conj_eq_univ hf hp hdom hdiff h,
    dom_conj_eq_univ_of_isBounded hf hp hdom hdiff⟩

end Lemma267

end Tdaf.ConvexAnalysis
