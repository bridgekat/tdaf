/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Subgradient.Reconstruction

/-!
# Essential smoothness

Rockafellar's **Theorem 26.1**: for a closed proper convex function, the subdifferential is
single-valued exactly when the function is *essentially smooth* — differentiable on the interior
of its effective domain, whose interior is non-empty, with the gradient blowing up at every
boundary point. In that case the subdifferential *is* the gradient on the interior and is empty
everywhere else.

The theorem is what makes §26's Legendre transformation work: it is the statement that for an
essentially smooth function the multivalued object `∂f` carries exactly the information of the
classical gradient mapping.

## Main definitions

* `EssentiallySmooth f` — Rockafellar's three conditions (a), (b), (c), with the gradient written
  as `fderiv ℝ (fun z => (f z).toReal)`.

## Main results

* `subgradient_eq_singleton_of_essentiallySmooth`, `subgradient_eq_empty_of_essentiallySmooth` —
  the "in this case" clause of Theorem 26.1.
* `subsingleton_subgradient_of_essentiallySmooth`,
  `essentiallySmooth_of_subsingleton_subgradient` — the two halves of **Theorem 26.1**.
* `subsingleton_subgradient_iff_essentiallySmooth` — **Theorem 26.1**.

## Design notes

**Condition (c) is stated at every point outside the interior, not at boundary points.**
Rockafellar quantifies over sequences in `C = int (dom f)` converging to a *boundary point* of
`C`. A sequence in `C` converging to a point not in `C` converges to a boundary point of `C`
automatically, since `C` is open, so the two readings agree and dropping the word "boundary"
removes a hypothesis that would otherwise have to be re-derived at every use — including inside
Theorem 26.1's own proof, where the point is known only to lie outside `int (dom f)`.

**The two halves use different parts of §25.** The forward half — single-valued implies
essentially smooth — needs only Theorem 24.4 (the graph of `∂f` is closed) beside Theorem 25.1:
a bounded subsequence of gradients has a convergent sub-subsequence whose limit is a subgradient
at the limit point, and a subgradient there would make `f` differentiable there, hence put the
point in the interior. It is the *converse* half that needs Theorem 25.6, and it needs it in the
weak form "`∂f x ≠ ∅` implies `S(x) ≠ ∅`" rather than as the full reconstruction formula.

**Gradients are compared through their Riesz representatives.** `∂f x` for the pairing `innerₗ E`
is a set of vectors, while `fderiv` produces an element of `StrongDual ℝ E`; extracting a
convergent subsequence is done in `E`, where `FiniteDimensional` gives compactness of closed balls
directly, and `InnerProductSpace.toDual` is an isometry so no constant is lost.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §26 (Theorem 26.1).
-/

namespace Tdaf.ConvexAnalysis

open Filter Metric Topology

section EssentiallySmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- **Rockafellar's essential smoothness.** A proper convex function is essentially smooth when,
writing `C = int (dom f)`:

* (a) `C` is non-empty;
* (b) `f` is differentiable throughout `C`;
* (c) `‖∇f xᵢ‖ → ∞` for every sequence in `C` converging to a point outside `C`.

A finite differentiable convex function on the whole space is essentially smooth, condition (c)
holding vacuously. -/
structure EssentiallySmooth (f : E → EReal) : Prop where
  /-- (a) The effective domain has non-empty interior. -/
  interior_dom_nonempty : (interior (dom f)).Nonempty
  /-- (b) `f` is differentiable at every interior point of its effective domain. -/
  differentiableAtFn : ∀ ⦃z : E⦄, z ∈ interior (dom f) → DifferentiableAtFn f z
  /-- (c) The gradient blows up along every approach to a point outside the interior. -/
  tendsto_norm_fderiv : ∀ ⦃z : E⦄, z ∉ interior (dom f) → ∀ zs : ℕ → E,
    (∀ i, zs i ∈ interior (dom f)) → Tendsto zs atTop (𝓝 z) →
      Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop

/-- On the interior of the effective domain, an essentially smooth function has exactly one
subgradient, namely its gradient. -/
theorem subgradient_eq_singleton_of_essentiallySmooth (hf : ConvexFn f) (hes : EssentiallySmooth f)
    (hx : x ∈ interior (dom f)) :
    subgradient (innerₗ E) f x
      = {(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun w => (f w).toReal) x)} :=
  subgradient_innerL_eq_singleton hf
    (DifferentiableAtFn.hasGradientAt_fderiv (hes.differentiableAtFn hx))

/-- **The substantive half of Theorem 26.1's "in this case" clause**: off the interior of the
effective domain an essentially smooth closed proper convex function has *no* subgradient.

By Theorem 25.6 a subgradient at `x` forces `S(x)` to be non-empty, so some sequence of gradients
converges — which condition (c) forbids. -/
theorem subgradient_eq_empty_of_essentiallySmooth (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) (hes : EssentiallySmooth f) (hx : x ∉ interior (dom f)) :
    subgradient (innerₗ E) f x = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨v, hv⟩
  -- Theorem 25.6 turns a subgradient into a limit of gradients.
  rw [subgradient_eq_closure_convexHull_gradientLimits_add_normalCone hf hp hcl
    hes.interior_dom_nonempty] at hv
  obtain ⟨a, ha, _, _, _⟩ := hv
  have hSne : (gradientLimits f x).Nonempty := by
    rcases (gradientLimits f x).eq_empty_or_nonempty with hempty | hne
    · rw [hempty, convexHull_empty, closure_empty] at ha
      exact absurd ha (Set.notMem_empty a)
    · exact hne
  obtain ⟨w, xs, vs, hxs, hgrad, hvs⟩ := hSne
  -- The gradients are eventually bounded, contradicting (c).
  have hint : ∀ i, xs i ∈ interior (dom f) := fun i => (hgrad i).mem_interior_dom
  have hfd : ∀ i, fderiv ℝ (fun z => (f z).toReal) (xs i) = InnerProductSpace.toDual ℝ E (vs i) :=
    fun i => (hgrad i).fderiv_toReal_eq
  have hnorm : ∀ i, ‖fderiv ℝ (fun z => (f z).toReal) (xs i)‖ = ‖vs i‖ := fun i => by
    rw [hfd i, LinearIsometryEquiv.norm_map]
  have htop := hes.tendsto_norm_fderiv hx xs hint hxs
  rw [tendsto_congr hnorm] at htop
  exact not_tendsto_atTop_of_tendsto_nhds (hvs.norm) htop

/-- **Rockafellar, Theorem 26.1**, the easy half: an essentially smooth closed proper convex
function has a single-valued subdifferential. -/
theorem subsingleton_subgradient_of_essentiallySmooth (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) (hes : EssentiallySmooth f) (x : E) :
    (subgradient (innerₗ E) f x).Subsingleton := by
  by_cases hx : x ∈ interior (dom f)
  · rw [subgradient_eq_singleton_of_essentiallySmooth hf hes hx]
    exact Set.subsingleton_singleton
  · rw [subgradient_eq_empty_of_essentiallySmooth hf hp hcl hes hx]
    exact Set.subsingleton_empty

/-- **A single-valued subdifferential is a gradient on the relative interior.** With Theorem 23.4
supplying a subgradient at every point of `ri (dom f)`, single-valuedness makes the subdifferential
there a singleton, and Theorem 25.1's converse turns that into differentiability — which in turn
places the point in the *interior* of `dom f`. -/
theorem differentiableAtFn_of_subsingleton_subgradient (hf : ConvexFn f) (hp : Proper f)
    (h : ∀ z : E, (subgradient (innerₗ E) f z).Subsingleton) (hx : x ∈ ri (dom f)) :
    DifferentiableAtFn f x := by
  obtain ⟨v, hv⟩ := subgradient_nonempty_of_mem_relint_dom (B := innerₗ E) hf hp hx
  exact ⟨_, hasGradientAt_toDual_of_subgradient_eq_singleton hf hp
    (Set.eq_singleton_iff_unique_mem.2 ⟨hv, fun z hz => h x hz hv⟩)⟩

/-- **Rockafellar, Theorem 26.1**, the substantive half: a closed proper convex function with a
single-valued subdifferential is essentially smooth.

Conditions (a) and (b) come from Theorem 23.4 and Theorem 25.1: a subgradient exists on
`ri (dom f)`, single-valuedness makes it a gradient, and a gradient exists only at interior points,
so `ri (dom f) ⊆ int (dom f)` and the two coincide. Condition (c) is Theorem 24.4: a bounded
subsequence of gradients has a convergent sub-subsequence, whose limit is a subgradient at the
limit point, which would place that point in the interior. -/
theorem essentiallySmooth_of_subsingleton_subgradient (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) (h : ∀ z : E, (subgradient (innerₗ E) f z).Subsingleton) :
    EssentiallySmooth f := by
  have hri : ∀ ⦃z : E⦄, z ∈ ri (dom f) → z ∈ interior (dom f) := fun z hz =>
    (differentiableAtFn_of_subsingleton_subgradient hf hp h hz).choose_spec.mem_interior_dom
  have hne : (interior (dom f)).Nonempty := by
    obtain ⟨z, hz⟩ := Convex.relint_nonempty hf.convex_dom hp.dom_nonempty
    exact ⟨z, hri hz⟩
  refine ⟨hne, fun z hz => differentiableAtFn_of_subsingleton_subgradient hf hp h
    (Convex.interior_subset_relint hf.convex_dom hne hz), ?_⟩
  intro z hz zs hzs hlim
  by_contra hcon
  -- A bounded subsequence of gradients.
  obtain ⟨b, hb⟩ := not_forall.1 (tendsto_atTop.not.1 hcon)
  obtain ⟨φ, hφ, hφb⟩ := Filter.extraction_of_frequently_atTop (Filter.not_eventually.1 hb)
  set vs : ℕ → E := fun i => (InnerProductSpace.toDual ℝ E).symm
    (fderiv ℝ (fun w => (f w).toReal) (zs i)) with hvsdef
  have hgrad : ∀ i, HasGradientAt f (InnerProductSpace.toDual ℝ E (vs i)) (zs i) := fun i => by
    rw [hvsdef, LinearIsometryEquiv.apply_symm_apply]
    exact DifferentiableAtFn.hasGradientAt_fderiv
      (differentiableAtFn_of_subsingleton_subgradient hf hp h
        (Convex.interior_subset_relint hf.convex_dom hne (hzs i)))
  have hvsb : ∀ n, vs (φ n) ∈ closedBall (0 : E) b := fun n => by
    rw [mem_closedBall_zero_iff, hvsdef, LinearIsometryEquiv.norm_map]
    exact (not_le.1 (hφb n)).le
  -- Its limit is a subgradient at `z`, so `f` is differentiable at `z` and `z` is interior.
  obtain ⟨w, _, ψ, hψ, hψlim⟩ := (isCompact_closedBall (0 : E) b).tendsto_subseq hvsb
  have hmem : w ∈ gradientLimits f z :=
    ⟨fun n => zs (φ (ψ n)), fun n => vs (φ (ψ n)), hlim.comp (hφ.comp hψ).tendsto_atTop,
      fun n => hgrad (φ (ψ n)), hψlim⟩
  have hsub : w ∈ subgradient (innerₗ E) f z :=
    gradientLimits_subset_subgradient hf hp hcl hmem
  exact hz (hasGradientAt_toDual_of_subgradient_eq_singleton hf hp
    (Set.eq_singleton_iff_unique_mem.2 ⟨hsub, fun u hu => h z hu hsub⟩)).mem_interior_dom

/-- **Rockafellar, Theorem 26.1**: for a closed proper convex function, single-valuedness of the
subdifferential and essential smoothness are the same thing. -/
theorem subsingleton_subgradient_iff_essentiallySmooth (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) :
    (∀ z : E, (subgradient (innerₗ E) f z).Subsingleton) ↔ EssentiallySmooth f :=
  ⟨essentiallySmooth_of_subsingleton_subgradient hf hp hcl,
    subsingleton_subgradient_of_essentiallySmooth hf hp hcl⟩

end EssentiallySmooth

end Tdaf.ConvexAnalysis
