/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.Calculus.Rademacher
import Tdaf.Analysis.Convex.Subgradient.Convergence
import Tdaf.Analysis.Convex.Subgradient.Gradient

/-!
# Almost everywhere differentiability of a convex function

Rockafellar's **Theorem 25.5**: a proper convex function on a finite-dimensional space is
differentiable at almost every point of the interior of its effective domain, the points of
differentiability are dense there, and the gradient map is continuous where it is defined.

## Main results

* `HasGradientAt.hasFDerivAt_toReal`, `hasGradientAt_of_hasFDerivAt_toReal` — the dictionary
  between `∇f` for an `EReal`-valued `f` and Mathlib's `fderiv` of the **real trace**
  `fun z => (f z).toReal`, valid at interior points of `dom f`.
* `exists_lipschitzOnWith_ball` — Theorem 10.4 localized: a proper convex function is Lipschitz on
  a whole *ball* around any interior point of its effective domain.
* `ae_differentiableAtFn` — **Theorem 25.5**, the measure-zero clause, in `∀ᵐ` form.
* `measure_diff_differentiableAtFn` — the same clause as a null set.
* `interior_dom_subset_closure_differentiableAtFn` — **Theorem 25.5**, the density clause.
* `continuousOn_fderiv_toReal` — **Theorem 25.5**, the continuity clause: `∇f` is continuous on
  the set where it exists.
* `continuousOn_fderiv_of_convexOn` — **Corollary 25.5.1**, for Mathlib's `ConvexOn`.
* `measure_diff_twoSided_dirDeriv` — **Theorem 25.4**, the measure-zero clause, which is now a
  corollary of Theorem 25.5 rather than its source.
* `mem_subgradient_innerL_iff`, `subgradient_innerL_eq_singleton` — the Riesz bridge between the
  two pairings the library uses on an inner-product space, which is what lets Corollary 24.5.1
  (stated for `innerₗ E`) speak about gradients (which live in `StrongDual ℝ E`).

## Design notes

**Mathlib's Rademacher theorem does the analysis; convexity only has to supply local Lipschitz
constants.** `LipschitzOnWith.ae_differentiableWithinAt_of_mem` gives a.e. differentiability *on a
set* for a function Lipschitz on it, so the work is to cover `int (dom f)` by sets on which the
real trace is Lipschitz and which are open, so that `DifferentiableWithinAt` upgrades to
`DifferentiableAt`. Theorem 10.4 gives Lipschitz constants on *compact* subsets of `ri (dom f)`;
`exists_lipschitzOnWith_ball` shrinks a closed ball to an open one to get both properties at once,
and `TopologicalSpace.isOpen_iUnion_countable` extracts a countable subcover, which is what turns
countably many a.e. statements into one.

**The density clause needs no measure in its statement.** A non-empty open set has positive Haar
measure, so it cannot sit inside a null set; the argument only needs *some* Haar measure to exist,
and following Mathlib's `dense_differentiableAt_norm` the proof introduces the Borel structure and
`Basis.addHaar` locally. The statement is therefore measure-free.

**The continuity clause is Corollary 24.5.1 read through the Riesz isomorphism.** Upper
semicontinuity of `∂f` says `∂f z ⊆ ∂f x + εB` near `x`; where `f` is differentiable both
subdifferentials are singletons, and the inclusion becomes `‖∇f z - ∇f x‖ ≤ ε`. Corollary 24.5.1
is stated for the pairing `innerₗ E`, whose subgradients are *vectors*, while `HasGradientAt`
produces an element of `StrongDual ℝ E`; `mem_subgradient_innerL_iff` is the translation, and it is
an isometry, so the `ε` survives unchanged.

**Rockafellar's implication runs the other way.** He proves Theorem 25.4's measure-zero clause
first, by a Fubini argument over lines through the `Sₖ` decomposition, and gets Theorem 25.5 by
intersecting the `n` coordinate directions. With Rademacher available the order reverses:
Theorem 25.5 is proved directly and `measure_diff_twoSided_dirDeriv` reads it off, since
differentiability supplies the two-sided derivative in *every* direction at once. Neither the
`Sₖ` decomposition nor Fubini is needed.

## What is not here

Theorem 25.6 (a subgradient at a boundary point as a limit of gradients) and Theorem 25.7
(convergence of gradients under pointwise convergence).
-/

namespace Tdaf.ConvexAnalysis

open Filter MeasureTheory Metric Topology
open scoped NNReal

/-! ### Differentiability through the real trace -/

section RealTrace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal}
  {f' : StrongDual ℝ E} {x : E}

omit [NormedSpace ℝ E] in
/-- Near an interior point of its effective domain, a proper function is the coercion of its
**real trace** `fun z => (f z).toReal`. -/
theorem eventuallyEq_coe_toReal (hp : Proper f) (hx : x ∈ interior (dom f)) :
    f =ᶠ[𝓝 x] fun z => (((f z).toReal : ℝ) : EReal) := by
  filter_upwards [isOpen_interior.mem_nhds hx] with z hz
  exact (_root_.EReal.coe_toReal (mem_dom.1 (interior_subset hz)).ne (hp.ne_bot z)).symm

/-- A gradient of `f` is a Fréchet derivative of its real trace. -/
theorem HasGradientAt.hasFDerivAt_toReal (h : HasGradientAt f f' x) :
    HasFDerivAt (fun z => (f z).toReal) f' x := by
  obtain ⟨g, hfg, hd⟩ := h
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hfg] with z hz
  rw [hz, _root_.EReal.toReal_coe]

/-- Conversely, at an interior point of `dom f` a Fréchet derivative of the real trace is a
gradient of `f`. -/
theorem hasGradientAt_of_hasFDerivAt_toReal (hp : Proper f) (hx : x ∈ interior (dom f))
    (hd : HasFDerivAt (fun z => (f z).toReal) f' x) : HasGradientAt f f' x :=
  ⟨_, eventuallyEq_coe_toReal hp hx, hd⟩

theorem hasGradientAt_iff_hasFDerivAt_toReal (hp : Proper f) (hx : x ∈ interior (dom f)) :
    HasGradientAt f f' x ↔ HasFDerivAt (fun z => (f z).toReal) f' x :=
  ⟨HasGradientAt.hasFDerivAt_toReal, hasGradientAt_of_hasFDerivAt_toReal hp hx⟩

theorem differentiableAtFn_iff_differentiableAt_toReal (hp : Proper f)
    (hx : x ∈ interior (dom f)) :
    DifferentiableAtFn f x ↔ DifferentiableAt ℝ (fun z => (f z).toReal) x :=
  ⟨fun ⟨_, h⟩ => h.hasFDerivAt_toReal.differentiableAt,
    fun h => ⟨_, hasGradientAt_of_hasFDerivAt_toReal hp hx h.hasFDerivAt⟩⟩

/-- Mathlib's `fderiv` of the real trace **is** Rockafellar's `∇f`. -/
theorem HasGradientAt.fderiv_toReal_eq (h : HasGradientAt f f' x) :
    fderiv ℝ (fun z => (f z).toReal) x = f' :=
  h.hasFDerivAt_toReal.fderiv

/-- The gradient of `f` at a point of differentiability, named. -/
theorem DifferentiableAtFn.hasGradientAt_fderiv (h : DifferentiableAtFn f x) :
    HasGradientAt f (fderiv ℝ (fun z => (f z).toReal) x) x := by
  obtain ⟨f', hf'⟩ := h
  rw [hf'.fderiv_toReal_eq]
  exact hf'

end RealTrace

/-! ### Theorem 25.5: differentiability almost everywhere -/

section Rademacher

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- **Theorem 10.4, localized**: a proper convex function is Lipschitz on a whole ball around any
interior point of its effective domain. Balls are what Rademacher's theorem needs, because
differentiability *within* an open set is differentiability. -/
theorem exists_lipschitzOnWith_ball (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) :
    ∃ r > 0, ball x r ⊆ interior (dom f) ∧
      ∃ K : ℝ≥0, LipschitzOnWith K (fun z => (f z).toReal) (ball x r) := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith_of_isCompact hp (isCompact_closedBall x (r / 2))
    (((closedBall_subset_ball (by linarith)).trans hsub).trans interior_subset_intrinsicInterior)
  exact ⟨r / 2, by linarith, (ball_subset_ball (by linarith)).trans hsub,
    K, hK.mono ball_subset_closedBall⟩

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Rockafellar, Theorem 25.5**, the measure-zero clause: a proper convex function is
differentiable at almost every point of the interior of its effective domain. -/
theorem ae_differentiableAtFn (hf : ConvexFn f) (hp : Proper f) :
    ∀ᵐ z ∂μ, z ∈ interior (dom f) → DifferentiableAtFn f z := by
  choose! r hr hball K hK using fun z (hz : z ∈ interior (dom f)) =>
    exists_lipschitzOnWith_ball hf hp hz
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun p : interior (dom f) => ball (p : E) (r p)) fun _ => isOpen_ball
  have hcover : ∀ z ∈ interior (dom f), ∃ p ∈ T, z ∈ ball ((p : E)) (r p) := by
    intro z hz
    have hmem : z ∈ ⋃ p : interior (dom f), ball ((p : E)) (r p) :=
      Set.mem_iUnion.2 ⟨⟨z, hz⟩, mem_ball_self (hr z hz)⟩
    rw [← hTeq] at hmem
    simpa using hmem
  have hae : ∀ᵐ z ∂μ, ∀ p ∈ T, z ∈ ball ((p : E)) (r p) →
      DifferentiableWithinAt ℝ (fun w => (f w).toReal) (ball ((p : E)) (r p)) z :=
    (ae_ball_iff hTc).2 fun p _ => (hK (p : E) p.2).ae_differentiableWithinAt_of_mem
  filter_upwards [hae] with z hz hzU
  obtain ⟨p, hpT, hzp⟩ := hcover z hzU
  exact (differentiableAtFn_iff_differentiableAt_toReal hp hzU).2
    ((hz p hpT hzp).differentiableAt (isOpen_ball.mem_nhds hzp))

/-- **Theorem 25.5**, the measure-zero clause as a null set. -/
theorem measure_diff_differentiableAtFn (hf : ConvexFn f) (hp : Proper f) :
    μ (interior (dom f) \ {z | DifferentiableAtFn f z}) = 0 := by
  have hae := ae_differentiableAtFn (μ := μ) hf hp
  rw [ae_iff] at hae
  refine measure_mono_null (fun z hz => ?_) hae
  change ¬(z ∈ interior (dom f) → DifferentiableAtFn f z)
  exact fun hcon => hz.2 (hcon hz.1)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Where `f` is differentiable, every two-sided directional derivative exists.** Both sides are
values of the gradient (Theorem 25.2, necessity). -/
theorem twoSided_dirDeriv_of_differentiableAtFn (hf : ConvexFn f)
    (h : DifferentiableAtFn f x) (y : E) : dirDeriv f x y = -dirDeriv f x (-y) := by
  obtain ⟨f', hf'⟩ := h
  rw [hf'.dirDeriv_eq hf, hf'.dirDeriv_eq hf, map_neg, _root_.EReal.coe_neg, neg_neg]

/-- **Rockafellar, Theorem 25.4**, the measure-zero clause: in any fixed direction `y`, the
two-sided directional derivative exists almost everywhere on `int (dom f)`.

Rockafellar proves this first, by a Fubini argument over lines, and deduces Theorem 25.5 from it
by intersecting the `n` coordinate directions. Here Rademacher's theorem gives Theorem 25.5
directly, and this clause is the trivial consequence: differentiability at `z` supplies the
two-sided derivative in *every* direction. -/
theorem measure_diff_twoSided_dirDeriv (hf : ConvexFn f) (hp : Proper f) (y : E) :
    μ (interior (dom f) \ {z | dirDeriv f z y = -dirDeriv f z (-y)}) = 0 := by
  refine measure_mono_null (fun z hz => ?_) (measure_diff_differentiableAtFn (μ := μ) hf hp)
  obtain ⟨hzU, hzy⟩ := hz
  exact Set.mem_sdiff_of_mem hzU fun hzd =>
    hzy (twoSided_dirDeriv_of_differentiableAtFn hf hzd y)

end Rademacher

section Dense

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- **Rockafellar, Theorem 25.5**, the density clause: the points of differentiability are dense in
the interior of the effective domain.

No measure appears in the statement; the proof borrows one, exactly as Mathlib's
`dense_differentiableAt_norm` does. -/
theorem interior_dom_subset_closure_differentiableAtFn (hf : ConvexFn f) (hp : Proper f) :
    interior (dom f) ⊆ closure {z | DifferentiableAtFn f z} := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let w := Module.Basis.ofVectorSpace ℝ E
  intro x hx
  refine mem_closure_iff.2 fun V hV hxV => ?_
  by_contra hne
  have hsub : V ∩ interior (dom f) ⊆ interior (dom f) \ {z | DifferentiableAtFn f z} := by
    rintro z ⟨hzV, hzU⟩
    exact ⟨hzU, fun hzD => hne ⟨z, hzV, hzD⟩⟩
  have hpos : 0 < w.addHaar (V ∩ interior (dom f)) :=
    (hV.inter isOpen_interior).measure_pos _ ⟨x, hxV, hx⟩
  exact hpos.ne' (measure_mono_null hsub (measure_diff_differentiableAtFn hf hp))

end Dense

/-! ### Theorem 25.5: continuity of the gradient -/

section GradientContinuity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E} {f' : StrongDual ℝ E}

/-- **The Riesz bridge between the two pairings of an inner-product space with itself and with its
dual**: `v` is a subgradient for `innerₗ E` exactly when the functional `⟪v, ·⟫` is one for the
canonical pairing with the dual. -/
theorem mem_subgradient_innerL_iff {v : E} :
    v ∈ subgradient (innerₗ E) f x ↔
      InnerProductSpace.toDual ℝ E v ∈ subgradient (topDualPairing ℝ E).flip f x := by
  have key : ∀ z : E, (innerₗ E) (z - x) v
      = (topDualPairing ℝ E).flip (z - x) (InnerProductSpace.toDual ℝ E v) := fun z => by
    simp [innerₗ_apply_apply, real_inner_comm]
  simp only [mem_subgradient]
  exact forall_congr' fun z => by rw [key z]

/-- **Theorem 25.1 in vector form**: at a point of differentiability the subdifferential for the
inner-product pairing is the single vector representing the gradient. -/
theorem subgradient_innerL_eq_singleton (hf : ConvexFn f) (h : HasGradientAt f f' x) :
    subgradient (innerₗ E) f x = {(InnerProductSpace.toDual ℝ E).symm f'} := by
  ext v
  rw [mem_subgradient_innerL_iff, h.subgradient_eq hf, Set.mem_singleton_iff,
    Set.mem_singleton_iff]
  exact ⟨fun hv => by rw [← hv, LinearIsometryEquiv.symm_apply_apply],
    fun hv => by rw [hv, LinearIsometryEquiv.apply_symm_apply]⟩

/-- **Rockafellar, Theorem 25.5**, the continuity clause: the gradient mapping is continuous on the
set where the function is differentiable.

This is Corollary 24.5.1 — upper semicontinuity of `∂f` — with both subdifferentials collapsed to
singletons by Theorem 25.1. -/
theorem continuousOn_fderiv_toReal (hf : ConvexFn f) (hp : Proper f) :
    ContinuousOn (fderiv ℝ fun w => (f w).toReal) {z | DifferentiableAtFn f z} := by
  set g := fderiv ℝ fun w => (f w).toReal with hgdef
  have hgrad : ∀ z ∈ {z | DifferentiableAtFn f z}, HasGradientAt f (g z) z := fun _ hz =>
    DifferentiableAtFn.hasGradientAt_fderiv hz
  intro x hx
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hev := eventually_nhds_subgradient_subset_add_closedBall hf hp
    (hgrad x hx).mem_interior_dom (half_pos hε)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z hzsub hzD
  have hzz : (InnerProductSpace.toDual ℝ E).symm (g z) ∈ subgradient (innerₗ E) f z := by
    rw [subgradient_innerL_eq_singleton hf (hgrad z hzD)]
    rfl
  have hmem := hzsub hzz
  rw [subgradient_innerL_eq_singleton hf (hgrad x hx)] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  rw [Set.mem_singleton_iff] at ha
  subst ha
  rw [mem_closedBall_zero_iff] at hb
  have hnorm : ‖(InnerProductSpace.toDual ℝ E).symm (g z)
      - (InnerProductSpace.toDual ℝ E).symm (g x)‖ ≤ ε / 2 := by
    rw [← hab, add_sub_cancel_left]
    exact hb
  calc dist (g z) (g x)
      = ‖(InnerProductSpace.toDual ℝ E).symm (g z)
        - (InnerProductSpace.toDual ℝ E).symm (g x)‖ := by
        rw [dist_eq_norm, ← (InnerProductSpace.toDual ℝ E).symm.norm_map (g z - g x), map_sub]
    _ ≤ ε / 2 := hnorm
    _ < ε := half_lt_self hε

/-- **Rockafellar, Corollary 25.5.1**: a finite convex function differentiable on an open convex
set is *continuously* differentiable there.

Mathlib's `ConvexOn` enters through `convexOn_iff_convexFn`, which extends `g` by `⊤` off `C`; on
the open set `C` the extension has the same gradients, so Theorem 25.5's continuity clause applies
verbatim. -/
theorem continuousOn_fderiv_of_convexOn {C : Set E} {g : E → ℝ} (hC : IsOpen C)
    (hne : C.Nonempty) (hg : ConvexOn ℝ C g) (hd : DifferentiableOn ℝ g C) :
    ContinuousOn (fderiv ℝ g) C := by
  set f : E → EReal := restrict C fun z => ((g z : ℝ) : EReal) with hfdef
  have hcf : ConvexFn f := (convexOn_iff_convexFn C g).1 hg
  have hdom : dom f = C := by
    ext z
    by_cases hz : z ∈ C <;> simp [hfdef, hz]
  have hp : Proper f := ⟨by rw [hdom]; exact hne, fun z => by
    by_cases hz : z ∈ C <;> simp [hfdef, hz]⟩
  have hint : interior (dom f) = C := by rw [hdom, hC.interior_eq]
  have hgrad : ∀ z ∈ C, HasGradientAt f (fderiv ℝ g z) z := fun z hz => by
    refine ⟨g, ?_, ((hd z hz).differentiableAt (hC.mem_nhds hz)).hasFDerivAt⟩
    filter_upwards [hC.mem_nhds hz] with w hw
    simp [hfdef, hw]
  have hsub : C ⊆ {z | DifferentiableAtFn f z} := fun z hz => ⟨_, hgrad z hz⟩
  exact ((continuousOn_fderiv_toReal hcf hp).mono hsub).congr fun z hz =>
    (HasGradientAt.fderiv_toReal_eq (hgrad z hz)).symm

end GradientContinuity

end Tdaf.ConvexAnalysis
