/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Continuity
import Tdaf.Analysis.Convex.Subgradient.Monotone

/-!
# Local boundedness of the subdifferential

A proper convex function is Lipschitz on every compact subset of the interior of its effective
domain, and *the same constant* bounds its subgradients there. For a compact `S ⊆ int (dom f)`
there is a `K ≥ 0` with

* `f` Lipschitz on `S` with constant `K`;
* `⟨z, y⟩ ≤ K ‖z‖` for every `x ∈ S`, every `y ∈ ∂f x` and every direction `z`;
* `f'(x; z) ≤ K ‖z‖` for every `x ∈ S`.

When `f` is in addition closed, the image

```
∂f(S) = ⋃ {∂f x | x ∈ S}
```

is nonempty and compact.

## Main results

* `exists_lipschitz_forall_pairing_le_of_isCompact` — the three bounds above, with one constant,
  over an arbitrary pairing.
* `image_subgradientRel_nonempty` — `∂f(S) ≠ ∅`.
* `isCompact_image_subgradientRel` — `∂f(S)` is compact, hence closed and bounded. Stated for a
  real inner-product space paired with itself, which is where the norm `‖y‖` of a subgradient has
  a meaning.

## Design notes

**One constant does all three jobs.** The classical statement takes `α = sup {‖y‖ | y ∈ ∂f(S)}`
and then *proves* the two inequalities for it. Here the Lipschitz constant supplied by
`ConvexFn.exists_lipschitzOnWith_of_isCompact` on a compact collar of `S` is produced first and the
three statements are read off it. That is slightly stronger (`α ≤ K`) and it avoids the
support-function calculus, which is what the classical route to boundedness uses.

**Closedness of `f` is needed only for the topological half.** The quantitative half uses convexity
and properness alone; `IsClosed (∂f(S))` goes through `isClosed_subgradientRel`, which is where
lower semicontinuity enters.

**The bound on subgradients is stated through the pairing.** `⟨z, y⟩ ≤ K ‖z‖` for all `z` is the
pairing-side formulation of `‖y‖ ≤ K` and needs no norm on `F`; it is the same idiom as
`bddAbove_subgradient_iff_mem_interior_dom` in `Subgradient/Existence.lean`. When `F = E` is an
inner-product space, `real_inner_self_eq_norm_mul_norm` turns it into `‖y‖ ≤ K`.

## What is not here

**The differential convergence theorems.** `limsup_i f_i'(x_i; y_i) ≤ f'(x; y)` for a pointwise
convergent sequence of convex functions needs the equi-Lipschitz theory of `Convergence.lean`
transported across the `ConvexFn`/`ConvexOn` boundary (that file is stated for families
`ι → E → ℝ`, `dirDeriv` for `E → EReal`); the companion statement
`∂f_i (x_i) ⊆ ∂f x + εB` needs `δ*(· | C₁) ≤ δ*(· | C₂) ↔ cl conv C₁ ⊆ cl conv C₂` together with
`δ*(· | C + εB) = δ*(· | C) + ε‖·‖`. The refinement in which `x_i` approaches `x` from a single
direction needs in addition the second-order directional derivative `f'(x; y; ·)`, local
simpliciality of a polytope, and continuity of a convex function relative to a locally simplicial
set.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §24 (Theorem 24.7).
  Theorems 24.5 and 24.6 are the convergence statements listed above.
-/

open Set Filter Topology
open scoped NNReal RealInnerProductSpace

namespace Tdaf.ConvexAnalysis

/-! ### The relative interior of a set with interior points -/

section Relint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {C : Set E}

/-- A convex set with an interior point has `ri C = interior C`; in particular
`interior C ⊆ ri C`, which is how Theorem 23.4 becomes applicable at interior points. -/
theorem Convex.interior_subset_relint (hC : Convex ℝ C) (hne : (interior C).Nonempty) :
    interior C ⊆ ri C :=
  le_of_eq (intrinsicInterior_eq_interior
    ((Convex.interior_nonempty_iff_affineSpan_eq_top hC).1 hne)).symm

end Relint

/-! ### Theorem 24.7, the quantitative half -/

section Bound

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- Moving a point of `S` a distance `δ` in any direction keeps it inside the collar
`cthickening δ S`. -/
theorem mem_cthickening_add_smul {S : Set E} {x : E} (hx : x ∈ S) {δ : ℝ} (hδ : 0 < δ) {z : E}
    (hz : z ≠ 0) : x + (δ / ‖z‖) • z ∈ Metric.cthickening δ S := by
  have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz
  refine Metric.mem_cthickening_of_dist_le _ _ _ _ hx (le_of_eq ?_)
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hδ hznorm)]
  field_simp

/-- **Rockafellar, Theorem 24.7**, quantitative half. On a compact `S ⊆ int (dom f)` a single
constant `K` is simultaneously a Lipschitz constant for `f`, a bound `⟨z, y⟩ ≤ K ‖z‖` for every
subgradient at every point of `S`, and a bound `f'(x; z) ≤ K ‖z‖` for the directional derivatives.

The proof reverses Rockafellar's order. Theorem 10.4 gives a Lipschitz constant on a compact collar
`cthickening δ S ⊆ int (dom f)`; the subgradient inequality and the difference quotient, both
evaluated at `x + (δ / ‖z‖) • z`, which stays in the collar, are then bounded at one stroke. -/
theorem exists_lipschitz_forall_pairing_le_of_isCompact (hf : ConvexFn f) (hp : Proper f)
    {S : Set E} (hS : IsCompact S) (hSD : S ⊆ interior (dom f)) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun x => (f x).toReal) S ∧
      (∀ x ∈ S, ∀ y ∈ subgradient B f x, ∀ z : E, B z y ≤ (K : ℝ) * ‖z‖) ∧
      ∀ x ∈ S, ∀ z : E, dirDeriv f x z ≤ (((K : ℝ) * ‖z‖ : ℝ) : EReal) := by
  obtain ⟨δ, hδ, hδsub⟩ := hS.exists_cthickening_subset_open isOpen_interior hSD
  have hTc : IsCompact (Metric.cthickening δ S) := hS.cthickening
  have hTdom : Metric.cthickening δ S ⊆ dom f := hδsub.trans interior_subset
  have hTri : Metric.cthickening δ S ⊆ ri (dom f) := fun w hw =>
    Convex.interior_subset_relint hf.convex_dom ⟨w, hδsub hw⟩ (hδsub hw)
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith_of_isCompact hp hTc hTri
  -- The single estimate both halves consume.
  have hkey : ∀ x ∈ S, ∀ z : E, z ≠ 0 → ∀ a b : ℝ, f x = (a : EReal) →
      f (x + (δ / ‖z‖) • z) = (b : EReal) → b - a ≤ (K : ℝ) * ((δ / ‖z‖) * ‖z‖) := by
    intro x hx z hz a b ha hb
    have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hxT : x ∈ Metric.cthickening δ S := Metric.self_subset_cthickening S hx
    have hwT := mem_cthickening_add_smul hx hδ hz
    have hnorm : dist (x + (δ / ‖z‖) • z) x = (δ / ‖z‖) * ‖z‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hδ hznorm)]
    have hlip := hK.dist_le_mul _ hwT _ hxT
    simp only [ha, hb, _root_.EReal.toReal_coe, Real.dist_eq, hnorm] at hlip
    exact (le_abs_self _).trans hlip
  refine ⟨K, hK.mono (Metric.self_subset_cthickening S), ?_, ?_⟩
  · intro x hx y hy z
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz
    have ht : (0 : ℝ) < δ / ‖z‖ := div_pos hδ hznorm
    obtain ⟨a, ha⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x)
      (hTdom (Metric.self_subset_cthickening S hx))
    obtain ⟨b, hb⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot _)
      (hTdom (mem_cthickening_add_smul hx hδ hz))
    have hsg := hy (x + (δ / ‖z‖) • z)
    rw [add_sub_cancel_left, map_smul, LinearMap.smul_apply, smul_eq_mul, ha, hb,
      ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at hsg
    refine le_of_mul_le_mul_left ?_ ht
    calc (δ / ‖z‖) * B z y
        ≤ b - a := by linarith
      _ ≤ (K : ℝ) * ((δ / ‖z‖) * ‖z‖) := hkey x hx z hz a b ha hb
      _ = (δ / ‖z‖) * ((K : ℝ) * ‖z‖) := by ring
  · intro x hx z
    have hxT : x ∈ Metric.cthickening δ S := Metric.self_subset_cthickening S hx
    obtain ⟨a, ha⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) (hTdom hxT)
    rcases eq_or_ne z 0 with rfl | hz
    · rw [dirDeriv_zero (by rw [ha]; exact _root_.EReal.coe_ne_top a) (hp.ne_bot x)]
      simp
    have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz
    have ht : (0 : ℝ) < δ / ‖z‖ := div_pos hδ hznorm
    obtain ⟨b, hb⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot _)
      (hTdom (mem_cthickening_add_smul hx hδ hz))
    refine le_trans (dirDeriv_le f x z ht) ?_
    rw [ha, hb, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div, _root_.EReal.coe_le_coe_iff,
      div_le_iff₀ ht]
    calc b - a ≤ (K : ℝ) * ((δ / ‖z‖) * ‖z‖) := hkey x hx z hz a b ha hb
      _ = (K : ℝ) * ‖z‖ * (δ / ‖z‖) := by ring

end Bound

/-! ### Theorem 24.7, the topological half -/

section Image

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- **Rockafellar, Theorem 24.7**, nonemptiness: `∂f(S) ≠ ∅` for a nonempty
`S ⊆ int (dom f)`. This is Theorem 23.4 applied at any point of `S`. -/
theorem image_subgradientRel_nonempty (hf : ConvexFn f) (hp : Proper f) {S : Set E}
    (hne : S.Nonempty) (hSD : S ⊆ interior (dom f)) :
    ((subgradientRel (innerₗ E) f).image S).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ := subgradient_nonempty_of_mem_relint_dom (B := innerₗ E) hf hp
    (Convex.interior_subset_relint hf.convex_dom ⟨x, hSD hx⟩ (hSD hx))
  exact ⟨y, x, hx, hy⟩

/-- **Rockafellar, Theorem 24.7**, topological half: `∂f(S)` is compact — in particular closed and
bounded — for a closed proper convex `f` and a compact `S ⊆ int (dom f)`.

Boundedness is `exists_lipschitz_forall_pairing_le_of_isCompact` read at `z = y`, where
`⟪y, y⟫ = ‖y‖²` turns the pairing bound into `‖y‖ ≤ K`. Closedness is Theorem 24.4: the graph of
`∂f` meets the compact box `S ×ˢ closedBall 0 K` in a compact set, and `∂f(S)` is its projection. -/
theorem isCompact_image_subgradientRel (hf : ClosedProperConvexFn f) {S : Set E}
    (hS : IsCompact S) (hSD : S ⊆ interior (dom f)) :
    IsCompact ((subgradientRel (innerₗ E) f).image S) := by
  obtain ⟨K, -, hpair, -⟩ :=
    exists_lipschitz_forall_pairing_le_of_isCompact (B := innerₗ E) hf.convex hf.proper hS hSD
  have hnorm : ∀ x ∈ S, ∀ y ∈ subgradient (innerₗ E) f x, ‖y‖ ≤ (K : ℝ) := by
    intro x hx y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    have h := hpair x hx y hy y
    rw [innerₗ_apply_apply, real_inner_self_eq_norm_mul_norm] at h
    exact le_of_mul_le_mul_right (by linarith) (norm_pos_iff.2 hy0)
  have hbox : IsCompact (S ×ˢ Metric.closedBall (0 : E) (K : ℝ)) :=
    IsCompact.prod hS (isCompact_closedBall 0 (K : ℝ))
  have hclosed : IsClosed (subgradientRel (innerₗ E) f) := by
    refine isClosed_subgradientRel ?_ hf.proper hf.lowerSemicontinuous
    exact continuous_inner
  have hcap : IsCompact (subgradientRel (innerₗ E) f ∩ S ×ˢ Metric.closedBall (0 : E) (K : ℝ)) :=
    hbox.inter_left hclosed
  have himg : (subgradientRel (innerₗ E) f).image S
      = Prod.snd '' (subgradientRel (innerₗ E) f ∩ S ×ˢ Metric.closedBall (0 : E) (K : ℝ)) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(x, y), ⟨hxy, hx, by simpa using hnorm x hx y hxy⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hpS, -⟩, rfl⟩
      exact ⟨p.1, hpS, hp⟩
  rw [himg]
  exact hcap.image continuous_snd

end Image

end Tdaf.ConvexAnalysis
