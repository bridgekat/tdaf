/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.Convex.Continuous
import Tdaf.Analysis.Convex.RelativeInterior

/-!
# Continuity of a convex function on the relative interior of its domain

Rockafellar's **Theorem 10.1**: a proper convex function on a finite-dimensional space is
continuous, relative to the affine hull of its effective domain, at every relative interior point
of that domain.

Mathlib proves the *interior* statement (`ConvexOn.continuousOn_interior`) and leaves the relative
version as a `proof_wanted` in `Mathlib/Analysis/Convex/Continuous.lean`, because
`intrinsicInterior` lives in `Mathlib/Analysis/Convex/Intrinsic.lean` and the two files do not meet.
This file supplies it.

## Main results

* `relint_eq_vadd_image_interior` — the *chart*: `ri C = x₀ + ι (int D)`, where `D` is the trace of
  `C` on a subspace `V` spanned by `C - x₀`. This is the reduction "relative interior = interior in
  the affine hull", carried out in a linear chart rather than in the affine hull itself, so that
  `Convex` and `ConvexOn` — which need a module, not a torsor — still apply.
* `ConvexFn.continuousOn_toReal_relint_dom`, `ConvexFn.continuousOn_relint_dom` —
  **Theorem 10.1**, in the real-valued and the `EReal`-valued form.
* `intrinsicInterior_vadd` — translation invariance of `ri`, which the chart needs and which
  Mathlib does not state.

## Design notes

**The chart is a linear subspace, not the affine hull.** `intrinsicInterior ℝ C` is *defined* as the
image of the interior taken inside `↥(affineSpan ℝ C)`, so it looks as if that subtype is the right
place to work. It is not: `↥(affineSpan ℝ C)` is an `AddTorsor`, and `Convex`, `ConvexOn` and every
Mathlib continuity theorem need a *module*. Fixing a point `x₀ ∈ C` and moving to a subspace `V`
spanned by `C - x₀` costs one translation and buys the entire module API.

**The subspace is a parameter, not a definition.** Every lemma here takes `V` together with
`hV : V = span ℝ (C - x₀)` rather than mentioning a `chartSpace C x₀` of its own. The reason is
operational: `chart C x₀ V` has type `Set ↥V`, so instance synthesis for `↥V` happens constantly,
and with `V` a definition that unfolds to a `Submodule.span` every such query redoes the unfolding
— rewriting inside `Set ↥(chartSpace C x₀)` then times out. With `V` opaque the same proofs go
through immediately, and the caller obtains an opaque `V` from `⟨_, rfl⟩`.

**Three lemmas do the reduction.** `Convex.relint_image` (Theorem 6.6) moves `ri` across the
inclusion `V → E`; `intrinsicInterior_eq_interior` collapses `ri` to `interior` inside `V`, because
`chart C x₀ V` affinely spans `V` by construction; and `intrinsicInterior_vadd` handles the
translation. None of them is new.

**Transporting continuity back needs a retraction, not an embedding.** `ContinuousOn` on the image
`x₀ + ι (int D)` does not follow formally from `ContinuousOn` on `int D` — the inclusion is an
embedding, but the cheap way to exploit that is to exhibit a continuous left inverse. In finite
dimensions `V` has a complement, so `LinearMap.linearProjOfIsCompl` gives one, and
`ContinuousOn.congr` finishes.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §10 (Theorem 10.1).
-/

open Pointwise Set

namespace Tdaf.ConvexAnalysis

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E} {x₀ : E} {V : Submodule ℝ E}

omit [FiniteDimensional ℝ E] in
/-- The relative interior is translation invariant. -/
theorem intrinsicInterior_vadd (v : E) (s : Set E) : ri (v +ᵥ s) = v +ᵥ ri s := by
  have h : ∀ t : Set E, v +ᵥ t = (AffineIsometryEquiv.constVAdd ℝ E v).toAffineIsometry '' t :=
    fun t => by rw [← Set.image_vadd]; rfl
  rw [h, h, AffineIsometry.intrinsicInterior_image]

/-- The **chart** of `C` at `x₀` in a subspace `V`: the directions `z ∈ V` with `x₀ + z ∈ C`. -/
def chart (C : Set E) (x₀ : E) (V : Submodule ℝ E) : Set V := {z | x₀ + (z : E) ∈ C}

omit [FiniteDimensional ℝ E] in
@[simp] theorem mem_chart {z : V} : z ∈ chart C x₀ V ↔ x₀ + (z : E) ∈ C := Iff.rfl

omit [FiniteDimensional ℝ E] in
/-- The chart maps onto the translate `C - x₀`. -/
theorem image_chart (hV : V = Submodule.span ℝ ((fun x => x - x₀) '' C)) :
    V.subtype '' chart C x₀ V = (fun x => x - x₀) '' C := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨x₀ + (z : E), hz, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x - x₀, hV ▸ Submodule.subset_span ⟨x, hx, rfl⟩⟩, ?_, rfl⟩
    change x₀ + (x - x₀) ∈ C
    rwa [add_sub_cancel]

omit [FiniteDimensional ℝ E] in
theorem zero_mem_chart (hx₀ : x₀ ∈ C) : (0 : V) ∈ chart C x₀ V := by
  change x₀ + ((0 : V) : E) ∈ C
  simpa using hx₀

omit [FiniteDimensional ℝ E] in
theorem convex_chart (hC : Convex ℝ C) : Convex ℝ (chart C x₀ V) := by
  intro z hz w hw a b ha hb hab
  change x₀ + ((a • z + b • w : V) : E) ∈ C
  have hsplit : x₀ + ((a • z + b • w : V) : E)
      = a • (x₀ + (z : E)) + b • (x₀ + (w : E)) := by
    push_cast
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]
  rw [hsplit]
  exact hC hz hw ha hb hab

omit [FiniteDimensional ℝ E] in
/-- The chart affinely spans the chart space: that is what makes `ri` collapse to `interior`
there. -/
theorem affineSpan_chart (hx₀ : x₀ ∈ C)
    (hV : V = Submodule.span ℝ ((fun x => x - x₀) '' C)) :
    affineSpan ℝ (chart C x₀ V) = ⊤ := by
  have h0 : (0 : V) ∈ chart C x₀ V := zero_mem_chart hx₀
  have hspan : Submodule.span ℝ (chart C x₀ V) = ⊤ := by
    refine Submodule.map_injective_of_injective V.injective_subtype ?_
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, image_chart hV, ← hV]
  have hvs : vectorSpan ℝ (chart C x₀ V) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.2 fun z hz => ?_
    have hmem := vsub_mem_vectorSpan ℝ hz h0
    simpa using hmem
  exact (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ V V ⟨0, h0⟩).2 hvs

/-- **The relative interior, computed in the chart.** `ri C` is the translate by `x₀` of the image
of the ordinary interior of `chart C x₀ V`. -/
theorem relint_eq_vadd_image_interior (hC : Convex ℝ C) (hx₀ : x₀ ∈ C)
    (hV : V = Submodule.span ℝ ((fun x => x - x₀) '' C)) :
    ri C = x₀ +ᵥ (V.subtype '' interior (chart C x₀ V)) := by
  have htrans : (fun x => x - x₀) '' C = (-x₀) +ᵥ C := by
    rw [← Set.image_vadd]
    exact Set.image_congr' fun x => sub_eq_neg_add x x₀
  have hstep : ri ((-x₀) +ᵥ C) = V.subtype '' interior (chart C x₀ V) := by
    have h2 : ri (chart C x₀ V) = interior (chart C x₀ V) :=
      intrinsicInterior_eq_interior (affineSpan_chart hx₀ hV)
    have h1 : ri (V.subtype '' chart C x₀ V) = V.subtype '' ri (chart C x₀ V) :=
      Convex.relint_image (convex_chart hC) V.subtype
    rw [image_chart hV, htrans, h2] at h1
    exact h1
  rw [← hstep, intrinsicInterior_vadd, vadd_vadd, add_neg_cancel, zero_vadd]

end Chart

section Thm101

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- The real-valued restriction of `f` is convex on `dom f`, in Mathlib's sense. -/
theorem ConvexFn.convexOn_toReal_dom (hf : ConvexFn f) (hp : Proper f) :
    ConvexOn ℝ (dom f) fun x => (f x).toReal := by
  rw [convexOn_iff_convexFn]
  have hrestrict : restrict (dom f) (fun x => (((f x).toReal : ℝ) : EReal)) = f := by
    funext x
    by_cases hx : x ∈ dom f
    · rw [restrict_of_mem hx]
      exact _root_.EReal.coe_toReal (mem_dom.1 hx).ne (hp.ne_bot x)
    · rw [restrict_of_notMem hx]
      exact (top_le_iff.1 (not_lt.1 hx)).symm
  rwa [hrestrict]

/-- **Rockafellar, Theorem 10.1**, real-valued form: a proper convex function is continuous,
relative to the affine hull of its domain, at every relative interior point. -/
theorem ConvexFn.continuousOn_toReal_relint_dom (hf : ConvexFn f) (hp : Proper f) :
    ContinuousOn (fun x => (f x).toReal) (ri (dom f)) := by
  obtain ⟨x₀, hx₀⟩ := hp.dom_nonempty
  obtain ⟨V, hV⟩ :
      ∃ V : Submodule ℝ E, V = Submodule.span ℝ ((fun x => x - x₀) '' dom f) := ⟨_, rfl⟩
  -- convexity, read through the chart
  have hconv : ConvexOn ℝ (dom f) (fun x => (f x).toReal) := hf.convexOn_toReal_dom hp
  have hshift : (AffineMap.const ℝ V x₀ + V.subtype.toAffineMap) ⁻¹' dom f
      = chart (dom f) x₀ V := rfl
  have hψ : ConvexOn ℝ (chart (dom f) x₀ V) fun z : V => (f (x₀ + (z : E))).toReal :=
    hshift ▸ hconv.comp_affineMap (AffineMap.const ℝ V x₀ + V.subtype.toAffineMap)
  have hcont : ContinuousOn (fun z : V => (f (x₀ + (z : E))).toReal)
      (interior (chart (dom f) x₀ V)) := ConvexOn.continuousOn_interior hψ
  -- a continuous retraction `E → V`, to carry continuity back
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  have hW' : IsCompl (LinearMap.range V.subtype) W := by rwa [Submodule.range_subtype]
  set r : E →ₗ[ℝ] V := LinearMap.linearProjOfIsCompl W V.subtype V.injective_subtype hW' with hr
  have hrz : ∀ z : V, r (z : E) = z := fun z =>
    LinearMap.linearProjOfIsCompl_apply_left W V.subtype V.injective_subtype hW' z
  have hρcont : Continuous fun x : E => r (x - x₀) :=
    r.continuous_of_finiteDimensional.comp (continuous_id.sub continuous_const)
  have himg := relint_eq_vadd_image_interior hf.convex_dom hx₀ hV
  have hmaps : Set.MapsTo (fun x : E => r (x - x₀)) (ri (dom f))
      (interior (chart (dom f) x₀ V)) := by
    intro x hx
    rw [himg] at hx
    obtain ⟨w, ⟨z, hz, rfl⟩, rfl⟩ := hx
    simpa [hrz z] using hz
  have heq : Set.EqOn (fun x => (f x).toReal)
      ((fun z : V => (f (x₀ + (z : E))).toReal) ∘ fun x : E => r (x - x₀)) (ri (dom f)) := by
    intro x hx
    rw [himg] at hx
    obtain ⟨w, ⟨z, hz, rfl⟩, rfl⟩ := hx
    simp [Function.comp_apply, hrz z]
  exact ContinuousOn.congr (hcont.comp hρcont.continuousOn hmaps) heq

/-- **Rockafellar, Theorem 10.1**: a proper convex function on a finite-dimensional space is
continuous, relative to the affine hull of its effective domain, on `ri (dom f)`. -/
theorem ConvexFn.continuousOn_relint_dom (hf : ConvexFn f) (hp : Proper f) :
    ContinuousOn f (ri (dom f)) := by
  have hcoe : Set.EqOn f (fun x => (((f x).toReal : ℝ) : EReal)) (ri (dom f)) := by
    intro x hx
    have hx' : x ∈ dom f := intrinsicInterior_subset hx
    exact (_root_.EReal.coe_toReal (mem_dom.1 hx').ne (hp.ne_bot x)).symm
  exact ContinuousOn.congr
    (continuous_coe_real_ereal.comp_continuousOn (hf.continuousOn_toReal_relint_dom hp)) hcoe

end Thm101

end Tdaf.ConvexAnalysis
