/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.Convex.Exposed
import Tdaf.Analysis.Convex.RelativeInterior

/-!
# Faces of a convex set

Rockafellar's §18. A **face** of a convex set `C` is a convex subset `C'` of `C` such that every
closed line segment in `C` with a relative interior point in `C'` has both endpoints in `C'`. The
whole section rests on **Theorem 18.1**, which upgrades "line segment" to "arbitrary convex
subset": if `D ⊆ C` is convex and `ri D` meets `C'`, then all of `D` lies in `C'`.

## Main results

* `IsFace` — Rockafellar's face, as `Mathlib`'s `IsExtreme ℝ C C'` plus convexity of `C'`.
* `IsFace.subset_of_relint_inter_nonempty` — **Theorem 18.1**.
* `IsFace.eq_inter_closure` — Corollary 18.1.1: `C' = C ∩ cl C'`; a face of a closed convex set is
  closed.
* `IsFace.eq_of_relint_inter_nonempty` — Corollary 18.1.2: faces whose relative interiors meet are
  equal.
* `IsFace.disjoint_relint`, `IsFace.subset_intrinsicFrontier`,
  `IsFace.finrank_vectorSpan_lt` — Corollary 18.1.3: a proper face lies in the relative boundary
  and has strictly smaller dimension.
* `exists_isFace_subset_relint` — the engine of **Theorem 18.2**: every nonempty relatively open
  convex subset of `C` lies in the relative interior of a (unique) face of `C`.
* `exists_isFace_mem_relint`, `eq_iUnion_relint_isFace`, `IsFace.relint_pairwise_disjoint`,
  `IsFace.relint_maximal` — **Theorem 18.2**: the relative interiors of the nonempty faces
  partition `C`, and they are exactly the maximal relatively open convex subsets of `C`.
* `exists_notMem_relint_mem_segment` — **Theorem 18.4** for compact sets.
* `convexHull_extremePoints` — **Corollary 18.5.1** (Minkowski's theorem): a compact convex set is
  the convex hull of its extreme points. This is Theorem 18.5 in the bounded case.
* `extremePoints_nonempty` — **Corollary 18.5.3** for compact sets.

Extreme points and exposed faces are Mathlib's `Set.extremePoints` and `IsExposed`;
`isFace_singleton` and `IsExposed.isFace` connect them to `IsFace`.

## What is not here

**Theorem 18.5 for unbounded sets, and with it Theorems 18.3, 18.4 in general, 18.6, 18.7 and
18.8, are elsewhere.** All of them are stated in terms of Rockafellar's `conv S` for an `S`
containing both points *and directions*, which is `convexHullPD P D` in `HullDirections.lean`;
`Representation.lean` then carries Theorems 18.3, 18.4, 18.5 and 18.6 (Straszewicz) with
Corollaries 18.3.1 and 18.5.2–18.5.3, and `Exposed.lean` and `Tangent.lean` carry Theorems 18.7
and 18.8. What is here is the bounded case, which is what §19's polyhedral theory and the
Krein–Milman corollaries actually consume.

## Design notes

**`IsFace` bundles `IsExtreme` with convexity, and the convexity is not redundant.** For convex
`C`, an extreme subset need not be a face: `C = [0, 1] ⊆ ℝ` has `C' = {0, 1}` extreme but not
convex, and `{0, 1}` is not a face of `[0, 1]` in Rockafellar's sense — the plan file's earlier
guess that the two notions coincide for convex `C` is wrong in exactly this way. Everything else
about extreme subsets does transfer, so `IsFace` is a structure extending `IsExtreme ℝ` and the
`IsExtreme` API is reused verbatim through `toIsExtreme`.

**Theorem 18.1 is the prolongation lemma of §6 read backwards.**
`exists_one_lt_smul_mem_of_mem_relint` prolongs the segment from `x ∈ D` past a relative interior
point `z ∈ ri D` and stays in `D`;
`combo_prolong` then exhibits `z` as an interior point of the segment from `x` to the prolonged
point, and the face property returns `x ∈ C'`. No case distinction for `x = z` is needed — the
prolongation lemma already handles it.

**Theorem 18.2 needs a supporting hyperplane, and that is Corollary 11.6.2.** For the smallest face
`C'` containing a relatively open convex `D`, if `D` missed `ri C'` then
`notMem_relint_iff_exists_isMaxOn` would produce a linear function maximised over `C'` at a point of
`D` but not constant on `C'`; `eq_of_isMaxOn_of_mem_relint` makes it constant on `D` (this is where
`ri D = D` is used), so the exposed face it cuts out of `C'` would be a strictly smaller face still
containing `D`. Corollary 6.5.2 then upgrades `D ∩ ri C' ≠ ∅` to `D = ri D ⊆ ri C'`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §18 (Theorems 18.1,
  18.2, 18.4 and 18.5 in the bounded case, Corollaries 18.1.1, 18.1.2, 18.1.3, 18.5.1, 18.5.3).
-/

open Set

namespace Tdaf.ConvexAnalysis

/-! ### The definition and its elementary calculus -/

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C C' C'' D : Set E}

/-- **Rockafellar's face**: a convex subset `C'` of a convex set `C` such that every closed line
segment in `C` with a relative interior point in `C'` has both endpoints in `C'`.

The segment condition is exactly Mathlib's `IsExtreme ℝ C C'`. Convexity of `C'` is a genuine extra
requirement: `{0, 1}` is an extreme subset of `[0, 1]` but not a face of it. -/
structure IsFace (C C' : Set E) : Prop extends IsExtreme ℝ C C' where
  /-- A face is a convex set. -/
  convex : Convex ℝ C'

/-- Every convex set is a face of itself: the greatest element of the lattice of faces. -/
protected theorem Convex.isFace_self (hC : Convex ℝ C) : IsFace C C :=
  ⟨IsExtreme.rfl, hC⟩

/-- The empty set is a face of every set: the least element of the lattice of faces. -/
protected theorem IsFace.empty : IsFace C (∅ : Set E) :=
  ⟨⟨empty_subset _, fun _ _ _ _ z hz _ => absurd hz (notMem_empty z)⟩, convex_empty⟩

/-- A face of a face is a face. -/
protected theorem IsFace.trans (h₁ : IsFace C C') (h₂ : IsFace C' C'') : IsFace C C'' :=
  ⟨h₁.toIsExtreme.trans h₂.toIsExtreme, h₂.convex⟩

/-- A face of `C` that happens to lie inside an intermediate convex set `D` is a face of `D`. -/
protected theorem IsFace.mono (h : IsFace C C'') (hDC : D ⊆ C) (hC''D : C'' ⊆ D) : IsFace D C'' :=
  ⟨h.toIsExtreme.mono hDC hC''D, h.convex⟩

/-- The intersection of two faces is a face. -/
protected theorem IsFace.inter (h₁ : IsFace C C') (h₂ : IsFace C C'') : IsFace C (C' ∩ C'') :=
  ⟨h₁.toIsExtreme.inter h₂.toIsExtreme, h₁.convex.inter h₂.convex⟩

/-- The intersection of a nonempty family of faces is a face. Together with `Convex.isFace_self`
and `IsFace.empty` this makes the faces of `C` a complete lattice under inclusion. -/
theorem isFace_sInter {F : Set (Set E)} (hF : F.Nonempty) (h : ∀ B ∈ F, IsFace C B) :
    IsFace C (⋂₀ F) :=
  ⟨isExtreme_sInter hF fun B hB => (h B hB).toIsExtreme,
    convex_sInter fun B hB => (h B hB).convex⟩

/-- Rockafellar's **extreme points** are the zero-dimensional faces, so they are Mathlib's
`Set.extremePoints`. -/
@[simp]
theorem isFace_singleton {x : E} : IsFace C {x} ↔ x ∈ C.extremePoints ℝ :=
  ⟨fun h => isExtreme_singleton.1 h.toIsExtreme,
    fun h => ⟨isExtreme_singleton.2 h, convex_singleton x⟩⟩

/-- **Exposed faces are faces**: the set on which a linear function attains its maximum over a
convex set `C` is a face of `C`. This is the only source of faces used in the proof of
Theorem 18.2. -/
theorem Convex.isFace_inter_setOf_eq (hC : Convex ℝ C) {g : E →ₗ[ℝ] ℝ} {α : ℝ}
    (hmax : ∀ y ∈ C, g y ≤ α) : IsFace C (C ∩ {w | g w = α}) := by
  refine ⟨⟨inter_subset_left, ?_⟩, hC.inter (convex_hyperplane g.isLinear α)⟩
  rintro x hx y hy z ⟨_, hz⟩ ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨hx, ?_⟩
  have hz' : a * g x + b * g y = α := by
    rw [← show g (a • x + b • y) = α from hz, map_add, map_smul, map_smul, smul_eq_mul,
      smul_eq_mul]
  change g x = α
  by_contra hne
  have hlt : g x < α := lt_of_le_of_ne (hmax x hx) hne
  have h1 : a * g x < a * α := mul_lt_mul_of_pos_left hlt ha
  have h2 : b * g y ≤ b * α := mul_le_mul_of_nonneg_left (hmax y hy) hb.le
  have h3 : a * α + b * α = α := by rw [← add_mul, hab, one_mul]
  linarith

end Defs

section Exposed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C C' : Set E}

/-- Mathlib's exposed faces are faces. -/
protected theorem IsExposed.isFace (h : IsExposed ℝ C C') (hC : Convex ℝ C) : IsFace C C' :=
  ⟨h.isExtreme, h.convex hC⟩

end Exposed

/-! ### Theorem 18.1 and its corollaries -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C C' C₁ C₂ D : Set E}

omit [FiniteDimensional ℝ E] in
/-- **Rockafellar, Theorem 18.1**: a face absorbs every convex subset of `C` whose relative
interior it meets. This is the strengthening of the defining segment property to arbitrary convex
sets, and every other result of §18 goes through it.

Convexity of `D` is not needed: the prolongation lemma `exists_one_lt_smul_mem_of_mem_relint`
already carries everything the argument uses about `ri D`. -/
theorem IsFace.subset_of_relint_inter_nonempty (hface : IsFace C C')
    (hDC : D ⊆ C) (h : (ri D ∩ C').Nonempty) : D ⊆ C' := by
  obtain ⟨z, hzD, hzC'⟩ := h
  intro x hx
  obtain ⟨μ, hμ, hy⟩ := exists_one_lt_smul_mem_of_mem_relint hzD (subset_affineSpan ℝ D hx)
  have hμ0 : (0 : ℝ) < μ := lt_trans zero_lt_one hμ
  have hinv : μ⁻¹ < 1 := by rw [inv_lt_one_iff₀]; exact Or.inr hμ
  refine hface.left_mem_of_mem_openSegment (hDC hx) (hDC hy) hzC' ?_
  exact ⟨1 - μ⁻¹, μ⁻¹, by linarith, inv_pos.2 hμ0, by ring, combo_prolong x z hμ0.ne'⟩

/-- **Rockafellar, Corollary 18.1.1**: a face is cut out of `C` by its own closure. In particular a
face of a closed convex set is closed. -/
theorem IsFace.eq_inter_closure (hC : Convex ℝ C) (hface : IsFace C C') :
    C' = C ∩ closure C' := by
  refine Subset.antisymm (fun x hx => ⟨hface.subset hx, subset_closure hx⟩) ?_
  rcases C'.eq_empty_or_nonempty with rfl | hne
  · simp
  have hDconv : Convex ℝ (C ∩ closure C') := hC.inter hface.convex.closure
  have hDne : (C ∩ closure C').Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hface.subset hx, subset_closure hx⟩
  have hmeet : ((C ∩ closure C') ∩ ri C').Nonempty := by
    obtain ⟨z, hz⟩ := Convex.relint_nonempty hface.convex hne
    exact ⟨z, ⟨hface.subset (intrinsicInterior_subset hz),
      subset_closure (intrinsicInterior_subset hz)⟩, hz⟩
  have hri : ri (C ∩ closure C') ⊆ ri C' :=
    Convex.relint_subset_relint_of_subset_closure hface.convex hDconv inter_subset_right hmeet
  obtain ⟨z, hz⟩ := Convex.relint_nonempty hDconv hDne
  exact hface.subset_of_relint_inter_nonempty inter_subset_left
    ⟨z, hz, intrinsicInterior_subset (hri hz)⟩

/-- A face of a closed convex set is closed. -/
theorem IsFace.isClosed (hC : Convex ℝ C) (hCcl : IsClosed C) (hface : IsFace C C') :
    IsClosed C' := by
  rw [hface.eq_inter_closure hC]
  exact hCcl.inter isClosed_closure

omit [FiniteDimensional ℝ E] in
/-- **Rockafellar, Corollary 18.1.2**: two faces whose relative interiors have a point in common
are equal. This is what makes the relative interiors of the faces a *partition* in Theorem 18.2. -/
theorem IsFace.eq_of_relint_inter_nonempty (h₁ : IsFace C C₁) (h₂ : IsFace C C₂)
    (h : (ri C₁ ∩ ri C₂).Nonempty) : C₁ = C₂ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  refine Subset.antisymm ?_ ?_
  · exact h₂.subset_of_relint_inter_nonempty h₁.subset ⟨z, hz₁, intrinsicInterior_subset hz₂⟩
  · exact h₁.subset_of_relint_inter_nonempty h₂.subset ⟨z, hz₂, intrinsicInterior_subset hz₁⟩

omit [FiniteDimensional ℝ E] in
/-- **Rockafellar, Corollary 18.1.3**, first half: a face other than `C` itself misses `ri C`. -/
theorem IsFace.disjoint_relint (hface : IsFace C C') (hne : C' ≠ C) :
    Disjoint C' (ri C) := by
  rw [Set.disjoint_left]
  intro x hxC' hxri
  exact hne (Subset.antisymm hface.subset
    (hface.subset_of_relint_inter_nonempty Subset.rfl ⟨x, hxri, hxC'⟩))

/-- **Rockafellar, Corollary 18.1.3**: a face other than `C` itself is contained in the relative
boundary of `C`. -/
theorem IsFace.subset_intrinsicFrontier (hface : IsFace C C') (hne : C' ≠ C) :
    C' ⊆ intrinsicFrontier ℝ C := by
  intro x hx
  rw [← closure_sdiff_intrinsicInterior (𝕜 := ℝ) C]
  exact ⟨subset_closure (hface.subset hx),
    fun hxri => (Set.disjoint_left.1 (hface.disjoint_relint hne)) hx hxri⟩

/-- A face has the same affine hull as `C` only if it is all of `C`. This is the step from the
relative-boundary statement of Corollary 18.1.3 to the dimension statement. -/
theorem IsFace.affineSpan_ne (hface : IsFace C C') (hne' : C'.Nonempty)
    (hne : C' ≠ C) : affineSpan ℝ C' ≠ affineSpan ℝ C := by
  intro hspan
  obtain ⟨z, hz⟩ := Convex.relint_nonempty hface.convex hne'
  refine (Set.disjoint_left.1 (hface.disjoint_relint hne)) (intrinsicInterior_subset hz) ?_
  rw [mem_intrinsicInterior_iff] at hz ⊢
  obtain ⟨hzA, ε, hε, hball⟩ := hz
  exact ⟨hspan ▸ hzA, ε, hε, fun y hy hd => hface.subset (hball y (hspan ▸ hy) hd)⟩

/-- **Rockafellar, Corollary 18.1.3**, the dimension statement: a nonempty face other than `C`
itself has strictly smaller dimension than `C`. -/
theorem IsFace.finrank_vectorSpan_lt (hface : IsFace C C') (hne' : C'.Nonempty)
    (hne : C' ≠ C) :
    Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) := by
  have hle : vectorSpan ℝ C' ≤ vectorSpan ℝ C := vectorSpan_mono ℝ hface.subset
  refine lt_of_le_of_ne (Submodule.finrank_mono hle) fun heq => ?_
  have hdir : vectorSpan ℝ C' = vectorSpan ℝ C := Submodule.eq_of_le_of_finrank_eq hle heq
  refine hface.affineSpan_ne hne' hne (AffineSubspace.ext_of_direction_eq ?_ ?_)
  · rw [direction_affineSpan, direction_affineSpan, hdir]
  · obtain ⟨x, hx⟩ := hne'
    exact ⟨x, subset_affineSpan ℝ C' hx, subset_affineSpan ℝ C (hface.subset hx)⟩

/-! ### Theorem 18.2: the relative interiors of the faces partition `C` -/

/-- The engine of **Theorem 18.2**: every nonempty relatively open convex subset `D` of `C` lies in
the relative interior of a face of `C`, namely the smallest face containing `D`.

Rockafellar's proof: were `D` inside the relative boundary of that smallest face `C'`, a supporting
hyperplane to `C'` through `D` (Corollary 11.6.2) would cut out a strictly smaller face still
containing `D`. So `D` meets `ri C'`, and Corollary 6.5.2 gives `D = ri D ⊆ ri C'`. -/
theorem exists_isFace_subset_relint (hC : Convex ℝ C) (hD : Convex ℝ D) (hDC : D ⊆ C)
    (hne : D.Nonempty) (hopen : ri D = D) : ∃ C', IsFace C C' ∧ D ⊆ ri C' := by
  classical
  set F : Set (Set E) := {B | IsFace C B ∧ D ⊆ B} with hFdef
  have hFne : F.Nonempty := ⟨C, Convex.isFace_self hC, hDC⟩
  set C' : Set E := ⋂₀ F with hC'def
  have hC'face : IsFace C C' := isFace_sInter hFne fun B hB => hB.1
  have hDC' : D ⊆ C' := fun x hx => mem_sInter.2 fun B hB => hB.2 hx
  have hmeet : (D ∩ ri C').Nonempty := by
    obtain ⟨x, hxD⟩ := hne
    by_contra hcon
    have hxnot : x ∉ ri C' := fun h => hcon ⟨x, hxD, h⟩
    obtain ⟨g, hle, y, hyC', hyne⟩ :=
      (notMem_relint_iff_exists_isMaxOn hC'face.convex (hDC' hxD)).1 hxnot
    -- `g` is maximised over `C'` at `x ∈ ri D`, hence constant on `D`
    have hxriD : x ∈ ri D := by rw [hopen]; exact hxD
    have hconst : ∀ w ∈ D, (g : E →ₗ[ℝ] ℝ) w = (g : E →ₗ[ℝ] ℝ) x :=
      eq_of_isMaxOn_of_mem_relint (C := D) hxriD fun w hw => hle w (hDC' hw)
    have hface'' : IsFace C' (C' ∩ {w | (g : E →ₗ[ℝ] ℝ) w = (g : E →ₗ[ℝ] ℝ) x}) :=
      Convex.isFace_inter_setOf_eq hC'face.convex fun w hw => hle w hw
    have hmem : C' ∩ {w | (g : E →ₗ[ℝ] ℝ) w = (g : E →ₗ[ℝ] ℝ) x} ∈ F :=
      ⟨hC'face.trans hface'', fun w hw => ⟨hDC' hw, hconst w hw⟩⟩
    exact hyne (mem_sInter.1 (hC'def ▸ hyC') _ hmem).2
  have hsub : ri D ⊆ ri C' :=
    Convex.relint_subset_relint_of_subset_closure hC'face.convex hD (hDC'.trans subset_closure)
      hmeet
  exact ⟨C', hC'face, hopen ▸ hsub⟩

/-- **Theorem 18.2**, the union half: every point of `C` is a relative interior point of some face
of `C`. -/
theorem exists_isFace_mem_relint (hC : Convex ℝ C) {x : E} (hx : x ∈ C) :
    ∃ C', IsFace C C' ∧ x ∈ ri C' := by
  obtain ⟨C', hface, hsub⟩ := exists_isFace_subset_relint hC (convex_singleton x)
    (singleton_subset_iff.2 hx) ⟨x, rfl⟩ (intrinsicInterior_singleton x)
  exact ⟨C', hface, hsub rfl⟩

/-- **Theorem 18.2**, the union half, as an equation. -/
theorem eq_iUnion_relint_isFace (hC : Convex ℝ C) :
    C = ⋃ C' ∈ {B : Set E | IsFace C B}, ri C' := by
  refine Subset.antisymm (fun x hx => ?_) ?_
  · obtain ⟨C', hface, hmem⟩ := exists_isFace_mem_relint hC hx
    exact mem_biUnion hface hmem
  · exact iUnion₂_subset fun C' hface => intrinsicInterior_subset.trans hface.subset

omit [FiniteDimensional ℝ E] in
/-- **Theorem 18.2**, the disjointness half: distinct faces have disjoint relative interiors. -/
theorem IsFace.relint_pairwise_disjoint (h₁ : IsFace C C₁) (h₂ : IsFace C C₂) (hne : C₁ ≠ C₂) :
    Disjoint (ri C₁) (ri C₂) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hcon
  exact hne (h₁.eq_of_relint_inter_nonempty h₂ (nonempty_iff_ne_empty.2 hcon))

/-- **Theorem 18.2**, the maximality half: the relative interior of a nonempty face is a *maximal*
relatively open convex subset of `C`. -/
theorem IsFace.relint_maximal (hC : Convex ℝ C) (hface : IsFace C C') (hne' : C'.Nonempty)
    (hD : Convex ℝ D) (hopen : ri D = D) (hsub : ri C' ⊆ D) (hDC : D ⊆ C) : D = ri C' := by
  obtain ⟨z, hz⟩ := Convex.relint_nonempty hface.convex hne'
  obtain ⟨C'', hface'', hDsub⟩ := exists_isFace_subset_relint hC hD hDC ⟨z, hsub hz⟩ hopen
  have : C' = C'' := hface.eq_of_relint_inter_nonempty hface'' ⟨z, hz, hDsub (hsub hz)⟩
  exact Subset.antisymm (this ▸ hDsub) hsub

/-- The relative interior of a convex set is relatively open, so `IsFace.relint_maximal` really is
a maximality statement inside the family it quantifies over. -/
theorem IsFace.relint_relint (hface : IsFace C C') : ri (ri C') = ri C' :=
  Convex.relint_relint hface.convex

end Main

/-! ### Theorems 18.4 and 18.5 for bounded sets: Minkowski's theorem -/

section Bounded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {C : Set E}

omit [FiniteDimensional ℝ E] in
/-- **Rockafellar, Theorem 18.4** for compact sets: a relative interior point of a compact set of
positive dimension lies on a segment joining two points that are not relative interior points.

Rockafellar states Theorem 18.4 for closed convex sets that are neither affine sets nor closed
halves of affine sets; compactness is a cruder hypothesis but it is all that Minkowski's theorem
needs, and it makes the proof elementary. The line through `x` in a direction of `vectorSpan ℝ C`
meets `C` in a compact set of parameters, and the prolongation principle puts its largest and
smallest elements outside `ri C`. Convexity of `C` is never used. -/
theorem exists_notMem_relint_mem_segment (hcomp : IsCompact C) (hdim : vectorSpan ℝ C ≠ ⊥)
    {x : E} (hx : x ∈ ri C) :
    ∃ a ∈ C, ∃ b ∈ C, a ∉ ri C ∧ b ∉ ri C ∧ x ∈ segment ℝ a b := by
  obtain ⟨d, hdmem, hdne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hdim
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.2 hdne
  have hxC : x ∈ C := intrinsicInterior_subset hx
  set T : Set ℝ := {t : ℝ | x + t • d ∈ C} with hTdef
  have hline : ∀ t : ℝ, x + t • d ∈ affineSpan ℝ C := by
    intro t
    have hv : t • d ∈ (affineSpan ℝ C).direction := by
      rw [direction_affineSpan]
      exact Submodule.smul_mem _ t hdmem
    have hmem := AffineSubspace.vadd_mem_of_mem_direction hv (subset_affineSpan ℝ C hxC)
    rwa [vadd_eq_add, add_comm] at hmem
  -- the parameter set is compact
  have hcont : Continuous fun t : ℝ => x + t • d := by fun_prop
  have hTclosed : IsClosed T := hcomp.isClosed.preimage hcont
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x).1 hcomp.isBounded
  have hTsub : T ⊆ Set.Icc (-(R / ‖d‖)) (R / ‖d‖) := by
    intro t ht
    have hmem : x + t • d ∈ Metric.closedBall x R := hR ht
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    have he : x + t • d - x = t • d := by module
    rw [he, norm_smul, Real.norm_eq_abs] at hmem
    exact Set.mem_Icc.2 (abs_le.1 ((le_div_iff₀ hdnorm).2 hmem))
  have hTcomp : IsCompact T := isCompact_Icc.of_isClosed_subset hTclosed hTsub
  have hT0 : (0 : ℝ) ∈ T := by
    change x + (0 : ℝ) • d ∈ C
    simpa using hxC
  obtain ⟨tp, htp⟩ := hTcomp.exists_isGreatest ⟨0, hT0⟩
  obtain ⟨tm, htm⟩ := hTcomp.exists_isLeast ⟨0, hT0⟩
  -- `x` is strictly inside the parameter interval, because `x ∈ ri C`
  obtain ⟨hxA, ε, hε, hball⟩ := mem_intrinsicInterior_iff.1 hx
  set s : ℝ := ε / (2 * ‖d‖) with hsdef
  have hspos : 0 < s := by positivity
  have hsT : ∀ u : ℝ, |u| ≤ s → u ∈ T := by
    intro u hu
    refine hball _ (hline u) ?_
    have he : x + u • d - x = u • d := by module
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs]
    have hprod : |u| * ‖d‖ ≤ s * ‖d‖ := by nlinarith
    have hs' : s * ‖d‖ = ε / 2 := by
      rw [hsdef]
      field_simp
    linarith [hs' ▸ hprod]
  have htppos : 0 < tp := lt_of_lt_of_le hspos (htp.2 (hsT s (le_of_eq (abs_of_pos hspos))))
  have htmneg : tm < 0 := by
    have hle := htm.2 (hsT (-s) (by rw [abs_neg, abs_of_pos hspos]))
    linarith
  have hlt : tm < tp := lt_trans htmneg htppos
  have hgap : (0 : ℝ) < tp - tm := by linarith
  refine ⟨x + tm • d, htm.1, x + tp • d, htp.1, ?_, ?_, ?_⟩
  · -- the lower endpoint is not a relative interior point
    intro hari
    obtain ⟨μ, hμ, hw⟩ := exists_one_lt_smul_mem_of_mem_relint hari (hline tp)
    have heq : (1 - μ) • (x + tp • d) + μ • (x + tm • d)
        = x + ((1 - μ) * tp + μ * tm) • d := by module
    rw [heq] at hw
    have hmem : (1 - μ) * tp + μ * tm ∈ T := hw
    nlinarith [htm.2 hmem, mul_pos (sub_pos.2 hμ) hgap]
  · -- the upper endpoint is not a relative interior point
    intro hbri
    obtain ⟨μ, hμ, hw⟩ := exists_one_lt_smul_mem_of_mem_relint hbri (hline tm)
    have heq : (1 - μ) • (x + tm • d) + μ • (x + tp • d)
        = x + ((1 - μ) * tm + μ * tp) • d := by module
    rw [heq] at hw
    have hmem : (1 - μ) * tm + μ * tp ∈ T := hw
    nlinarith [htp.2 hmem, mul_pos (sub_pos.2 hμ) hgap]
  · refine ⟨tp / (tp - tm), -tm / (tp - tm), div_nonneg htppos.le hgap.le,
      div_nonneg (neg_nonneg.2 htmneg.le) hgap.le, by field_simp; ring, ?_⟩
    match_scalars <;> field_simp <;> ring

/-- The induction behind Minkowski's theorem: a compact set of dimension at most `n` that is convex
lies in the convex hull of its extreme points. -/
private theorem subset_convexHull_extremePoints_aux :
    ∀ (n : ℕ) (C : Set E), Module.finrank ℝ (vectorSpan ℝ C) ≤ n → IsCompact C → Convex ℝ C →
      C ⊆ convexHull ℝ (C.extremePoints ℝ) := by
  intro n
  induction n with
  | zero =>
    intro C hcard _ _ x hx
    have hbot : vectorSpan ℝ C = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hcard)
    have hCx : C = {x} := ((vectorSpan_eq_bot_iff_subsingleton ℝ).1 hbot).eq_singleton_of_mem hx
    rw [hCx, extremePoints_singleton, convexHull_singleton]
    exact rfl
  | succ n ih =>
    intro C hcard hcomp hconv x hx
    -- a relative boundary point sits in the relative interior of a strictly smaller face
    have hbd : ∀ y ∈ C, y ∉ ri C → y ∈ convexHull ℝ (C.extremePoints ℝ) := by
      intro y hy hyri
      obtain ⟨C', hface, hyC'⟩ := exists_isFace_mem_relint hconv hy
      have hC'ne : C' ≠ C := fun h => hyri (h ▸ hyC')
      have hC'comp : IsCompact C' :=
        hcomp.of_isClosed_subset (hface.isClosed hconv hcomp.isClosed) hface.subset
      have hlt : Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) :=
        hface.finrank_vectorSpan_lt ⟨y, intrinsicInterior_subset hyC'⟩ hC'ne
      exact convexHull_mono hface.toIsExtreme.extremePoints_subset_extremePoints
        (ih C' (by omega) hC'comp hface.convex (intrinsicInterior_subset hyC'))
    by_cases hri : x ∈ ri C
    · by_cases hbot : vectorSpan ℝ C = ⊥
      · have hCx : C = {x} := ((vectorSpan_eq_bot_iff_subsingleton ℝ).1 hbot).eq_singleton_of_mem hx
        rw [hCx, extremePoints_singleton, convexHull_singleton]
        exact rfl
      · obtain ⟨a, haC, b, hbC, hari, hbri, hseg⟩ :=
          exists_notMem_relint_mem_segment hcomp hbot hri
        exact (convex_convexHull ℝ _).segment_subset (hbd a haC hari) (hbd b hbC hbri) hseg
    · exact hbd x hx hri

/-- **Rockafellar, Corollary 18.5.1** (Minkowski's theorem): a closed bounded convex set is the
convex hull of its extreme points. This is Theorem 18.5 in the case where `C` has no directions of
recession, and it is stronger than Mathlib's Krein–Milman theorem
(`closure_convexHull_extremePoints`), which only gives the *closed* convex hull — the set of
extreme points need not be closed even for a compact `C`.

The proof is Rockafellar's induction on `dim C`: a relative boundary point lies in the relative
interior of a face of strictly smaller dimension (Theorem 18.2 and Corollary 18.1.3), which is
again compact (Corollary 18.1.1), and a relative interior point lies on a segment joining two
relative boundary points (Theorem 18.4). -/
theorem convexHull_extremePoints (hcomp : IsCompact C) (hconv : Convex ℝ C) :
    convexHull ℝ (C.extremePoints ℝ) = C :=
  Subset.antisymm (convexHull_min extremePoints_subset hconv)
    (subset_convexHull_extremePoints_aux _ C le_rfl hcomp hconv)

/-- **Rockafellar, Corollary 18.5.3** for compact sets: a nonempty compact convex set has an
extreme point. Rockafellar's own derivation — the convex hull of the empty set is empty. -/
theorem extremePoints_nonempty (hcomp : IsCompact C) (hconv : Convex ℝ C) (hne : C.Nonempty) :
    (C.extremePoints ℝ).Nonempty := by
  rcases (C.extremePoints ℝ).eq_empty_or_nonempty with hem | h
  · rw [← convexHull_extremePoints hcomp hconv, hem, convexHull_empty] at hne
    exact absurd hne Set.not_nonempty_empty
  · exact h

end Bounded

end Tdaf.ConvexAnalysis
