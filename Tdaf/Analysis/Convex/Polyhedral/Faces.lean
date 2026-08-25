/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Polyhedral.Ops
import Tdaf.Analysis.Convex.Representation

/-!
# Finite generation and a finite set of faces

A closed convex set has only finitely many faces exactly when it is finitely generated. This is
the third description of a polyhedral convex set: `Polyhedral/Defs.lean` identifies "polyhedral"
with "finitely generated", and this module adds "closed, with a finite set of faces".

## Main results

* `FinitelyGenerated.finite_setOf_isFace` — a finitely generated set has finitely many faces.
  Each face is the hull of the points among the generators it contains together with the
  generating directions in which it recedes (`IsFace.eq_convexHullPD`), so the faces are indexed
  by a pair of subsets of the two generating sets. `FinitelyGenerated.of_isFace` is the
  accompanying statement that such a face is itself finitely generated.
* `finitelyGenerated_of_finite_setOf_isFace_of_containsNoLine` — a closed convex set that
  contains no lines and has finitely many faces is finitely generated. The internal
  representation theorem `convexHullPD_extremePoints_extremeDirections` writes the set as the
  hull of its extreme points and extreme directions, and the two finiteness counts are
  `finite_extremePoints_of_finite_setOf_isFace` and `exists_finite_generating_extremeDirections`.
* `polyhedral_of_finite_setOf_isFace` — the same conclusion with no hypothesis on lines, by the
  direct-sum decomposition `C = N + (C ∩ M)` along the lineality space together with the face
  correspondence `isFaceEquivInter`.
* `polyhedral_iff_isClosed_finite_setOf_isFace` — the characterisation the two halves give.

## Design notes

**Extreme directions are counted as rays, not as vectors.** `extremeDirections C` is closed under
multiplication by positive scalars, so it is never finite. What finiteness of the face set bounds
is the number of half-line faces, and `exists_finite_generating_extremeDirections` turns that
bound into a finite set of generators by choosing, for every face, a direction vector for it when
it happens to be a half-line, and intersecting the resulting finite image with
`extremeDirections C` to discard the faces that are not. Two generators of one half-line face lie
in the recession cone of that face, which is a single ray, so the chosen vector generates every
extreme direction whose half-line face it came from.

**The two counting lemmas are algebraic; everything after them is finite-dimensional.** Neither
`finite_extremePoints_of_finite_setOf_isFace` nor
`exists_finite_generating_extremeDirections` needs a topology: an extreme point is a singleton
face and an extreme direction is a half-line face, and both facts are definitional. The
representation theorem they are used with is genuinely finite-dimensional, and so is everything
about `Polyhedral`, so the rest of the file sits in the finite-dimensional layer by necessity
rather than by default.

**The lineality reduction is carried out on `Polyhedral`, not on `FinitelyGenerated`.** Once
`C ∩ M` is known to be finitely generated, `C = N + (C ∩ M)` is a sum of two polyhedral sets —
`polyhedral_coe_submodule` and `Polyhedral.add` — so no generating set for a subspace has to be
produced, and no basis is chosen.

## What is not here

**The tangent-half-space route to a system of inequalities.** A full-dimensional closed convex
set is the intersection of its tangent closed half-spaces (`Tangent.lean`), each of which is
determined by the exposed face it touches, so a finite face set bounds them too. That is a second
proof that finitely many faces implies *polyhedrality*, and it is not here: it needs a reduction
of a lower-dimensional set to a full-dimensional one inside its own affine hull, whereas finite
generation is reached with no dimension count at all and `FinitelyGenerated.polyhedral` then
supplies the inequalities.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §19, Theorem 19.1,
  and §18, Theorems 18.3 and 18.5.
-/

open Set

open scoped Pointwise

namespace Tdaf.ConvexAnalysis

/-! ### Counting extreme points and extreme directions -/

section Counting

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E}

/-- **A set with finitely many faces has finitely many extreme points**, because the extreme
points are exactly the singleton faces (`isFace_singleton`). -/
theorem finite_extremePoints_of_finite_setOf_isFace
    (hfin : {C' : Set E | IsFace C C'}.Finite) : (C.extremePoints ℝ).Finite := by
  refine Set.Finite.of_finite_image (hfin.subset ?_) Set.singleton_injective.injOn
  rintro _ ⟨x, hx, rfl⟩
  exact isFace_singleton.2 hx

/-- **A set with finitely many faces has finitely many extreme rays.** The set
`extremeDirections C` is closed under positive rescaling and so is never finite; what the face
count bounds is the number of rays, and the conclusion is a finite subset of the extreme
directions that generates all of them as a pointed cone.

The mechanism: every extreme direction is the direction of a half-line face, and every generator
of a given half-line face lies in the recession cone of that face, which is a single ray. -/
theorem exists_finite_generating_extremeDirections
    (hfin : {C' : Set E | IsFace C C'}.Finite) :
    ∃ D : Set E, D.Finite ∧ D ⊆ extremeDirections C ∧
      extremeDirections C ⊆ (PointedCone.hull ℝ D : Set E) := by
  classical
  have hchoice : ∀ C' : Set E, ∃ y : E,
      (∃ x : E, y ≠ 0 ∧ C' = halfLine x y) ∨ ∀ x z : E, z ≠ 0 → C' ≠ halfLine x z := by
    intro C'
    by_cases h : ∃ x z : E, z ≠ 0 ∧ C' = halfLine x z
    · obtain ⟨x, z, hz, he⟩ := h
      exact ⟨z, Or.inl ⟨x, hz, he⟩⟩
    · exact ⟨0, Or.inr fun x z hz he => h ⟨x, z, hz, he⟩⟩
  choose g hg using hchoice
  refine ⟨g '' {C' : Set E | IsFace C C'} ∩ extremeDirections C,
    (hfin.image g).subset Set.inter_subset_left, Set.inter_subset_right, ?_⟩
  rintro y ⟨hy, x, hface⟩
  rcases hg (halfLine x y) with ⟨x', hg0, hx'⟩ | hno
  · have hgmem : g (halfLine x y) ∈
        g '' {C' : Set E | IsFace C C'} ∩ extremeDirections C := by
      refine ⟨⟨halfLine x y, hface, rfl⟩, hg0, x', ?_⟩
      rw [← hx']
      exact hface
    have hrec : y ∈ recessionCone (halfLine x' (g (halfLine x y))) := by
      rw [← hx']
      exact mem_recessionCone_halfLine x y
    rw [recessionCone_halfLine] at hrec
    obtain ⟨a, ha, hya⟩ := hrec
    have hone : y ∈ (PointedCone.hull ℝ ({g (halfLine x y)} : Set E) : Set E) := by
      rw [coe_coneHull_singleton]
      exact ⟨a, ha, hya⟩
    exact Submodule.span_mono (Set.singleton_subset_iff.2 hgmem) hone
  · exact absurd rfl (hno x y hy)

end Counting

/-! ### The faces of a finitely generated set -/

section Generated

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C C' : Set E}

/-- **A face of a finitely generated set is finitely generated.** By Theorem 18.3
(`IsFace.eq_convexHullPD`) the face is the hull of the generating points it contains and the
generating directions in which it recedes, and both of those are described by a `Finset.filter`
of the original generators. -/
theorem FinitelyGenerated.of_isFace (hC : FinitelyGenerated C) (hface : IsFace C C') :
    FinitelyGenerated C' := by
  classical
  obtain ⟨P, D, hPD⟩ := hC
  have hPD' : C = convexHullPD (P : Set E) (D : Set E) := hPD
  rw [hPD'] at hface
  refine ⟨P.filter (· ∈ C'), D.filter (· ∈ recessionCone C'), ?_⟩
  have hp : ((P.filter (· ∈ C') : Finset E) : Set E) = (P : Set E) ∩ C' := by
    ext z; simp
  have hd : ((D.filter (· ∈ recessionCone C') : Finset E) : Set E)
      = {y ∈ (D : Set E) | y ∈ recessionCone C'} := by
    ext z; simp
  rw [← convexHullPD_def, hp, hd]
  exact hface.eq_convexHullPD

/-- **A finitely generated set has only finitely many faces.** Theorem 18.3 makes the face map
factor through the pairs of subsets of the two generating sets. -/
theorem FinitelyGenerated.finite_setOf_isFace (hC : FinitelyGenerated C) :
    {C' : Set E | IsFace C C'}.Finite := by
  classical
  obtain ⟨P, D, hPD⟩ := hC
  have hPD' : C = convexHullPD (P : Set E) (D : Set E) := hPD
  refine Set.Finite.subset (Set.Finite.image
    (fun q : Finset E × Finset E => convexHullPD (q.1 : Set E) (q.2 : Set E))
    (P.powerset ×ˢ D.powerset).finite_toSet) ?_
  rintro C' hC'
  have hface : IsFace (convexHullPD (P : Set E) (D : Set E)) C' := hPD' ▸ hC'
  have hp : ((P.filter (· ∈ C') : Finset E) : Set E) = (P : Set E) ∩ C' := by
    ext z; simp
  have hd : ((D.filter (· ∈ recessionCone C') : Finset E) : Set E)
      = {y ∈ (D : Set E) | y ∈ recessionCone C'} := by
    ext z; simp
  refine ⟨(P.filter (· ∈ C'), D.filter (· ∈ recessionCone C')), ?_, ?_⟩
  · exact Finset.mem_coe.2 (Finset.mem_product.2
      ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _),
        Finset.mem_powerset.2 (Finset.filter_subset _ _)⟩)
  · change convexHullPD ((P.filter (· ∈ C') : Finset E) : Set E)
      ((D.filter (· ∈ recessionCone C') : Finset E) : Set E) = C'
    rw [hp, hd]
    exact hface.eq_convexHullPD.symm

/-- **A face of a polyhedral set is polyhedral.** -/
theorem Polyhedral.of_isFace (hC : Polyhedral C) (hface : IsFace C C') : Polyhedral C' :=
  (hC.finitelyGenerated.of_isFace hface).polyhedral

/-- **A polyhedral set has only finitely many faces.** -/
theorem Polyhedral.finite_setOf_isFace (hC : Polyhedral C) :
    {C' : Set E | IsFace C C'}.Finite :=
  hC.finitelyGenerated.finite_setOf_isFace

end Generated

/-! ### Finitely many faces forces finite generation -/

section FiniteFaces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E}

/-- **A closed convex set containing no lines and having only finitely many faces is finitely
generated.**

The set is the hull of its extreme points and extreme directions
(`convexHullPD_extremePoints_extremeDirections`); a finite face set makes the extreme points
finite and the extreme rays finitely many, and replacing the extreme directions by a finite set
of generators for them does not change the hull. -/
theorem finitelyGenerated_of_finite_setOf_isFace_of_containsNoLine (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C)
    (hfin : {C' : Set E | IsFace C C'}.Finite) : FinitelyGenerated C := by
  classical
  obtain ⟨D, hDfin, hDsub, hDcov⟩ := exists_finite_generating_extremeDirections hfin
  have hPfin := finite_extremePoints_of_finite_setOf_isFace hfin
  have hrepr := convexHullPD_extremePoints_extremeDirections hC hCcl hnl
  refine ⟨hPfin.toFinset, hDfin.toFinset, ?_⟩
  rw [hPfin.coe_toFinset, hDfin.coe_toFinset, ← convexHullPD_def]
  refine Set.Subset.antisymm (Set.Subset.trans hrepr.ge ?_)
    (Set.Subset.trans (convexHullPD_mono_right _ hDsub) hrepr.subset)
  exact Set.Subset.trans (convexHullPD_mono_right _ hDcov)
    (convexHullPD_coneHull _ _).subset

/-- **A closed convex set with only finitely many faces is polyhedral.**

Rockafellar's reduction to lineality zero: with `N` the lineality space of `C` and `M` any
complement of it, `C = N + (C ∩ M)`, the faces of `C ∩ M` correspond to the faces of `C`
(`isFaceEquivInter`), and `C ∩ M` contains no lines because a line inside it would have its
direction in `N ⊓ M = ⊥`. So `C ∩ M` is finitely generated, and `C` is a sum of two polyhedral
sets. -/
theorem polyhedral_of_finite_setOf_isFace (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hfin : {C' : Set E | IsFace C C'}.Finite) : Polyhedral C := by
  classical
  obtain ⟨M, hcompl⟩ := (linealitySubmodule C).exists_isCompl
  have hN : ((linealitySubmodule C : Submodule ℝ E) : Set E) ⊆ linealitySpace C :=
    (coe_linealitySubmodule C).subset
  have hdec : C = ((linealitySubmodule C : Submodule ℝ E) : Set E) + (C ∩ (M : Set E)) :=
    eq_add_inter_of_isCompl_of_le hN hcompl
  have hC₀nl : ContainsNoLine (C ∩ (M : Set E)) := by
    intro x y hy
    by_contra hall
    push Not at hall
    have hyL : y ∈ linealitySpace C :=
      mem_linealitySpace_of_forall_add_smul_mem hC hCcl fun t => (hall t).1
    have h0 : x + (0 : ℝ) • y ∈ M := (hall 0).2
    have h1 : x + (1 : ℝ) • y ∈ M := (hall 1).2
    have hsub : (x + (1 : ℝ) • y) - (x + (0 : ℝ) • y) ∈ M := M.sub_mem h1 h0
    have heq : (x + (1 : ℝ) • y) - (x + (0 : ℝ) • y) = y := by module
    rw [heq] at hsub
    exact hy ((Submodule.disjoint_def.1 hcompl.disjoint) y
      (mem_linealitySubmodule.2 hyL) hsub)
  have hfin₀ : {C₀ : Set E | IsFace (C ∩ (M : Set E)) C₀}.Finite := by
    have h1 : Finite {C' : Set E // IsFace C C'} := hfin.to_subtype
    have h2 : Finite {C₀ : Set E // IsFace (C ∩ (M : Set E)) C₀} :=
      Finite.of_equiv _ (isFaceEquivInter hN hcompl)
    have h3 : Finite ↥{C₀ : Set E | IsFace (C ∩ (M : Set E)) C₀} := h2
    exact Set.toFinite _
  have hC₀ : FinitelyGenerated (C ∩ (M : Set E)) :=
    finitelyGenerated_of_finite_setOf_isFace_of_containsNoLine (hC.inter M.convex)
      (hCcl.inter M.closed_of_finiteDimensional) hC₀nl hfin₀
  have hsum : Polyhedral (((linealitySubmodule C : Submodule ℝ E) : Set E)
      + (C ∩ (M : Set E))) :=
    (polyhedral_coe_submodule _).add hC₀.polyhedral
  rwa [← hdec] at hsum

/-- **A closed convex set with only finitely many faces is finitely generated.** -/
theorem finitelyGenerated_of_finite_setOf_isFace (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hfin : {C' : Set E | IsFace C C'}.Finite) : FinitelyGenerated C :=
  (polyhedral_of_finite_setOf_isFace hC hCcl hfin).finitelyGenerated

/-- **A convex set is polyhedral exactly when it is closed and has only finitely many faces.**
Together with `polyhedral_iff_finitelyGenerated` this is the full three-way characterisation. -/
theorem polyhedral_iff_isClosed_finite_setOf_isFace (hC : Convex ℝ C) :
    Polyhedral C ↔ IsClosed C ∧ {C' : Set E | IsFace C C'}.Finite :=
  ⟨fun h => ⟨h.isClosed, h.finite_setOf_isFace⟩,
    fun h => polyhedral_of_finite_setOf_isFace hC h.1 h.2⟩

/-- **A convex set is finitely generated exactly when it is closed and has only finitely many
faces.** -/
theorem finitelyGenerated_iff_isClosed_finite_setOf_isFace (hC : Convex ℝ C) :
    FinitelyGenerated C ↔ IsClosed C ∧ {C' : Set E | IsFace C C'}.Finite := by
  rw [← polyhedral_iff_finitelyGenerated]
  exact polyhedral_iff_isClosed_finite_setOf_isFace hC

end FiniteFaces

end Tdaf.ConvexAnalysis
