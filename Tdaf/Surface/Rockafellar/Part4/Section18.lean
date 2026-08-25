/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Exposed
import Tdaf.Analysis.Convex.Face
import Tdaf.Analysis.Convex.Representation
import Tdaf.Analysis.Convex.Tangent
import Tdaf.Surface.Rockafellar.Part2.Section06

/-!
# Rockafellar, §18: Extreme Points and Faces of Convex Sets

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §18, pp. 162–169: the facial structure of
a convex set, the internal representations `C = conv S` and `C = cl (conv S)` that it produces,
and the external representation dual to the second. All sixteen numbered results are here, stated
over `Rn n = ℝⁿ` in the book's own vocabulary and closed by specialising the backbone.

## Contents

| label | declaration |
|---|---|
| Theorem 18.1 | `theorem_18_1` |
| Corollary 18.1.1 | `corollary_18_1_1`, `corollary_18_1_1_isClosed` |
| Corollary 18.1.2 | `corollary_18_1_2` |
| Corollary 18.1.3 | `corollary_18_1_3`, `corollary_18_1_3_dim` |
| Theorem 18.2 | `theorem_18_2_union`, `theorem_18_2_disjoint`, `theorem_18_2_subset`, |
| | `theorem_18_2_maximal` |
| Theorem 18.3 | `theorem_18_3` |
| Corollary 18.3.1 | `corollary_18_3_1_points`, `corollary_18_3_1_directions`, |
| | `corollary_18_3_1_directions_of_isBounded` |
| Theorem 18.4 | `theorem_18_4` |
| Theorem 18.5 | `theorem_18_5`, `theorem_18_5_lineality` |
| Corollary 18.5.1 | `corollary_18_5_1` |
| Corollary 18.5.2 | `corollary_18_5_2` |
| Corollary 18.5.3 | `corollary_18_5_3` |
| Theorem 18.6 | `theorem_18_6`, `theorem_18_6_closure` |
| Theorem 18.7 | `theorem_18_7` |
| Corollary 18.7.1 | `corollary_18_7_1` |
| Theorem 18.8 | `theorem_18_8` |

## The section's definitions

* **Face** is the backbone's `Tdaf.ConvexAnalysis.IsFace`, which is Rockafellar's definition
  verbatim; `isFace_iff` spells it out in the book's segment wording.
* **Extreme point** is Mathlib's `Set.extremePoints ℝ`, the zero-dimensional faces
  (`isFace_singleton_iff`); `mem_extremePoints_iff` is the book's `(1 - λ) y + λ z` wording.
* **Extreme direction** is the backbone's `IsExtremeDirection`: a non-zero `y` such that some
  closed half-line in the direction of `y` is a face. Representing a direction by a generating
  vector avoids a quotient, at the cost of `extremeDirections C` being closed under positive
  scaling.
* `Rockafellar.IsExtremeRay`, `Rockafellar.IsExposedRay` — an extreme (exposed) *ray* of a convex
  cone is a face (an exposed face) which is a half-line **emanating from the origin**.
  `isExtremeRay_iff_isExtremeDirection` and `isExposedRay_iff_isExposedDirection` are the bridges,
  and they are the book's "the extreme rays of a convex cone are in one-to-one correspondence with
  the extreme directions of the cone", proved rather than asserted: the key step
  `eq_zero_of_isExtreme_halfLine` says that a half-line face of a cone must start at the origin.
* **Exposed face** is Mathlib's `IsExposed ℝ`; `isExposed_iff_exists_vector` is the book's "the
  set of points where a linear function `⟨·, b⟩` achieves its maximum over `C`".
* **Exposed point** is Mathlib's `Set.exposedPoints ℝ`; `mem_exposedPoints_iff` is the book's "a
  point through which there is a supporting hyperplane containing no other point of `C`".
* **Exposed direction** is the backbone's `IsExposedDirection`, the exposed analogue of
  `IsExtremeDirection`. The book leaves it informal; the backbone had to make it precise.
* `Rockafellar.IsTangentHyperplaneAt` — the book's *tangent hyperplane*, `{z | ⟨z, b⟩ = ⟨x, b⟩}`
  being the unique supporting hyperplane to `C` at `x`. It is the backbone's `IsTangentAt` read
  through `linFn`, and is the vector-versus-functional translation only.
* `faces_isGLB`, `faces_isLUB` — `F(C)` is a complete lattice under inclusion.

**`conv S` for `S` a set of points and directions** is the backbone's `convexHullPD P D`, with `P`
the points and `D` the generating vectors of the directions. That idiom is §17's, and §17 may
introduce a surface spelling of it; nothing here depends on which spelling wins, because every
statement below names `convexHullPD` directly.

## What is not here

* **The torus example** (p. 163), the disk-plus-segment example (p. 167), and the parabolic set of
  p. 163 — *omitted*. They are the counterexamples showing that a face need not be exposed, that
  the extreme points of a compact convex set need not form a closed set, and that `0⁺C` can have
  extreme directions where `C` has none. Each needs coordinate machinery for no downstream return;
  the mathematical content they guard is already recorded in the backbone docstrings (the closure
  in Theorem 18.7 cannot be dropped, and Theorem 18.6 is stated with a closure for this reason).
* **"Every extreme direction of `C` is an extreme direction of `0⁺C`"** and its exposed analogue
  (p. 163) — *omitted*, and recorded as a backbone gap. What the backbone has is
  `extremeDirections_subset_recessionCone`, the weaker statement that an extreme direction is a
  direction of recession; the sharpening to an extreme direction *of the recession cone* is the
  book's `C' ⊆ x + 0⁺C ⊆ C` argument and has no backbone counterpart.
* **"Any strictly decreasing sequence of faces must be finite in length"** (p. 164) — *omitted*.
  It is an immediate consequence of `corollary_18_1_3_dim`, stated in the book as a remark on the
  lattice `F(C)` and used nowhere.
* **The bijection between the faces of `C` and the faces of `C ∩ L^⊥`** (p. 166) — *omitted*. Only
  the representation half of that remark is here, as `theorem_18_5_lineality`.
* **The minimality remark after Corollary 18.5.3** (p. 167) — *omitted*: it is
  `corollary_18_3_1_points` and `corollary_18_3_1_directions` restated for the `S` of Theorem
  18.5, with no new content.
* **The forward reference to Corollary 25.1.3** (p. 168) — *deferred by scope*, to §25.

## Where the book's hypotheses had to change

* **Theorem 18.3 does not need the face to be non-empty.** The backbone's proof does not use it,
  and the empty face satisfies the conclusion.
* **Corollaries 18.5.2 and 18.7.1 do not need "more than just the origin".** For `K = {0}` there
  are no extreme (or exposed) directions at all, the hypothesis on `T` is vacuous, and both sides
  of the conclusion are `{0}`. This is recorded in the backbone docstrings.
* **Corollary 18.7.1 is printed in the book with no `Proof.` paragraph.** The argument it wants is
  the one Rockafellar gives for Corollary 18.5.2, one layer up: `K` is the closure of `conv S` for
  `S` the origin together with the exposed directions (Theorem 18.7), the origin is the only
  exposed point of `K` because it is the only extreme point of a line-free cone, and a hull of the
  origin and a set of directions is the cone generated by those directions. That is exactly how
  `closure_coneHull_exposedDirections` is proved in the backbone, so the missing paragraph is
  supplied here by citation rather than left as a gap.
* **Theorem 18.5's "obvious extension to closed convex sets of arbitrary lineality"** (p. 166) is
  never stated or proved in the book. It *is* cheap over the backbone and is here as
  `theorem_18_5_lineality`: `eq_add_inter_of_isCompl` gives `C = L + (C ∩ L^⊥)` for `L` the
  lineality space, `C ∩ L^⊥` is closed, convex and line-free, and Theorem 18.5 applies to it.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §18.
-/

open Set

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface
open scoped Pointwise

variable {n : ℕ} {C C' C₁ C₂ D : Set (Rn n)}

/-! ### Faces (p. 162) -/

/-- **Rockafellar, §18 (p. 162).** A **face** of a convex set `C` is a convex subset `C'` of `C`
such that every closed line segment in `C` with a relative interior point in `C'` has both
endpoints in `C'`.

This is the backbone's `IsFace` unfolded; the segment condition is Mathlib's `IsExtreme ℝ C C'`,
and convexity of `C'` is a genuine extra requirement (`{0, 1}` is an extreme subset of `[0, 1]`
but not a face of it). -/
theorem isFace_iff : IsFace C C' ↔ Convex ℝ C' ∧ C' ⊆ C ∧
    ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C', z ∈ openSegment ℝ x y → x ∈ C' ∧ y ∈ C' :=
  ⟨fun h => ⟨h.convex, h.subset, fun _ hx _ hy _ hz hseg =>
      ⟨h.toIsExtreme.left_mem_of_mem_openSegment hx hy hz hseg,
        h.toIsExtreme.right_mem_of_mem_openSegment hx hy hz hseg⟩⟩,
    fun h => ⟨⟨h.2.1, fun _ hx _ hy _ hz hseg => (h.2.2 _ hx _ hy _ hz hseg).1⟩, h.1⟩⟩

/-- **Rockafellar, §18 (p. 162).** `C` itself is a face of `C`. -/
theorem isFace_self (hC : Convex ℝ C) : IsFace C C := Convex.isFace_self hC

/-- **Rockafellar, §18 (p. 162).** The empty set is a face of every convex set. -/
theorem isFace_empty : IsFace C (∅ : Set (Rn n)) := IsFace.empty

/-- **Rockafellar, §18 (p. 163).** A face of a face is a face. "This is immediate from the
definition of `face`." -/
theorem isFace_trans (h₁ : IsFace C C') (h₂ : IsFace C' C₁) : IsFace C C₁ := h₁.trans h₂

/-- **Rockafellar, §18 (p. 163).** If `C'` is a face of `C` and `D` is a convex set with
`C' ⊆ D ⊆ C`, then `C'` is a fortiori a face of `D`. -/
theorem isFace_mono (h : IsFace C C') (hDC : D ⊆ C) (hC'D : C' ⊆ D) : IsFace D C' :=
  h.mono hDC hC'D

/-- **Rockafellar, §18 (p. 162).** The **extreme points** of `C` are its zero-dimensional faces:
`x ∈ C` is extreme exactly when `{x}` is a face of `C`. -/
theorem isFace_singleton_iff {x : Rn n} : IsFace C {x} ↔ x ∈ C.extremePoints ℝ :=
  isFace_singleton

/-- **Rockafellar, §18 (p. 162)**, the book's wording: `x ∈ C` is an extreme point of `C` if and
only if there is no way to express `x` as a convex combination `(1 - λ) y + λ z` with `y ∈ C`,
`z ∈ C` and `0 < λ < 1`, except by taking `y = z = x`. -/
theorem mem_extremePoints_iff {x : Rn n} :
    x ∈ C.extremePoints ℝ ↔ x ∈ C ∧ ∀ y ∈ C, ∀ z ∈ C, ∀ l : ℝ, 0 < l → l < 1 →
      x = (1 - l) • y + l • z → y = x ∧ z = x := by
  rw [mem_extremePoints]
  refine and_congr_right fun _ => ⟨fun h y hy z hz l hl0 hl1 heq => ?_, fun h y hy z hz hseg => ?_⟩
  · exact h y hy z hz ⟨1 - l, l, by linarith, hl0, by ring, heq.symm⟩
  · obtain ⟨a, b, ha, hb, hab, hval⟩ := hseg
    exact h y hy z hz b hb (by linarith) (by rw [← hval, show (1 : ℝ) - b = a by linarith])

/-! ### The lattice of faces (p. 164) -/

/-- **Rockafellar, §18 (p. 164).** The intersection of an arbitrary non-empty set of faces of `C`
is again a face, so every set of elements of `F(C)` has a greatest lower bound. -/
theorem faces_isGLB {F : Set (Set (Rn n))} (hF : F.Nonempty) (h : ∀ B ∈ F, IsFace C B) :
    IsFace C (⋂₀ F) ∧ IsGLB F (⋂₀ F) :=
  ⟨isFace_sInter hF h,
    ⟨fun _ hB => sInter_subset_of_mem hB, fun _ hB => subset_sInter fun _ hC' => hB hC'⟩⟩

/-- **Rockafellar, §18 (p. 164).** Every set of faces of `C` has a least upper bound in `F(C)`:
the intersection of all the faces containing them all. With `faces_isGLB`, `isFace_self` and
`isFace_empty`, this is the assertion that `F(C)` is a complete lattice under inclusion. -/
theorem faces_isLUB (hC : Convex ℝ C) (F : Set (Set (Rn n))) (h : ∀ B ∈ F, IsFace C B) :
    ∃ G, IsFace C G ∧ (∀ B ∈ F, B ⊆ G) ∧ ∀ G', IsFace C G' → (∀ B ∈ F, B ⊆ G') → G ⊆ G' :=
  ⟨⋂₀ {H | IsFace C H ∧ ∀ B ∈ F, B ⊆ H},
    isFace_sInter ⟨C, Convex.isFace_self hC, fun B hB => (h B hB).subset⟩ fun _ hH => hH.1,
    fun _ hB _ hx => mem_sInter.2 fun _ hH => hH.2 _ hB hx,
    fun _ hG' hsub => sInter_subset_of_mem ⟨hG', hsub⟩⟩

/-! ### Theorem 18.1 and its corollaries -/

/-- **Rockafellar, Theorem 18.1.** Let `C` be a convex set and `C'` a face of `C`. If `D` is a
convex set in `C` such that `ri D` meets `C'`, then `D ⊆ C'`.

Specialises `IsFace.subset_of_relint_inter_nonempty`. The backbone does not need `Convex ℝ D`:
its proof uses only the prolongation lemma of §6, which says nothing about `D` beyond `ri D`. -/
theorem theorem_18_1 (hface : IsFace C C') (hDC : D ⊆ C) (h : (ri D ∩ C').Nonempty) : D ⊆ C' :=
  hface.subset_of_relint_inter_nonempty hDC h

/-- **Rockafellar, Corollary 18.1.1.** If `C'` is a face of a convex set `C`, then
`C' = C ∩ cl C'`.

Specialises `IsFace.eq_inter_closure`. -/
theorem corollary_18_1_1 (hC : Convex ℝ C) (hface : IsFace C C') : C' = C ∩ closure C' :=
  hface.eq_inter_closure hC

/-- **Rockafellar, Corollary 18.1.1**, second sentence: a face of a closed convex set is closed.

Specialises `IsFace.isClosed`. -/
theorem corollary_18_1_1_isClosed (hC : Convex ℝ C) (hCcl : IsClosed C) (hface : IsFace C C') :
    IsClosed C' :=
  hface.isClosed hC hCcl

/-- **Rockafellar, Corollary 18.1.2.** If `C'` and `C''` are faces of a convex set `C` such that
`ri C'` and `ri C''` have a point in common, then `C' = C''`.

Specialises `IsFace.eq_of_relint_inter_nonempty`. -/
theorem corollary_18_1_2 (h₁ : IsFace C C₁) (h₂ : IsFace C C₂) (h : (ri C₁ ∩ ri C₂).Nonempty) :
    C₁ = C₂ :=
  h₁.eq_of_relint_inter_nonempty h₂ h

/-- **Rockafellar, Corollary 18.1.3.** A face of `C` other than `C` itself is entirely contained
in the relative boundary of `C`.

Specialises `IsFace.subset_intrinsicFrontier` through §6's `relbd_eq_intrinsicFrontier`. -/
theorem corollary_18_1_3 (hface : IsFace C C') (hne : C' ≠ C) : C' ⊆ relbd C := by
  rw [relbd_eq_intrinsicFrontier]
  exact hface.subset_intrinsicFrontier hne

/-- **Rockafellar, Corollary 18.1.3**, the dimension statement: a non-empty face of `C` other than
`C` itself has `dim C' < dim C`. The book deduces it from Corollary 6.3.3, and so does this
proof. -/
theorem corollary_18_1_3_dim (hC : Convex ℝ C) (hface : IsFace C C') (hne' : C'.Nonempty)
    (hne : C' ≠ C) : dim C' < dim C :=
  corollary_6_3_3 hface.convex hC (hne'.mono hface.subset) (corollary_18_1_3 hface hne)

/-! ### Theorem 18.2: the relative interiors of the faces partition `C` -/

/-- **Rockafellar, Theorem 18.2**, the union half: the relative interiors of the non-empty faces
of `C` cover `C`.

Specialises `eq_iUnion_relint_isFace`. (`ri ∅ = ∅`, so the empty face contributes nothing and the
union may as well be taken over all faces.) -/
theorem theorem_18_2_union (hC : Convex ℝ C) : C = ⋃ C' ∈ {B : Set (Rn n) | IsFace C B}, ri C' :=
  eq_iUnion_relint_isFace hC

/-- **Rockafellar, Theorem 18.2**, the disjointness half: the relative interiors of distinct faces
of `C` are disjoint. With `theorem_18_2_union` this is the assertion that they partition `C`.

Specialises `IsFace.relint_pairwise_disjoint`. -/
theorem theorem_18_2_disjoint (h₁ : IsFace C C₁) (h₂ : IsFace C C₂) (hne : C₁ ≠ C₂) :
    Disjoint (ri C₁) (ri C₂) :=
  h₁.relint_pairwise_disjoint h₂ hne

/-- **Rockafellar, Theorem 18.2**, the containment half: every non-empty relatively open convex
subset of `C` is contained in the relative interior of some face of `C`.

Specialises `exists_isFace_subset_relint`; `IsRelativelyOpen` is §6's `ri D = D`. -/
theorem theorem_18_2_subset (hC : Convex ℝ C) (hD : Convex ℝ D) (hDC : D ⊆ C) (hne : D.Nonempty)
    (hopen : IsRelativelyOpen D) : ∃ C', IsFace C C' ∧ D ⊆ ri C' :=
  exists_isFace_subset_relint hC hD hDC hne hopen

/-- **Rockafellar, Theorem 18.2**, the maximality half: the relative interiors of the non-empty
faces of `C` are the *maximal* relatively open convex subsets of `C`.

Specialises `IsFace.relint_maximal`. -/
theorem theorem_18_2_maximal (hC : Convex ℝ C) (hface : IsFace C C') (hne' : C'.Nonempty)
    (hD : Convex ℝ D) (hopen : IsRelativelyOpen D) (hsub : ri C' ⊆ D) (hDC : D ⊆ C) :
    D = ri C' :=
  hface.relint_maximal hC hne' hD hopen hsub hDC

/-! ### Theorem 18.3: the faces of a hull of points and directions -/

/-- **Rockafellar, Theorem 18.3.** Let `C = conv S`, where `S` is a set of points and directions,
and let `C'` be a face of `C`. Then `C' = conv S'`, where `S'` consists of the points in `S` which
belong to `C'` and the directions in `S` which are directions of recession of `C'`.

`conv S` is the backbone's `convexHullPD P D`, with `P` the points of `S` and `D` a set of vectors
generating its directions. Specialises `IsFace.eq_convexHullPD`, which does not need the book's
hypothesis that `C'` be non-empty. -/
theorem theorem_18_3 {P D : Set (Rn n)} (hface : IsFace (convexHullPD P D) C') :
    C' = convexHullPD (P ∩ C') {y ∈ D | y ∈ recessionCone C'} :=
  hface.eq_convexHullPD

/-- **Rockafellar, Corollary 18.3.1**, first half: if `C = conv S` for a set `S` of points and
directions, every extreme point of `C` is a point of `S`.

Specialises `extremePoints_convexHullPD_subset`. -/
theorem corollary_18_3_1_points (P D : Set (Rn n)) :
    (convexHullPD P D).extremePoints ℝ ⊆ P :=
  extremePoints_convexHullPD_subset P D

/-- **Rockafellar, Corollary 18.3.1**, second half: if no half-line contains an unbounded set of
points of `S`, then every extreme direction of `C = conv S` is a direction in `S`.

Specialises `exists_mem_eq_smul_of_mem_extremeDirections`. A direction is recorded by a generating
vector, so "is a direction in `S`" reads "is a positive multiple of a vector of `S`". -/
theorem corollary_18_3_1_directions (P D : Set (Rn n))
    (hP : ∀ x z : Rn n, Bornology.IsBounded (P ∩ halfLine x z)) {y : Rn n}
    (hy : y ∈ extremeDirections (convexHullPD P D)) : ∃ z ∈ D, ∃ a : ℝ, 0 < a ∧ y = a • z :=
  exists_mem_eq_smul_of_mem_extremeDirections P D hP hy

/-- **Rockafellar, Corollary 18.3.1**, second half in the special case the book highlights: it is
enough that the set of all points of `S` be bounded.

Specialises `exists_mem_eq_smul_of_mem_extremeDirections_of_isBounded`. -/
theorem corollary_18_3_1_directions_of_isBounded (P D : Set (Rn n))
    (hP : Bornology.IsBounded P) {y : Rn n}
    (hy : y ∈ extremeDirections (convexHullPD P D)) : ∃ z ∈ D, ∃ a : ℝ, 0 < a ∧ y = a • z :=
  exists_mem_eq_smul_of_mem_extremeDirections_of_isBounded P D hP hy

/-! ### Theorem 18.4: a closed convex set is the hull of its relative boundary -/

/-- **Rockafellar, Theorem 18.4.** Let `C` be a closed convex set which is not an affine set or a
closed half of an affine set. Then each relative interior point of `C` lies on some line segment
joining two relative boundary points of `C`.

Specialises `exists_notMem_relint_mem_segment_of_not_isAffineHalf`. The book's two exceptional
cases are the backbone's single predicate `IsAffineHalf`: allowing the functional to be `0` makes
"affine set" the degenerate case of "closed half of an affine set". -/
theorem theorem_18_4 (hC : Convex ℝ C) (hCcl : IsClosed C) (hhalf : ¬ IsAffineHalf C) {x : Rn n}
    (hx : x ∈ ri C) : ∃ a ∈ relbd C, ∃ b ∈ relbd C, x ∈ segment ℝ a b := by
  obtain ⟨a, haC, b, hbC, hari, hbri, hseg⟩ :=
    exists_notMem_relint_mem_segment_of_not_isAffineHalf hC hCcl hhalf hx
  exact ⟨a, ⟨subset_closure haC, hari⟩, b, ⟨subset_closure hbC, hbri⟩, hseg⟩

/-! ### Theorem 18.5: the fundamental internal representation -/

/-- **Rockafellar, Theorem 18.5.** Let `C` be a closed convex set containing no lines, and let `S`
be the set of all extreme points and extreme directions of `C`. Then `C = conv S`.

Specialises `convexHullPD_extremePoints_extremeDirections`. -/
theorem theorem_18_5 (hC : Convex ℝ C) (hCcl : IsClosed C) (hnl : ContainsNoLine C) :
    convexHullPD (C.extremePoints ℝ) (extremeDirections C) = C :=
  convexHullPD_extremePoints_extremeDirections hC hCcl hnl

/-- **Rockafellar, Theorem 18.5** for a closed convex set of arbitrary lineality — the "obvious
extension" of p. 166, which the book states in words and never proves.

Let `L` be the lineality space of `C` and `C₀ = C ∩ L^⊥`. Then `C = L + conv S₀`, where `S₀` is
the set of extreme points and extreme directions of `C₀`.

The proof is the book's: `eq_add_inter_of_isCompl` is `C = L + C₀` (the remark of p. 166, with
`L^⊥` as the complement), `C₀` is closed and convex, and `C₀` contains no lines because the
direction of a line in `C₀` lies in `L` — the line lies in `C` — and in `L^⊥`. Theorem 18.5 then
applies to `C₀`. -/
theorem theorem_18_5_lineality (hC : Convex ℝ C) (hCcl : IsClosed C) :
    C = (linealitySubmodule C : Set (Rn n)) +
      convexHullPD ((C ∩ ((linealitySubmodule C)ᗮ : Set (Rn n))).extremePoints ℝ)
        (extremeDirections (C ∩ ((linealitySubmodule C)ᗮ : Set (Rn n)))) := by
  set L : Submodule ℝ (Rn n) := linealitySubmodule C with hL
  set C₀ : Set (Rn n) := C ∩ ((Lᗮ : Submodule ℝ (Rn n)) : Set (Rn n)) with hC₀
  have hcompl : IsCompl L Lᗮ := Submodule.isCompl_orthogonal L
  have hC₀conv : Convex ℝ C₀ := hC.inter (Lᗮ : Submodule ℝ (Rn n)).convex
  have hC₀cl : IsClosed C₀ :=
    hCcl.inter (Lᗮ : Submodule ℝ (Rn n)).closed_of_finiteDimensional
  have hC₀nl : ContainsNoLine C₀ := by
    intro x y hy
    by_contra hall
    push Not at hall
    have hyL : y ∈ L := by
      rw [hL, mem_linealitySubmodule]
      exact mem_linealitySpace_of_forall_add_smul_mem hC hCcl fun t => (hall t).1
    have hxL : x ∈ (Lᗮ : Submodule ℝ (Rn n)) := by
      have h0 := (hall 0).2
      simpa using h0
    have hx1L : x + (1 : ℝ) • y ∈ (Lᗮ : Submodule ℝ (Rn n)) := (hall 1).2
    have hyL' : y ∈ (Lᗮ : Submodule ℝ (Rn n)) := by
      have hsub := (Lᗮ : Submodule ℝ (Rn n)).sub_mem hx1L hxL
      simpa using hsub
    have hbot : y ∈ L ⊓ Lᗮ := Submodule.mem_inf.2 ⟨hyL, hyL'⟩
    rw [hcompl.inf_eq_bot] at hbot
    exact hy (Submodule.mem_bot ℝ |>.1 hbot)
  rw [theorem_18_5 hC₀conv hC₀cl hC₀nl]
  exact eq_add_inter_of_isCompl hcompl

/-- **Rockafellar, Corollary 18.5.1** (Minkowski's theorem). A closed bounded convex set is the
convex hull of its extreme points.

Specialises `convexHull_extremePoints`. -/
theorem corollary_18_5_1 (hC : Convex ℝ C) (hCcl : IsClosed C) (hbdd : Bornology.IsBounded C) :
    convexHull ℝ (C.extremePoints ℝ) = C :=
  convexHull_extremePoints (Metric.isCompact_of_isClosed_isBounded hCcl hbdd) hC

/-- **Rockafellar, Corollary 18.5.3.** A non-empty closed convex set containing no lines has at
least one extreme point.

Specialises `extremePoints_nonempty_of_containsNoLine`. -/
theorem corollary_18_5_3 (hC : Convex ℝ C) (hCcl : IsClosed C) (hnl : ContainsNoLine C)
    (hne : C.Nonempty) : (C.extremePoints ℝ).Nonempty :=
  extremePoints_nonempty_of_containsNoLine hC hCcl hnl hne

/-! ### Rays of a convex cone (p. 162)

For cones the useful zero-dimensional object is not an extreme point — the origin is the only
candidate — but an extreme *ray*: a face which is a half-line emanating from the origin. The book
asserts that these are "in one-to-one correspondence with the extreme directions of the cone";
`eq_zero_of_isExtreme_halfLine` is the half of that which is not immediate. -/

/-- **Rockafellar, §18 (p. 162).** An **extreme ray** of a convex cone `K` is a face of `K` which
is a half-line emanating from the origin, recorded by a generating vector. -/
def IsExtremeRay (K : Set (Rn n)) (y : Rn n) : Prop := y ≠ 0 ∧ IsFace K (halfLine 0 y)

/-- **Rockafellar, §18 (p. 162).** An **exposed ray** of a convex cone `K` is an exposed face of
`K` which is a half-line emanating from the origin. -/
def IsExposedRay (K : Set (Rn n)) (y : Rn n) : Prop := y ≠ 0 ∧ IsExposed ℝ K (halfLine 0 y)

/-- **A half-line extreme subset of a cone starts at the origin.** This is the content of the
book's "the extreme rays of a convex cone are in one-to-one correspondence with the extreme
directions of the cone", which the book asserts without argument.

Both endpoints of `openSegment 0 (2 • x)` lie in the half-line because its midpoint `x` does, so
`0` and `2 • x` are both of the form `x + a • y` with `a ≥ 0`; writing `x = a • y = -(b • y)` with
`a, b ≥ 0` and `y ≠ 0` forces `a = b = 0`. -/
theorem eq_zero_of_isExtreme_halfLine {K : Set (Rn n)} (hne : K.Nonempty)
    (hcone : ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K) {x y : Rn n} (hy : y ≠ 0)
    (h : IsExtreme ℝ K (halfLine x y)) : x = 0 := by
  have h0 : (0 : Rn n) ∈ K := zero_mem_of_forall_smul_mem hne hcone
  have hxC' : x ∈ halfLine x y := left_mem_halfLine x y
  have h2x : (2 : ℝ) • x ∈ K := hcone x (h.subset hxC') 2 (by norm_num)
  have hopen : x ∈ openSegment ℝ (0 : Rn n) ((2 : ℝ) • x) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  obtain ⟨b, hb, hbeq⟩ :=
    mem_halfLine.1 (h.left_mem_of_mem_openSegment h0 h2x hxC' hopen)
  obtain ⟨a, ha, haeq⟩ :=
    mem_halfLine.1 (h.right_mem_of_mem_openSegment h0 h2x hxC' hopen)
  have hxa : x = a • y := by
    have hstep : x + x = x + a • y := by rw [← haeq]; module
    exact add_left_cancel hstep
  have hsum : (a + b) • y = 0 := by
    rw [add_smul, ← hxa]
    exact hbeq.symm
  have hab : a + b = 0 := by
    rcases smul_eq_zero.1 hsum with hab | hy0
    · exact hab
    · exact absurd hy0 hy
  have ha0 : a = 0 := by linarith
  rw [hxa, ha0, zero_smul]

/-- **Rockafellar, §18 (p. 162).** For a convex cone, the extreme rays and the extreme directions
are the same data. -/
theorem isExtremeRay_iff_isExtremeDirection {K : Set (Rn n)} (hne : K.Nonempty)
    (hcone : ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K) {y : Rn n} :
    IsExtremeRay K y ↔ IsExtremeDirection K y := by
  refine ⟨fun h => ⟨h.1, 0, h.2⟩, fun h => ⟨h.1, ?_⟩⟩
  obtain ⟨x, hface⟩ := h.2
  rwa [eq_zero_of_isExtreme_halfLine hne hcone h.1 hface.toIsExtreme] at hface

/-- **Rockafellar, §18 (p. 162).** For a convex cone, the exposed rays and the exposed directions
are the same data. -/
theorem isExposedRay_iff_isExposedDirection {K : Set (Rn n)} (hne : K.Nonempty)
    (hcone : ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K) {y : Rn n} :
    IsExposedRay K y ↔ IsExposedDirection K y := by
  refine ⟨fun h => ⟨h.1, 0, h.2⟩, fun h => ⟨h.1, ?_⟩⟩
  obtain ⟨x, hexp⟩ := h.2
  rwa [eq_zero_of_isExtreme_halfLine hne hcone h.1 hexp.isExtreme] at hexp

/-- A non-empty closed cone in Rockafellar's sense — closed under *positive* scalar multiplication
— is closed under non-negative scalar multiplication, which is the form the backbone's cone
theorems take. The origin is the limit of `a • x` as `a` decreases to `0`. -/
theorem forall_smul_mem_of_isCone {K : Set (Rn n)} (hK : IsCone K) (hKcl : IsClosed K) :
    ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K := by
  intro x hx a ha
  rcases ha.lt_or_eq with hpos | h0
  · exact hK a hpos x hx
  · have hlim : Filter.Tendsto (fun t : ℝ => t • x) (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((0 : ℝ) • x)) :=
      ((continuous_id.smul continuous_const).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hmem : (0 : Rn n) ∈ K := by
      have h := hKcl.mem_of_tendsto hlim
        (Filter.Eventually.mono self_mem_nhdsWithin fun t ht => hK t ht x hx)
      rwa [zero_smul] at h
    rw [← h0, zero_smul]
    exact hmem

/-- **Rockafellar, Corollary 18.5.2.** Let `K` be a closed convex cone containing no lines, and
let `T` be any set of vectors in `K` such that each extreme ray of `K` is generated by some
`x ∈ T`. Then `K` is the convex cone generated by `T`.

Specialises `coneHull_of_forall_extremeDirection` through `isExtremeRay_iff_isExtremeDirection`.
The book's "containing more than just the origin" is unnecessary: the zero cone has no extreme
rays, so the hypothesis on `T` is vacuous and both sides are `{0}`. -/
theorem corollary_18_5_2 {K T : Set (Rn n)} (hK : Convex ℝ K) (hKcl : IsClosed K)
    (hcone : IsCone K) (hne : K.Nonempty) (hnl : ContainsNoLine K) (hTK : T ⊆ K)
    (hgen : ∀ y, IsExtremeRay K y → ∃ x ∈ T, ∃ a : ℝ, 0 < a ∧ y = a • x) :
    (PointedCone.hull ℝ T : Set (Rn n)) = K := by
  have hsmul := forall_smul_mem_of_isCone hcone hKcl
  exact coneHull_of_forall_extremeDirection hK hKcl hne hsmul hnl hTK fun y hy =>
    hgen y ((isExtremeRay_iff_isExtremeDirection hne hsmul).2 hy)

/-! ### Theorem 18.6: Straszewicz's theorem -/

/-- **Rockafellar, Theorem 18.6** (Straszewicz's Theorem). For any closed convex set `C`, every
extreme point of `C` is the limit of some sequence of exposed points of `C`.

Specialises `extremePoints_subset_closure_exposedPoints`. -/
theorem theorem_18_6 (hC : Convex ℝ C) (hCcl : IsClosed C) :
    C.extremePoints ℝ ⊆ closure (C.exposedPoints ℝ) :=
  extremePoints_subset_closure_exposedPoints hC hCcl

/-- **Rockafellar, Theorem 18.6** in the book's own phrasing: the set of exposed points of a
closed convex set `C` is a dense subset of the set of extreme points of `C`.

Specialises `closure_exposedPoints_eq_closure_extremePoints`. -/
theorem theorem_18_6_closure (hC : Convex ℝ C) (hCcl : IsClosed C) :
    C.exposedPoints ℝ ⊆ C.extremePoints ℝ ∧
      closure (C.exposedPoints ℝ) = closure (C.extremePoints ℝ) :=
  ⟨exposedPoints_subset_extremePoints, closure_exposedPoints_eq_closure_extremePoints hC hCcl⟩

/-! ### Exposed faces and exposed points (p. 162) -/

/-- **Rockafellar, §18 (p. 162).** The **exposed faces** of `C` are the sets of points at which
some linear function `⟨·, b⟩` achieves its maximum over `C`; equivalently — aside from `C` itself
and possibly `∅` — the sets `C ∩ H` for `H` a non-trivial supporting hyperplane to `C`.

The book's vector `b` and Mathlib's continuous linear functional are the same quantification in
`ℝⁿ`; `exists_linFn` is the translation. -/
theorem isExposed_iff_exists_vector :
    IsExposed ℝ C C' ↔ (C'.Nonempty →
      ∃ b : Rn n, C' = {x | x ∈ C ∧ ∀ y ∈ C, pairing n y b ≤ pairing n x b}) := by
  constructor
  · intro h hne
    obtain ⟨l, hl⟩ := h hne
    obtain ⟨b, rfl⟩ := exists_linFn l
    exact ⟨b, by simpa using hl⟩
  · intro h hne
    obtain ⟨b, hb⟩ := h hne
    exact ⟨linFn b, by simpa using hb⟩

/-- **Rockafellar, §18 (p. 162).** An **exposed point** of `C` is a point through which there is a
supporting hyperplane containing no other point of `C`. -/
theorem mem_exposedPoints_iff {x : Rn n} :
    x ∈ C.exposedPoints ℝ ↔ x ∈ C ∧ ∃ b : Rn n, (∀ y ∈ C, pairing n y b ≤ pairing n x b) ∧
      ∀ y ∈ C, pairing n x b ≤ pairing n y b → y = x := by
  rw [exposed_point_def]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨l, hl⟩ := h
    obtain ⟨b, rfl⟩ := exists_linFn l
    exact ⟨b, fun y hy => by simpa using (hl y hy).1,
      fun y hy hle => (hl y hy).2 (by simpa using hle)⟩
  · obtain ⟨b, hmax, huniq⟩ := h
    exact ⟨linFn b, fun y hy =>
      ⟨by simpa using hmax y hy, fun hle => huniq y hy (by simpa using hle)⟩⟩

/-! ### Theorem 18.7: the exposed representation -/

/-- **Rockafellar, Theorem 18.7.** Let `C` be a closed convex set containing no lines, and let `S`
be the set of all exposed points and exposed directions of `C`. Then `C = cl (conv S)`.

Specialises `closure_convexHullPD_exposedPoints_exposedDirections`. Unlike Theorem 18.5 the
closure cannot be dropped: the exposed points of a closed convex set need not be closed. -/
theorem theorem_18_7 (hC : Convex ℝ C) (hCcl : IsClosed C) (hnl : ContainsNoLine C) :
    closure (convexHullPD (C.exposedPoints ℝ) (exposedDirections C)) = C :=
  closure_convexHullPD_exposedPoints_exposedDirections hC hCcl hnl

/-- **Rockafellar, Corollary 18.7.1.** Let `K` be a closed convex cone containing no lines, and
let `T` be any set of vectors in `K` such that each exposed ray of `K` is generated by some
`x ∈ T`. Then `K` is the closure of the convex cone generated by `T`.

**The book prints this corollary with no `Proof.` paragraph.** The argument it wants is the one
given for Corollary 18.5.2, one layer up: by Theorem 18.7, `K = cl (conv S)` for `S` the exposed
points and exposed directions of `K`; the origin is the only exposed point, because it is the only
extreme point of a line-free cone; and `conv` of the origin together with a set of directions is
the cone generated by those directions. That is exactly the proof of the backbone's
`closure_coneHull_of_forall_exposedDirection`, which this specialises through
`isExposedRay_iff_isExposedDirection`. As in Corollary 18.5.2 the book's "containing more than
just the origin" is unnecessary. -/
theorem corollary_18_7_1 {K T : Set (Rn n)} (hK : Convex ℝ K) (hKcl : IsClosed K)
    (hcone : IsCone K) (hne : K.Nonempty) (hnl : ContainsNoLine K) (hTK : T ⊆ K)
    (hgen : ∀ y, IsExposedRay K y → ∃ x ∈ T, ∃ a : ℝ, 0 < a ∧ y = a • x) :
    closure (PointedCone.hull ℝ T : Set (Rn n)) = K := by
  have hsmul := forall_smul_mem_of_isCone hcone hKcl
  exact closure_coneHull_of_forall_exposedDirection hK hKcl hne hsmul hnl hTK fun y hy =>
    hgen y ((isExposedRay_iff_isExposedDirection hne hsmul).2 hy)

/-! ### Theorem 18.8: the tangent representation -/

/-- **Rockafellar, §18 (p. 168).** A hyperplane `H` is **tangent** to a closed convex set `C` at a
point `x` if `H` is the unique supporting hyperplane to `C` at `x`; a **tangent half-space** is a
supporting half-space whose boundary is tangent to `C` at some point.

Here the hyperplane is `{z | ⟨z, b⟩ = ⟨x, b⟩}` and the half-space `{z | ⟨z, b⟩ ≤ ⟨x, b⟩}`. This is
the backbone's `IsTangentAt` read through `linFn`, and is the vector-versus-functional translation
only: `IsTangentAt` renders "unique hyperplane" as uniqueness of the functional up to a *positive*
multiple, since a hyperplane determines its functional up to a non-zero scalar and the supporting
inequality fixes the sign. -/
def IsTangentHyperplaneAt (C : Set (Rn n)) (b : Rn n) (x : Rn n) : Prop :=
  IsTangentAt C (linFn b) x

/-- **Rockafellar, Theorem 18.8.** An `n`-dimensional closed convex set `C` in `ℝⁿ` is the
intersection of the closed half-spaces tangent to it.

Specialises `eq_iInter_tangent_halfSpaces`; "`n`-dimensional in `ℝⁿ`" is `(interior C).Nonempty`,
and `exists_linFn` converts the backbone's quantification over functionals into the book's
quantification over vectors. The backbone does not route this through Corollary 18.7.1 as the book
does — it uses the polar of `C` instead. -/
theorem theorem_18_8 (hC : Convex ℝ C) (hCcl : IsClosed C) (hint : (interior C).Nonempty) :
    ⋂ (b : Rn n) (x : Rn n) (_ : IsTangentHyperplaneAt C b x),
      {z : Rn n | pairing n z b ≤ pairing n x b} = C := by
  refine subset_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · simp only [mem_iInter, mem_ofPred_eq] at hz
    rw [← eq_iInter_tangent_halfSpaces hC hCcl hint]
    simp only [mem_iInter, mem_ofPred_eq]
    intro f y hty
    obtain ⟨b, rfl⟩ := exists_linFn f
    simpa using hz b y hty
  · simp only [mem_iInter, mem_ofPred_eq]
    intro b y hty
    simpa using IsTangentAt.subset_halfSpace hty hz

end Rockafellar
