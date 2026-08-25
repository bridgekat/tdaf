/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Continuity
import Tdaf.Analysis.Convex.Polyhedral.Defs
import Tdaf.Analysis.Convex.Polyhedral.Ops
import Tdaf.Analysis.Convex.Representation
import Tdaf.Analysis.Convex.Subgradient.Defs

/-!
# The maximum of a convex function

Rockafellar's §32. Maximising a convex function behaves nothing like minimising one: the maximum
principle says that a relative interior maximiser forces the function to be constant, so maxima
live on the boundary — on faces, and ultimately on extreme points.

## Main results

* `ConvexFn.eq_of_isMaxOn_mem_relint` — **Theorem 32.1**, the maximum principle.
* `exists_isFace_forall_eq_of_isMaxOn` — **Corollary 32.1.1**: every maximiser lies in a face of
  `C` on which `f` is constant, so the maximiser set is a union of faces.
* `ConvexFn.iSup_convexHull`, `exists_eq_of_isMaxOn_convexHull` — **Theorem 32.2**: `conv` neither
  raises the supremum of a convex function nor creates maximisers.
* `ConvexFn.iSup_sdiff_relint`, `exists_notMem_relint_eq_of_isMaxOn` — **Corollary 32.2.1**: the
  supremum over `C` is already the supremum over the relative boundary of `C`.
* `ConvexFn.add_le_of_mem_recessionCone` — a convex function bounded above on `C` does not increase
  along a direction of recession of `C`. This is the analytic core of Theorem 32.3.
* `BddAboveOnRays` — the hypothesis of Theorem 32.3 and Corollary 32.3.3: `f` is bounded above on
  every half-line of `C`. `ConvexFn.add_le_of_bddAboveOnRays` and
  `ConvexFn.add_eq_of_mem_linealitySpace` are the two consequences the section runs on, and
  `BddAboveOnRays.subset_dom` recovers Rockafellar's standing `C ⊆ dom f` from it.
* `ConvexFn.iSup_extremePoints_of_containsNoLine`,
  `exists_mem_extremePoints_eq_of_isMaxOn_of_containsNoLine` — **Theorem 32.3**: for a closed
  convex `C` containing no lines and a convex `f` bounded above on `C`, the supremum over `C` is
  the supremum over the extreme points, and a maximiser can be replaced by an extreme point.
* `ConvexFn.iSup_extremePoints_add_coneHull` — Theorem 32.3 in representation form, with no
  boundedness hypothesis: the supremum over `C` is the supremum over the sums of an extreme point
  and a non-negative combination of extreme directions.
* `ConvexFn.eq_of_forall_le` — a convex function bounded above on the whole space is constant.
* `exists_mem_extremePoints_isMaxOn_of_finitelyGenerated_of_bddAboveOnRays`,
  `exists_mem_extremePoints_isMaxOn_of_finitelyGenerated` — Theorem 32.3 for a finitely generated
  (polyhedral) set: there the supremum is a maximum, attained at an extreme point. The second is
  **Corollary 32.3.4**, the uniformly bounded case.
* `exists_isMaxOn_of_polyhedral_of_bddAboveOnRays` — **Corollary 32.3.3**: on a nonempty
  polyhedral `C ⊆ dom f` with no half-line on which `f` is unbounded above, the supremum is
  attained. No "contains no lines" hypothesis: the lineality space of `C` is quotiented out.
* `ConvexFn.iSup_extremePoints`, `exists_mem_extremePoints_eq_of_isMaxOn` — **Corollary 32.3.2**
  for compact `C`: the supremum is already the supremum over the extreme points.
* `exists_mem_extremePoints_isMaxOn_of_isCompact` — the "supremum is attained" clause of
  **Corollary 32.3.2**, for a compact `C` inside `ri (dom f)`.
* `mem_normalCone_of_mem_subgradient_of_isMaxOn`, `ne_zero_of_mem_subgradient_of_isMaxOn` —
  **Theorem 32.4**: at a maximiser every subgradient is normal to `C`, and is non-zero as soon as
  `f` is not constant there.

## Design notes

**Maximisation is spelled `∀ z ∈ C, f z ≤ f x`, not `IsMaxOn`.** Every proof in §32 consumes the
hypothesis by applying it at one specific point, and the unfolded form is what `ConvexFn.epi_combo`
and the subgradient inequality want. `isMaxOn_iff` is the bridge for a caller who has `IsMaxOn`.

**Theorem 32.2 is `convexHull_min`, not a Carathéodory decomposition.** The sublevel set
`{z | f z ≤ α}` is convex, so it swallows `conv S` as soon as it contains `S`; the *strict*
sublevel set `{z | f z < f x}` does the same job for the attainment clause. Neither half needs a
topology or a dimension bound, which is why this section sits over `Module ℝ E`.

**Theorem 32.4 does not go through Theorem 23.7.** Rockafellar derives it from
`∂f x ⊆ N_{lev}(x)`; read directly it is one line, because the subgradient inequality at `z` and
maximality at `z` sandwich the pairing term between `f x` and `f x`.

**Theorem 32.3 is Theorem 18.5 plus one inequality.** Writing `x ∈ C` as `u + v` with `u` in the
convex hull of the extreme points and `v` in the cone of the extreme directions
(`convexHullPD_extremePoints_extremeDirections`), the half-line `u + t • v`, `t ≥ 0`, lies in `C`,
so boundedness above forces `f (u + v) ≤ f u` (`ConvexFn.add_le_of_mem_recessionCone`): a convex
function bounded above on a half-line is non-increasing along it. Theorem 32.2 then removes the
convex hull. Boundedness cannot be dropped — `f x = x` on `C = [0, ∞)` has supremum `⊤` over `C`
and `0` over the single extreme point — but the representation form
`ConvexFn.iSup_extremePoints_add_coneHull`, which keeps the directions, needs no hypothesis.

**Corollary 32.3.3 quotients out the lineality space by intersecting, not by passing to `E ⧸ L`.**
Rockafellar takes `D = C ∩ L^⊥` in an inner-product space; `eq_add_inter_of_isCompl` gives
`C = L + (C ∩ N)` for *any* complement `N` of `L`, which is all the argument needs and keeps the
statement free of an inner product. `f` is constant along `L` because both `y` and `−y` are
directions of recession of `C` and `f` is bounded above on the half-lines in each, so the two
inequalities of `ConvexFn.add_le_of_bddAboveOnRays` close on each other.

**The relative-boundary corollary is stated with `¬ IsAffineHalf C`, not with `ContainsNoLine C`.**
Rockafellar's Theorem 18.4 excludes the affine sets and the closed halves of affine sets, and both
exclusions are needed in §32 too: for `C = [0, ∞)` the relative boundary is `{0}`, and
`f x = x` has supremum `⊤` over `C`. Containing no lines is not enough by itself; it *is* enough
in dimension at least two (`ConvexFn.iSup_sdiff_relint_of_containsNoLine`, via
`not_containsNoLine_of_isAffineHalf`), which is the case Rockafellar has in mind.

## What is not here

**Theorem 32.3 in the book's exact form**, `sup_C f = sup_E f` with `E` the set of extreme points
of `C ∩ L^⊥` and `L` the lineality space of `C`. Its two specialisations are what is here:
`ConvexFn.iSup_extremePoints_of_containsNoLine` for `L = 0`, where `C ∩ L^⊥` is `C`, and
`exists_isMaxOn_of_polyhedral_of_bddAboveOnRays` (Corollary 32.3.3), whose maximiser is an extreme
point of `C ∩ N` for a complement `N` of `L` chosen inside the proof. Stating the book's form would
mean fixing that complement in the statement — Rockafellar fixes `L^⊥`, which needs an inner
product this development does not want to assume.

**The unqualified "supremum is attained" clause of Corollary 32.3.2.** It is false for a merely
compact convex `C ⊆ dom f`: take `C` the closed unit disc in `ℝ²`, `f = 0` on the open disc and
`f (cos θ, sin θ) = 1 - θ` for `θ ∈ (0, 2π]`, `f = 0` at `(1, 0)`. Chords between distinct boundary
points meet the circle only at their endpoints, so `f` is convex; its supremum over `C` is `1` and
is not attained. `exists_mem_extremePoints_isMaxOn_of_isCompact` therefore asks for
`C ⊆ ri (dom f)`, where Theorem 10.1 (`ConvexFn.continuousOn_relint_dom`) supplies the continuity
that compactness needs.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §32 (Theorems 32.1,
  32.2, 32.3, 32.4, Corollaries 32.1.1, 32.2.1, 32.3.1, 32.3.2, 32.3.3, 32.3.4 and 32.4.1).
-/

open scoped Pointwise

namespace Tdaf.ConvexAnalysis

/-! ### Theorem 32.1: the maximum principle -/

section Relint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {C : Set E}

/-- **Rockafellar, Theorem 32.1** (the maximum principle): if a convex function attains its
supremum over a convex set `C ⊆ dom f` at a *relative interior* point of `C`, it is constant on
`C`.

The proof is Rockafellar's. A relative interior point `z` can be prolonged past itself inside `C`
(Theorem 6.4), which exhibits `z` as a proper convex combination of `x` and a further point of
`C`; if `f x` were strictly below `f z`, convexity would put `f z` strictly below itself. -/
theorem ConvexFn.eq_of_isMaxOn_mem_relint (hf : ConvexFn f) (hCdom : C ⊆ dom f) {z : E}
    (hz : z ∈ ri C) (hmax : ∀ w ∈ C, f w ≤ f z) {x : E} (hx : x ∈ C) : f x = f z := by
  refine le_antisymm (hmax x hx) ?_
  by_contra hcon
  have hxlt : f x < f z := not_le.1 hcon
  obtain ⟨t, ht, hy⟩ := exists_one_lt_smul_mem_of_mem_relint hz (subset_affineSpan ℝ C hx)
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
  have htinv0 : (0 : ℝ) < t⁻¹ := inv_pos.2 ht0
  have htinv1 : t⁻¹ < 1 := by
    have hcancel : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0.ne'
    nlinarith
  obtain ⟨ζ, hζ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (ne_bot_of_gt hxlt)
    (mem_dom.1 (hCdom (intrinsicInterior_subset hz)))
  rw [hζ] at hxlt
  obtain ⟨ξ, hξ1, hξ2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hxlt
  have hξlt : ξ < ζ := by exact_mod_cast hξ2
  have hcomb := hf.epi_combo hξ1.le ((hmax _ hy).trans hζ.le)
    (by linarith : (0 : ℝ) ≤ 1 - t⁻¹) htinv0.le (by ring)
  rw [combo_prolong x z ht0.ne', hζ, _root_.EReal.coe_le_coe_iff] at hcomb
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t⁻¹) (by linarith : (0 : ℝ) < ζ - ξ)]

/-- **Rockafellar, Corollary 32.1.1**: the set of points at which a convex function attains its
supremum over `C` is a union of faces of `C`. Concretely, every maximiser lies in a face on which
`f` is constant.

Theorem 18.2 (`exists_isFace_mem_relint`) supplies the face having the maximiser in its relative
interior, and Theorem 32.1 applied to that face does the rest. -/
theorem exists_isFace_forall_eq_of_isMaxOn [FiniteDimensional ℝ E] (hf : ConvexFn f)
    (hC : Convex ℝ C) (hCdom : C ⊆ dom f) {z : E} (hz : z ∈ C) (hmax : ∀ w ∈ C, f w ≤ f z) :
    ∃ C', IsFace C C' ∧ z ∈ C' ∧ ∀ x ∈ C', f x = f z := by
  obtain ⟨C', hface, hzri⟩ := exists_isFace_mem_relint hC hz
  have hsub : C' ⊆ C := hface.toIsExtreme.1
  exact ⟨C', hface, intrinsicInterior_subset hzri,
    fun x hx => hf.eq_of_isMaxOn_mem_relint (hsub.trans hCdom) hzri
      (fun w hw => hmax w (hsub hw)) hx⟩

end Relint

/-! ### Theorem 32.2: passing to the convex hull -/

section Hull

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {S : Set E}

/-- **Rockafellar, Theorem 32.2**: taking the convex hull does not raise the supremum of a convex
function.

The sublevel set at the supremum over `S` is convex and contains `S`, hence contains `conv S`. -/
theorem ConvexFn.iSup_convexHull (hf : ConvexFn f) (S : Set E) :
    (⨆ x ∈ convexHull ℝ S, f x) = ⨆ x ∈ S, f x := by
  refine le_antisymm (iSup₂_le fun x hx => ?_)
    (iSup₂_le fun x hx => le_iSup₂ (f := fun z (_ : z ∈ convexHull ℝ S) => f z) x
      (subset_convexHull ℝ S hx))
  exact convexHull_min (fun z hz => le_iSup₂ (f := fun w (_ : w ∈ S) => f w) z hz)
    (hf.convex_le _) hx

/-- **Rockafellar, Theorem 32.2**, second clause: the convex hull creates no new maximisers, so if
the supremum over `conv S` is attained then it is already attained on `S`.

The *strict* sublevel set is convex too, so a convex function that stays below its maximum
throughout `S` stays below it throughout `conv S`. -/
theorem exists_eq_of_isMaxOn_convexHull (hf : ConvexFn f) {x : E} (hx : x ∈ convexHull ℝ S)
    (hmax : ∀ z ∈ convexHull ℝ S, f z ≤ f x) : ∃ z ∈ S, f z = f x := by
  by_contra hcon
  push Not at hcon
  have hlt : S ⊆ {w : E | f w < f x} := fun z hz =>
    lt_of_le_of_ne (hmax z (subset_convexHull ℝ S hz)) (hcon z hz)
  exact absurd (convexHull_min hlt (hf.convex_lt (f x)) hx) (lt_irrefl (f x))

end Hull

/-! ### Corollary 32.2.1: the supremum over the relative boundary -/

section Boundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {C : Set E}

/-- **Rockafellar, Theorem 18.4**, in hull form: a closed convex set that is neither an affine set
nor a closed half of an affine set is the convex hull of its relative boundary.

`exists_notMem_relint_mem_segment_of_not_isAffineHalf` is the pointwise form Theorem 18.4's proof
produces; this is the packaging §32 consumes. -/
theorem convexHull_sdiff_relint (hC : Convex ℝ C) (hCcl : IsClosed C) (hhalf : ¬ IsAffineHalf C) :
    convexHull ℝ (C \ ri C) = C := by
  refine subset_antisymm (convexHull_min Set.sdiff_subset hC) fun w hw => ?_
  by_cases hwri : w ∈ ri C
  · obtain ⟨a, haC, b, hbC, hari, hbri, hseg⟩ :=
      exists_notMem_relint_mem_segment_of_not_isAffineHalf hC hCcl hhalf hwri
    exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ (C \ ri C) ⟨haC, hari⟩)
      (subset_convexHull ℝ (C \ ri C) ⟨hbC, hbri⟩) hseg
  · exact subset_convexHull ℝ (C \ ri C) ⟨hw, hwri⟩

/-- **Rockafellar, Corollary 32.2.1**: the supremum of a convex function over a closed convex set
is already its supremum over the relative boundary of that set.

The hypothesis is Rockafellar's exceptional-case hypothesis in Theorem 18.4 — `C` is neither an
affine set nor a closed half of an affine set — and it cannot be dropped: over the half-line
`[0, ∞)` the relative boundary is the single point `0`, while `f x = x` has supremum `⊤`. -/
theorem ConvexFn.iSup_sdiff_relint (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) : (⨆ x ∈ C, f x) = ⨆ x ∈ C \ ri C, f x := by
  conv_lhs => rw [← convexHull_sdiff_relint hC hCcl hhalf]
  exact hf.iSup_convexHull _

/-- **Rockafellar, Corollary 32.2.1**, attainment clause: a maximiser over `C` can be replaced by
a maximiser on the relative boundary of `C`. This is the second half of Theorem 32.2 read through
Theorem 18.4, and it is Theorem 32.1 again in disguise. -/
theorem exists_notMem_relint_eq_of_isMaxOn (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) {x : E} (hx : x ∈ C) (hmax : ∀ z ∈ C, f z ≤ f x) :
    ∃ z ∈ C \ ri C, f z = f x := by
  rw [← convexHull_sdiff_relint hC hCcl hhalf] at hx hmax
  exact exists_eq_of_isMaxOn_convexHull hf hx hmax

/-- **Rockafellar, Corollary 32.2.1** under his standing hypothesis of §18: a closed convex set of
dimension at least two containing no lines is neither an affine set nor a closed half of one
(`not_containsNoLine_of_isAffineHalf`), so its supremum is carried by its relative boundary. -/
theorem ConvexFn.iSup_sdiff_relint_of_containsNoLine (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) (hne : C.Nonempty)
    (hdim : 2 ≤ Module.finrank ℝ (vectorSpan ℝ C)) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C \ ri C, f x :=
  hf.iSup_sdiff_relint hC hCcl fun h => not_containsNoLine_of_isAffineHalf h hne hdim hnl

end Boundary

/-! ### Theorem 32.3: the extreme point principle -/

section Ray

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {C : Set E}

/-- **A convex function bounded above on a half-line does not increase along it.** If
`f (u + t • v) ≤ β` for every `t ≥ 0`, then `f (u + v) ≤ f u`: the endpoint of the half-line
already sees the largest value on it.

The proof is the usual "a convex function bounded above on `[0, ∞)` is non-increasing": `u + v` is
the convex combination of `u` and the far point `u + t • v` with weights `1 - t⁻¹` and `t⁻¹`, so
`f (u + v) ≤ ξ + t⁻¹ (β - ξ)` for every `ξ > f u` and every `t ≥ 1`, and `t` can be taken large. -/
theorem ConvexFn.add_le_of_forall_add_smul_le (hf : ConvexFn f) {u v : E} {β : ℝ}
    (hray : ∀ t : ℝ, 0 ≤ t → f (u + t • v) ≤ (β : EReal)) : f (u + v) ≤ f u := by
  by_contra hcon
  have hlt : f u < f (u + v) := not_le.1 hcon
  obtain ⟨ξ, hξ1, hξ2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hlt
  obtain ⟨η, hη1, hη2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hξ2
  have hξη : ξ < η := by exact_mod_cast hη1
  set t : ℝ := max 1 (1 + (β - ξ) / (η - ξ)) with ht
  have ht1 : (1 : ℝ) ≤ t := le_max_left _ _
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hcancel : (β - ξ) / (η - ξ) * (η - ξ) = β - ξ := div_mul_cancel₀ _ (by linarith)
  have hkey : β - ξ < t * (η - ξ) := by
    nlinarith [le_max_right (1 : ℝ) (1 + (β - ξ) / (η - ξ))]
  have hcomb := hf.epi_combo hξ1.le (hray t ht0.le) (a := 1 - t⁻¹) (b := t⁻¹)
    (by simp [inv_le_one_of_one_le₀ ht1]) (by positivity) (by ring)
  have hpt : (1 - t⁻¹) • u + t⁻¹ • (u + t • v) = u + v := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul, sub_smul, one_smul]
    abel
  rw [hpt] at hcomb
  have hηlt : (η : EReal) < (((1 - t⁻¹) * ξ + t⁻¹ * β : ℝ) : EReal) := lt_of_lt_of_le hη2 hcomb
  have hηlt' : η < (1 - t⁻¹) * ξ + t⁻¹ * β := by exact_mod_cast hηlt
  have hinv0 : (0 : ℝ) < t⁻¹ := inv_pos.2 ht0
  have hmul : t⁻¹ * (β - ξ) < η - ξ := by
    have h := mul_lt_mul_of_pos_left hkey hinv0
    rwa [← mul_assoc, inv_mul_cancel₀ ht0.ne', one_mul] at h
  linarith

/-- **A convex function bounded above on `C` does not increase along a direction of recession of
`C`.** This is `ConvexFn.add_le_of_forall_add_smul_le` fed with the half-line `u + t • v`, `t ≥ 0`,
which a direction of recession keeps inside `C`. It is the analytic core of Theorem 32.3. -/
theorem ConvexFn.add_le_of_mem_recessionCone (hf : ConvexFn f) {β : ℝ}
    (hbdd : ∀ x ∈ C, f x ≤ (β : EReal)) {u v : E} (hu : u ∈ C) (hv : v ∈ recessionCone C) :
    f (u + v) ≤ f u :=
  hf.add_le_of_forall_add_smul_le fun t ht => hbdd _ (hv u hu t ht)

/-- **`f` is bounded above on every half-line of `C`.** This is the hypothesis of Rockafellar's
Theorem 32.3 and of its Corollary 32.3.3, spelled as a condition on the *rays* of `C` rather than
on `C` itself: for every `u` and `v` with `u + t • v ∈ C` for all `t ≥ 0`, some real `β` bounds
`f` on that half-line.

Taking `v = 0` makes the condition say that every point of `C` carries a value below some real,
that is, `C ⊆ dom f` (`BddAboveOnRays.subset_dom`); so this single predicate carries both of
Rockafellar's standing hypotheses in Theorem 32.3, `C ⊆ dom f` and "no half-line in `C` on which
`f` is unbounded above". A uniform bound is the special case `bddAboveOnRays_of_forall_le`. -/
def BddAboveOnRays (f : E → EReal) (C : Set E) : Prop :=
  ∀ u v : E, (∀ t : ℝ, 0 ≤ t → u + t • v ∈ C) →
    ∃ β : ℝ, ∀ t : ℝ, 0 ≤ t → f (u + t • v) ≤ (β : EReal)

/-- A uniform upper bound on `C` bounds `f` on every half-line of `C`. -/
theorem bddAboveOnRays_of_forall_le {β : ℝ} (hbdd : ∀ x ∈ C, f x ≤ (β : EReal)) :
    BddAboveOnRays f C := fun _ _ hray => ⟨β, fun t ht => hbdd _ (hray t ht)⟩

/-- A subset of `C` has no more half-lines than `C` has. -/
theorem BddAboveOnRays.mono {C' : Set E} (hray : BddAboveOnRays f C) (hsub : C' ⊆ C) :
    BddAboveOnRays f C' := fun u v hr => hray u v fun t ht => hsub (hr t ht)

/-- The degenerate half-lines — the points — of `C` already force `C ⊆ dom f`. -/
theorem BddAboveOnRays.subset_dom (hray : BddAboveOnRays f C) : C ⊆ dom f := by
  intro u hu
  obtain ⟨β, hβ⟩ := hray u 0 fun t _ => by simpa using hu
  have hle := hβ 0 le_rfl
  simp only [smul_zero, add_zero] at hle
  exact lt_of_le_of_lt hle (by simp)

/-- **A convex function bounded above on the half-lines of `C` does not increase along a direction
of recession of `C`.** This is `ConvexFn.add_le_of_mem_recessionCone` with the uniform bound
weakened to a bound on the one half-line that the proof actually uses. -/
theorem ConvexFn.add_le_of_bddAboveOnRays (hf : ConvexFn f) (hray : BddAboveOnRays f C) {u v : E}
    (hu : u ∈ C) (hv : v ∈ recessionCone C) : f (u + v) ≤ f u := by
  obtain ⟨β, hβ⟩ := hray u v fun t ht => hv u hu t ht
  exact hf.add_le_of_forall_add_smul_le hβ

/-- **A convex function bounded above on the half-lines of `C` is constant along the lineality
space of `C`.** Rockafellar reads this off Corollary 8.6.2; here the two opposite directions of
recession give the two inequalities through `ConvexFn.add_le_of_bddAboveOnRays`.

It is the step that lets Theorem 32.3 replace `C` by `C ∩ L'` for a complement `L'` of the
lineality space `L`. -/
theorem ConvexFn.add_eq_of_mem_linealitySpace (hf : ConvexFn f) (hray : BddAboveOnRays f C)
    {u v : E} (hu : u ∈ C) (hv : v ∈ linealitySpace C) : f (u + v) = f u := by
  obtain ⟨hv1, hv2⟩ := mem_linealitySpace.1 hv
  refine le_antisymm (hf.add_le_of_bddAboveOnRays hray hu hv1) ?_
  have huv : u + v ∈ C := add_mem_of_mem_recessionCone hv1 hu
  have hback := hf.add_le_of_bddAboveOnRays hray huv hv2
  rwa [show u + v + -v = u by abel] at hback

/-- **A convex function bounded above on the whole space is constant.** Applying
`ConvexFn.add_le_of_forall_add_smul_le` at `x` in the direction `y - x` and at `y` in the direction
`x - y` gives the two inequalities at once.

This is the unbounded companion of the maximum principle: there `ri C` forced constancy, here the
absence of any boundary does. -/
theorem ConvexFn.eq_of_forall_le (hf : ConvexFn f) {β : ℝ} (hbdd : ∀ x : E, f x ≤ (β : EReal))
    (x y : E) : f x = f y := by
  have key : ∀ u v : E, f (u + v) ≤ f u := fun u v =>
    hf.add_le_of_forall_add_smul_le fun t _ => hbdd _
  have hxy : x + (y - x) = y := by abel
  have hyx : y + (x - y) = x := by abel
  have h₁ := key x (y - x)
  have h₂ := key y (x - y)
  rw [hxy] at h₁
  rw [hyx] at h₂
  exact le_antisymm h₂ h₁

end Ray

section ExtremeUnbounded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {C : Set E}

/-- **Every point of `C` is dominated by a point of the convex hull of the extreme points**, for a
convex function bounded above on the half-lines of a closed convex `C` containing no lines.

Theorem 18.5 splits `x` as `u + v` with `u ∈ conv (ext C)` and `v` a non-negative combination of
extreme directions, hence a direction of recession of `C`; `ConvexFn.add_le_of_bddAboveOnRays`
then gives `f x ≤ f u`. Only the half-line `u + t • v` is used, which is why the hypothesis is
`BddAboveOnRays` and not a uniform bound. -/
theorem ConvexFn.exists_mem_convexHull_extremePoints_le (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) (hray : BddAboveOnRays f C)
    {x : E} (hx : x ∈ C) : ∃ u ∈ convexHull ℝ (C.extremePoints ℝ), f x ≤ f u := by
  have hrep := convexHullPD_extremePoints_extremeDirections hC hCcl hnl
  have hx' : x ∈ convexHullPD (C.extremePoints ℝ) (extremeDirections C) := by rw [hrep]; exact hx
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_convexHullPD.1 hx'
  refine ⟨u, hu, hf.add_le_of_bddAboveOnRays hray ?_ ?_⟩
  · rw [← hrep]
    exact convexHull_subset_convexHullPD _ _ hu
  · rw [← hrep]
    exact coneHull_subset_recessionCone_convexHullPD _ _ hv

/-- **Rockafellar, Theorem 32.3**: the supremum of a convex function bounded above on a closed
convex set `C` containing no lines is its supremum over the extreme points of `C`.

Boundedness above is essential, and is what makes the extreme *directions* invisible in the
answer: `f x = x` on `C = [0, ∞)` has supremum `⊤` over `C` and `0` over the extreme points. -/
theorem ConvexFn.iSup_extremePoints_of_containsNoLine (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) {β : ℝ} (hbdd : ∀ x ∈ C, f x ≤ (β : EReal)) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x := by
  refine le_antisymm (iSup₂_le fun x hx => ?_)
    (iSup₂_le fun x hx => le_iSup₂ (f := fun z (_ : z ∈ C) => f z) x (extremePoints_subset hx))
  obtain ⟨u, hu, hle⟩ :=
    hf.exists_mem_convexHull_extremePoints_le hC hCcl hnl (bddAboveOnRays_of_forall_le hbdd) hx
  refine hle.trans ?_
  rw [← hf.iSup_convexHull (C.extremePoints ℝ)]
  exact le_iSup₂ (f := fun z (_ : z ∈ convexHull ℝ (C.extremePoints ℝ)) => f z) u hu

/-- **Rockafellar, Corollary 32.3.1**: if the supremum of a convex function over a closed convex
set containing no lines is attained at all, it is attained at an extreme point. This is also
Theorem 32.3's attainment clause.

No boundedness hypothesis is needed — a finite maximum is itself a bound — but `f x ≠ ⊤` is: for
`C = [0, ∞)` and `f` equal to `0` on `[0, 1)` and `⊤` on `[1, ∞)`, the value `⊤` is a maximum,
while the only extreme point carries the value `0`. Rockafellar's standing hypothesis
`C ⊆ dom f` supplies it. -/
theorem exists_mem_extremePoints_eq_of_isMaxOn_of_containsNoLine (hf : ConvexFn f)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hnl : ContainsNoLine C) {x : E} (hx : x ∈ C)
    (hxt : f x ≠ ⊤) (hmax : ∀ z ∈ C, f z ≤ f x) : ∃ z ∈ C.extremePoints ℝ, f z = f x := by
  rcases eq_or_ne (f x) ⊥ with hbot | hbot
  · obtain ⟨z, hz⟩ := extremePoints_nonempty_of_containsNoLine hC hCcl hnl ⟨x, hx⟩
    have hzle : f z ≤ ⊥ := hbot ▸ hmax z (extremePoints_subset hz)
    exact ⟨z, hz, by rw [le_bot_iff.1 hzle, hbot]⟩
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbot (lt_top_iff_ne_top.2 hxt)
  have hbdd : ∀ z ∈ C, f z ≤ (r : EReal) := fun z hz => hr ▸ hmax z hz
  obtain ⟨u, hu, hle⟩ :=
    hf.exists_mem_convexHull_extremePoints_le hC hCcl hnl (bddAboveOnRays_of_forall_le hbdd) hx
  have hsub : convexHull ℝ (C.extremePoints ℝ) ⊆ C := convexHull_min extremePoints_subset hC
  have hux : f u = f x := le_antisymm (hmax u (hsub hu)) hle
  obtain ⟨z, hz, hzu⟩ :=
    exists_eq_of_isMaxOn_convexHull hf hu fun z hz => hux ▸ hmax z (hsub hz)
  exact ⟨z, hz, by rw [hzu, hux]⟩

/-- **Rockafellar, Theorem 32.3** in representation form, with no boundedness hypothesis: the
supremum of a convex function over a closed convex set containing no lines is its supremum over
the sums `u + v` of an extreme point `u` and a non-negative combination `v` of extreme directions.

This is Theorem 18.5 fed to Theorem 32.2: `conv (ext C + cone (extremeDirections C))` is
`conv (ext C) + cone (extremeDirections C)`, which is `C`. Boundedness above collapses the second
summand and returns `ConvexFn.iSup_extremePoints_of_containsNoLine`. -/
theorem ConvexFn.iSup_extremePoints_add_coneHull (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) :
    (⨆ x ∈ C, f x)
      = ⨆ x ∈ C.extremePoints ℝ + (PointedCone.hull ℝ (extremeDirections C) : Set E), f x := by
  have hcone : Convex ℝ ((PointedCone.hull ℝ (extremeDirections C) : Set E)) :=
    ((PointedCone.hull ℝ (extremeDirections C) : ConvexCone ℝ E)).convex
  have hhull : convexHull ℝ
      (C.extremePoints ℝ + (PointedCone.hull ℝ (extremeDirections C) : Set E)) = C := by
    rw [convexHull_add, hcone.convexHull_eq, ← convexHullPD_def]
    exact convexHullPD_extremePoints_extremeDirections hC hCcl hnl
  conv_lhs => rw [← hhull]
  exact hf.iSup_convexHull _

end ExtremeUnbounded

/-! ### Theorem 32.3 for finitely generated sets -/

section Polyhedral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {C : Set E}

/-- **Theorem 32.3 for a finitely generated set**: a convex function bounded above on every
half-line of a nonempty finitely generated convex set containing no lines attains its supremum at
one of its finitely many extreme points.

The ingredient beyond Theorem 32.3 is Corollary 18.3.1 (`extremePoints_convexHullPD_subset`): a
finitely generated set has only finitely many extreme points, so the supremum over them is a
maximum, and the sublevel set at that maximum swallows their convex hull.

`exists_mem_extremePoints_isMaxOn_of_finitelyGenerated` is the uniformly bounded case, which is
Rockafellar's Corollary 32.3.4. -/
theorem exists_mem_extremePoints_isMaxOn_of_finitelyGenerated_of_bddAboveOnRays (hf : ConvexFn f)
    (hC : FinitelyGenerated C) (hnl : ContainsNoLine C) (hne : C.Nonempty)
    (hray : BddAboveOnRays f C) : ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z := by
  have hcl : IsClosed C := hC.isClosed
  obtain ⟨P, D, hCeq⟩ := hC
  have hCPD : C = convexHullPD (P : Set E) (D : Set E) := hCeq
  have hconv : Convex ℝ C := by rw [hCPD]; exact convex_convexHullPD _ _
  have hsub : C.extremePoints ℝ ⊆ (P : Set E) := by
    rw [hCPD]; exact extremePoints_convexHullPD_subset _ _
  have hfin : (C.extremePoints ℝ).Finite := P.finite_toSet.subset hsub
  obtain ⟨z, hz, hzmax⟩ := Set.exists_max_image (C.extremePoints ℝ) f hfin
    (extremePoints_nonempty_of_containsNoLine hconv hcl hnl hne)
  refine ⟨z, hz, fun w hw => ?_⟩
  obtain ⟨u, hu, hle⟩ := hf.exists_mem_convexHull_extremePoints_le hconv hcl hnl hray hw
  exact hle.trans (convexHull_min (fun y hy => hzmax y hy) (hf.convex_le (f z)) hu)

/-- **Rockafellar, Corollary 32.3.4**: a convex function bounded above on a nonempty polyhedral
convex set containing no lines attains its supremum at one of its finitely many extreme points.

"Polyhedral" is in its finitely generated form (Theorem 19.1); `hbdd` carries both Rockafellar's
boundedness hypothesis and his standing `C ⊆ dom f`. -/
theorem exists_mem_extremePoints_isMaxOn_of_finitelyGenerated (hf : ConvexFn f)
    (hC : FinitelyGenerated C) (hnl : ContainsNoLine C) (hne : C.Nonempty) {β : ℝ}
    (hbdd : ∀ x ∈ C, f x ≤ (β : EReal)) : ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z :=
  exists_mem_extremePoints_isMaxOn_of_finitelyGenerated_of_bddAboveOnRays hf hC hnl hne
    (bddAboveOnRays_of_forall_le hbdd)

/-- **Rockafellar, Corollary 32.3.3**: a convex function bounded above on every half-line of a
nonempty polyhedral convex set `C ⊆ dom f` attains its supremum relative to `C`.

Unlike Corollary 32.3.4 this asks nothing about lines in `C`, and correspondingly claims nothing
about extreme points of `C` — a set containing a line has none. The lineality space `L` of `C` is
quotiented out instead: for any complement `N` of `L`, Rockafellar's decomposition
`C = L + (C ∩ N)` (`eq_add_inter_of_isCompl`) reduces the supremum over `C` to the supremum over
`D = C ∩ N`, because `f` is constant along `L` (`ConvexFn.add_eq_of_mem_linealitySpace`). That `D`
is polyhedral (a submodule is polyhedral in finite dimensions), nonempty, and contains no lines —
a line direction of `D` lies in `L ⊓ N = ⊥` — so
`exists_mem_extremePoints_isMaxOn_of_finitelyGenerated_of_bddAboveOnRays` applies to it, and the
maximiser it returns is a maximiser over all of `C`.

The maximiser is an extreme point of `D`, not of `C`, and it depends on the choice of `N`; that is
why the conclusion is bare attainment. Rockafellar's standing `C ⊆ dom f` is carried by `hray`
(`BddAboveOnRays.subset_dom`). -/
theorem exists_isMaxOn_of_polyhedral_of_bddAboveOnRays (hf : ConvexFn f) (hC : Polyhedral C)
    (hne : C.Nonempty) (hray : BddAboveOnRays f C) : ∃ z ∈ C, ∀ w ∈ C, f w ≤ f z := by
  obtain ⟨N, hN⟩ := Submodule.exists_isCompl (linealitySubmodule C)
  have hCconv : Convex ℝ C := hC.convex
  have hCcl : IsClosed C := hC.isClosed
  have hdec : C = (linealitySubmodule C : Set E) + (C ∩ (N : Set E)) := eq_add_inter_of_isCompl hN
  have hsplit : ∀ w ∈ C, ∃ q ∈ C ∩ (N : Set E), f w = f q := by
    intro w hw
    obtain ⟨p, hp, q, hq, rfl⟩ := (hdec ▸ hw : w ∈ (linealitySubmodule C : Set E) + (C ∩ N))
    refine ⟨q, hq, ?_⟩
    change f (p + q) = f q
    rw [show p + q = q + p by abel]
    exact hf.add_eq_of_mem_linealitySpace hray hq.1 (by simpa using hp)
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨q₀, hq₀, -⟩ := hsplit x₀ hx₀
  have hDpoly : Polyhedral (C ∩ (N : Set E)) := hC.inter (polyhedral_coe_submodule N)
  have hDnl : ContainsNoLine (C ∩ (N : Set E)) := by
    intro a y hy0
    by_contra hcon
    push Not at hcon
    have hyC : y ∈ recessionCone C :=
      mem_recessionCone_of_exists_ray hCconv hCcl ⟨a, fun t _ => (hcon t).1⟩
    have hyC' : -y ∈ recessionCone C := by
      refine mem_recessionCone_of_exists_ray hCconv hCcl ⟨a, fun t _ => ?_⟩
      rw [show a + t • (-y) = a + (-t) • y by module]
      exact (hcon (-t)).1
    have hyL : y ∈ linealitySubmodule C :=
      mem_linealitySubmodule.2 (mem_linealitySpace.2 ⟨hyC, hyC'⟩)
    have hyN : y ∈ N := by
      have hdiff := N.sub_mem (hcon 1).2 (hcon 0).2
      rwa [show a + (1 : ℝ) • y - (a + (0 : ℝ) • y) = y by module] at hdiff
    exact hy0 (by simpa using hN.disjoint.le_bot ⟨hyL, hyN⟩)
  obtain ⟨z, hz, hzmax⟩ := exists_mem_extremePoints_isMaxOn_of_finitelyGenerated_of_bddAboveOnRays
    hf hDpoly.finitelyGenerated hDnl ⟨q₀, hq₀⟩ (hray.mono Set.inter_subset_left)
  refine ⟨z, (extremePoints_subset hz : z ∈ C ∩ (N : Set E)).1, fun w hw => ?_⟩
  obtain ⟨q, hq, hwq⟩ := hsplit w hw
  rw [hwq]
  exact hzmax q hq

end Polyhedral

/-! ### Corollary 32.3.2: the extreme point principle, compact case -/

section Extreme

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {C : Set E}

/-- **Rockafellar, Corollary 32.3.2** for a compact `C`: the supremum of a convex function over a
compact convex set is its supremum over the extreme points. This is Minkowski's theorem
(`convexHull_extremePoints`, Corollary 18.5.1) fed to Theorem 32.2. -/
theorem ConvexFn.iSup_extremePoints (hf : ConvexFn f) (hcomp : IsCompact C) (hconv : Convex ℝ C) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x := by
  conv_lhs => rw [← convexHull_extremePoints hcomp hconv]
  exact hf.iSup_convexHull _

/-- **Rockafellar, Corollary 32.3.2** for a compact `C`, attainment clause: a maximiser over a
compact convex set can always be replaced by an extreme point. -/
theorem exists_mem_extremePoints_eq_of_isMaxOn (hf : ConvexFn f) (hcomp : IsCompact C)
    (hconv : Convex ℝ C) {x : E} (hx : x ∈ C) (hmax : ∀ z ∈ C, f z ≤ f x) :
    ∃ z ∈ C.extremePoints ℝ, f z = f x := by
  rw [← convexHull_extremePoints hcomp hconv] at hx hmax
  exact exists_eq_of_isMaxOn_convexHull hf hx hmax

/-- **Rockafellar, Corollary 32.3.2**, the "supremum is attained" clause: a convex function attains
its supremum over a nonempty compact convex set `C ⊆ ri (dom f)` at an extreme point of `C`.

Compactness alone does not give attainment — see the module docstring for a convex function on the
closed unit disc whose supremum is not attained — so the hypothesis is `C ⊆ ri (dom f)`, where
Theorem 10.1 (`ConvexFn.continuousOn_relint_dom`) makes `f` continuous on `C`. -/
theorem exists_mem_extremePoints_isMaxOn_of_isCompact (hf : ConvexFn f) (hp : Proper f)
    (hcomp : IsCompact C) (hconv : Convex ℝ C) (hne : C.Nonempty) (hCri : C ⊆ ri (dom f)) :
    ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z := by
  obtain ⟨x, hx, hxmax⟩ := hcomp.exists_isMaxOn hne ((hf.continuousOn_relint_dom hp).mono hCri)
  obtain ⟨z, hz, hzx⟩ :=
    exists_mem_extremePoints_eq_of_isMaxOn hf hcomp hconv hx fun w hw => isMaxOn_iff.1 hxmax w hw
  exact ⟨z, hz, fun w hw => hzx ▸ isMaxOn_iff.1 hxmax w hw⟩

end Extreme

/-! ### Theorem 32.4: subgradients at a maximiser -/

section Optimality

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {C : Set E} {x : E} {y : F}

/-- **Rockafellar, Theorem 32.4**: at a point where `f` attains its supremum over `C`, every
subgradient of `f` is normal to `C`.

All that is needed is that `f x` be a real number, so that it can be cancelled from the two
inequalities that sandwich the pairing term. -/
theorem mem_normalCone_of_mem_subgradient_of_isMaxOn (hxb : f x ≠ ⊥) (hxt : f x ≠ ⊤)
    (hmax : ∀ z ∈ C, f z ≤ f x) (hy : y ∈ subgradient B f x) : y ∈ normalCone B C x := by
  intro z hz
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hxb (lt_top_iff_ne_top.2 hxt)
  have h2 : f x + ((B (z - x) y : ℝ) : EReal) ≤ f x := le_trans (hy z) (hmax z hz)
  rw [hr, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at h2
  linarith

/-- **Rockafellar, Theorem 32.4**, the non-vanishing clause: if `f` is not constant on `C`, no
subgradient at a maximiser can be zero. -/
theorem ne_zero_of_mem_subgradient_of_isMaxOn (hmax : ∀ z ∈ C, f z ≤ f x) {z₀ : E} (hz₀ : z₀ ∈ C)
    (hne : f z₀ ≠ f x) (hy : y ∈ subgradient B f x) : y ≠ 0 := by
  rintro rfl
  have hle : f x ≤ f z₀ := by simpa using hy z₀
  exact hne (le_antisymm (hmax z₀ hz₀) hle)

/-- **Rockafellar, Corollary 32.4.1**: a vector normal to `C` at `x` is exactly one whose linear
functional attains its supremum over `C` at `x`. Combined with Theorem 32.4, a subgradient at a
maximiser of `f` is a *linear* functional maximised at the same point. -/
theorem le_of_mem_normalCone (hy : y ∈ normalCone B C x) {z : E} (hz : z ∈ C) : B z y ≤ B x y := by
  have h := hy z hz
  rw [map_sub, LinearMap.sub_apply] at h
  linarith

end Optimality

end Tdaf.ConvexAnalysis
