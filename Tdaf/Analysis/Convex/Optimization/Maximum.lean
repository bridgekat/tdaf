/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Face
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
* `ConvexFn.iSup_extremePoints`, `exists_mem_extremePoints_eq_of_isMaxOn` — **Corollary 32.3.2**
  for compact `C`: the supremum is already the supremum over the extreme points.
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

## What is not here

**Theorem 32.3 and Corollaries 32.3.1, 32.3.3, 32.3.4.** They rest on Theorem 18.5 for *unbounded*
closed convex sets — the representation by extreme points *and extreme directions* — which
`Face.lean` has only in the bounded case (`convexHull_extremePoints`, Corollary 18.5.1).
`ConvexFn.iSup_extremePoints` is that bounded case, and it is Corollary 32.3.2 without the
"the supremum is attained" clause, which additionally needs Theorem 10.1 (continuity of a convex
function on the relative interior of its domain).

**Corollary 32.2.1** (the supremum over `C` equals the supremum over its relative boundary) needs
Theorem 18.4 in full generality, which `Face.lean` also has only for compact sets.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §32 (Theorems 32.1,
  32.2, 32.4, Corollaries 32.1.1, 32.3.2 and 32.4.1).
-/

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
