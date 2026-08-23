/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Saddle.Closure

/-!
# The correspondence between saddle-functions and bifunctions

Rockafellar's §33, last part: **Theorem 33.3** and **Corollary 33.3.1**. The brackets
`⟨Fu, y⟩ = cl₂ K` and `⟨u, F* y⟩ = cl₁ K` set up a one-to-one correspondence between the *lower
closed* concave-convex functions on `U × Y` and the *closed convex* bifunctions from `U` to `X`.
This is the theorem Part VII is built on: it is to saddle-functions what "a bilinear function is a
linear transformation" is to linear algebra.

## Main results

* `eq_of_bracket_eq` — the bracket determines an image-closed convex bifunction. This is what makes
  the correspondence injective, and it is why image-closedness has to be named.
* `lowerClosedFn_bracket` — **Theorem 33.3**, one direction: the bracket of a closed convex
  bifunction is lower closed.
* `exists_unique_convexBifun_bracket_eq` — **Theorem 33.3**, the other direction: every lower
  closed concave-convex function is the bracket of a *unique* closed convex bifunction.
* `exists_unique_bifun_of_closure_pair` — **Corollary 33.3.1**: a pair `(K̲, K̄)` with
  `cl₁ K̲ = K̄` and `cl₂ K̄ = K̲` is exactly a pair of brackets of a closed convex bifunction.
* `le_of_partialCl₂_eq` — such a pair satisfies `K̲ ≤ K̄`.

## Design notes

**Image-closedness is the right notion of "determined by the bracket".** `bracket Bx F u` is
`conj Bx (F u)`, which sees only `cl (F u)`; two bifunctions with the same bracket therefore have
the same slice-wise closures and nothing more. Asking each `F u` to be closed makes the bracket
injective, and `ClosedBifun.imageClosedBifun` says the joint closedness the theorem asks for is
enough — a slice of a closed function is closed.

**Closedness of the constructed bifunction is not free, and not hard.** Given a lower closed `K`,
`F = bifunOfSaddle Bx K` has the right bracket immediately, but `ClosedBifun F` has to be argued:
`cl F` and `F` are both image-closed and convex, and Theorem 33.2 shows they have the same
bracket, so they are equal. This is precisely Rockafellar's "for image-closed convex bifunctions
`F`, the condition `⟨(cl F)u, x*⟩ = ⟨Fu, x*⟩` is equivalent to `cl F = F`".

**The pairings are explicit arguments again.** Neither `LowerClosedFn K` nor the `∃!` mentions
`Bu`, so nothing can infer it; as in `Saddle/Closure.lean` the pairings and their instance binders
belong to the theorem rather than to the section.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §33 (Theorem 33.3,
  Corollary 33.3.1).
-/

namespace Tdaf.ConvexAnalysis

/-! ### The bracket is injective on image-closed convex bifunctions -/

section Injective

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F G : Bifun U X}

/-- **Two image-closed convex bifunctions with the same bracket are equal.** The bracket sees only
`cl (F u)`, and image-closedness says that is all of `F u`. -/
theorem eq_of_bracket_eq (hF : ConvexBifun F) (hG : ConvexBifun G) (hFi : ImageClosedBifun F)
    (hGi : ImageClosedBifun G) (h : bracket Bx F = bracket Bx G) : F = G := by
  funext u
  calc F u = clFn (F u) := (hFi u).symm
    _ = conj Bx.flip (bracket Bx F u) := clFn_eq_conj_bracket hF u
    _ = conj Bx.flip (bracket Bx G u) := by rw [h]
    _ = clFn (G u) := (clFn_eq_conj_bracket hG u).symm
    _ = G u := hGi u

end Injective

/-! ### Theorem 33.3 -/

section Thm333

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- **Rockafellar, Theorem 33.2**, first equation, for the pair of brackets of a bifunction:
`cl₁ ⟨Fu, y⟩ = ⟨u, F* y⟩`. -/
theorem partialCl₁_bracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    partialCl₁ (fun p : U × Y => bracket Bx F p.1 p.2)
      = fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2 := by
  funext p
  exact (congrFun (concaveBracket_adjointBifun_eq_partialCl₁ (Bu := Bu) hF p.2) p.1).symm

/-- **Rockafellar, Theorem 33.2**, second equation for a *closed* bifunction:
`cl₂ ⟨u, F* y⟩ = ⟨Fu, y⟩`. The two brackets of a closed convex bifunction are therefore a closure
pair in the sense of Corollary 33.3.1. -/
theorem partialCl₂_concaveBracket_adjoint (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    partialCl₂ (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2)
      = fun p : U × Y => bracket Bx F p.1 p.2 := by
  funext p
  have h2 := bracket_concaveAdjointBifun_eq_partialCl₂ (Bu := Bu) (Bx := Bx)
    (concaveBifun_adjointBifun Bu Bx F) p.1
  rw [concaveAdjointBifun_adjointBifun_eq_clBifun hF, hcl.clBifun_eq] at h2
  exact (congrFun h2 p.2).symm

/-- **Rockafellar, Theorem 33.3**, one direction: the bracket of a closed convex bifunction is a
lower closed concave-convex function. Both closure steps are Theorem 33.2, and the loop closes
because `F** = cl F = F`. -/
theorem lowerClosedFn_bracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    LowerClosedFn (fun p : U × Y => bracket Bx F p.1 p.2) := by
  rw [lowerClosedFn_iff, lowerCl_def, partialCl₁_bracket Bu Bx hF,
    partialCl₂_concaveBracket_adjoint Bu Bx hF hcl]

/-- **Rockafellar, Theorem 33.3**, the other direction: a lower closed concave-convex function is
the bracket of one and only one closed convex bifunction, namely `F u = K(u, ·)*`. -/
theorem exists_unique_convexBifun_bracket_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hK : ConcaveConvexFn K) (hlc : LowerClosedFn K) :
    ∃! F : Bifun U X, ConvexBifun F ∧ ClosedBifun F ∧
      (fun p : U × Y => bracket Bx F p.1 p.2) = K := by
  have hF : ConvexBifun (bifunOfSaddle Bx K) := convexBifun_bifunOfSaddle hK Bx
  have hbr : (fun p : U × Y => bracket Bx (bifunOfSaddle Bx K) p.1 p.2) = K :=
    funext fun p => (bracket_bifunOfSaddle hK p).trans (congrFun hlc.convexClosedFn p)
  have himg : ImageClosedBifun (bifunOfSaddle Bx K) :=
    fun u => closedFn_conj (B := Bx.flip) (f := fun y => K (u, y))
  have hcl1 : partialCl₁ K
      = fun p : U × Y =>
        concaveBracket Bu (adjointBifun Bu Bx (bifunOfSaddle Bx K)) p.1 p.2 := by
    calc partialCl₁ K
        = partialCl₁ (fun p : U × Y => bracket Bx (bifunOfSaddle Bx K) p.1 p.2) := by rw [hbr]
      _ = _ := by
          funext p
          exact (congrFun (concaveBracket_adjointBifun_eq_partialCl₁ (Bu := Bu) hF p.2) p.1).symm
  have hMK : partialCl₂ (fun p : U × Y =>
      concaveBracket Bu (adjointBifun Bu Bx (bifunOfSaddle Bx K)) p.1 p.2) = K := by
    rw [← hcl1]
    exact hlc
  have hclbr : bracket Bx (clBifun (bifunOfSaddle Bx K)) = bracket Bx (bifunOfSaddle Bx K) := by
    funext u y
    have h2 := congrFun
      (partialCl₂_concaveBracket_adjointBifun (Bu := Bu) (Bx := Bx) hF u) y
    rw [← h2, congrFun hMK (u, y)]
    exact (congrFun hbr (u, y)).symm
  have hclF : clBifun (bifunOfSaddle Bx K) = bifunOfSaddle Bx K :=
    eq_of_bracket_eq hF.clBifun hF
      ((closedBifun_clBifun (bifunOfSaddle Bx K)).imageClosedBifun) himg hclbr
  refine ⟨bifunOfSaddle Bx K, ⟨hF, closedBifun_iff_clBifun_eq.2 hclF, hbr⟩, ?_⟩
  rintro F' ⟨hF'conv, hF'cl, hF'br⟩
  exact eq_of_bracket_eq hF'conv hF hF'cl.imageClosedBifun himg
    (funext fun u => funext fun y => (congrFun hF'br (u, y)).trans (congrFun hbr (u, y)).symm)

end Thm333

/-! ### Corollary 33.3.1 -/

section Cor3331Order

variable {U Y : Type*} [TopologicalSpace Y] {Klow Kup : U × Y → EReal}

/-- **Rockafellar, Corollary 33.3.1**, last clause: a closure pair is ordered, `K̲ ≤ K̄`. Only the
`cl₂` relation is needed, because `cl₂` lowers. -/
theorem le_of_partialCl₂_eq (h2 : partialCl₂ Kup = Klow) : Klow ≤ Kup := by
  rw [← h2]
  exact partialCl₂_le Kup

end Cor3331Order

section Cor3331

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Klow Kup : U × Y → EReal}

/-- **Rockafellar, Corollary 33.3.1**: the pairs `(K̲, K̄)` of concave-convex functions with
`cl₁ K̲ = K̄` and `cl₂ K̄ = K̲` are exactly the pairs of brackets `(⟨Fu, y⟩, ⟨u, F* y⟩)` of a
closed convex bifunction, and `F` is unique. -/
theorem exists_unique_bifun_of_closure_pair (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hK : ConcaveConvexFn Klow) (h1 : partialCl₁ Klow = Kup) (h2 : partialCl₂ Kup = Klow) :
    ∃! F : Bifun U X, ConvexBifun F ∧ ClosedBifun F ∧
      (fun p : U × Y => bracket Bx F p.1 p.2) = Klow ∧
      (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2) = Kup := by
  have hlc : LowerClosedFn Klow := by
    rw [lowerClosedFn_iff, lowerCl_def, h1, h2]
  obtain ⟨F, ⟨hFconv, hFcl, hFbr⟩, huniq⟩ :=
    exists_unique_convexBifun_bracket_eq Bu Bx hK hlc
  have hup : (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2) = Kup := by
    refine Eq.trans ?_ h1
    rw [← hFbr]
    funext p
    exact congrFun (concaveBracket_adjointBifun_eq_partialCl₁ (Bu := Bu) hFconv p.2) p.1
  refine ⟨F, ⟨hFconv, hFcl, hFbr, hup⟩, ?_⟩
  rintro F' ⟨hF'conv, hF'cl, hF'br, -⟩
  exact huniq F' ⟨hF'conv, hF'cl, hF'br⟩

end Cor3331

end Tdaf.ConvexAnalysis
