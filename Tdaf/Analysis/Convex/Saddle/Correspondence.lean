/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Optimization.Normal
import Tdaf.Analysis.Convex.Saddle.Closure

/-!
# The correspondence between saddle-functions and bifunctions

Rockafellar's §33, last part: **Theorem 33.3** with **Corollaries 33.1.2, 33.3.1 and 33.3.2**.
The brackets
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
* `saddleOfBifun` — `⟨Fu, x*⟩` uncurried, so that Corollary 33.1.2 can be stated as a map.
* `bifunSaddleEquiv` — **Corollary 33.1.2**: `K = ⟨Fu, x*⟩` and `Fu = K(u, ·)*` are inverse
  bijections between the *image-closed convex bifunctions* and the *convex-closed* concave-convex
  functions. The two round trips are `saddleOfBifun_bifunOfSaddle` and
  `bifunOfSaddle_saddleOfBifun`.
* `lowerUpperClosedEquiv` — **Corollary 33.3.2**: `cl₁` and `cl₂` are inverse bijections between
  the lower closed and the upper closed concave-convex functions. Both round trips are the
  definitions of `LowerClosedFn` and `UpperClosedFn`, so the only content is that each operator
  lands in the other class (`upperClosedFn_partialCl₁`, `lowerClosedFn_partialCl₂`).
* `polyhedralFn_bracket`, `polyhedralFn_neg_bracket`,
  `imageClosedBifun_of_polyhedralBifun`, `eq_conj_bracket_of_polyhedralBifun`,
  `eq_iSup_sub_bracket_of_polyhedralBifun` — **Corollary 33.1.3**, the polyhedral form of
  Corollary 33.1.2: `⟨Fu, ·⟩` is polyhedral convex, `⟨F·, y⟩` is polyhedral concave, and a
  *proper* polyhedral convex bifunction is image-closed, hence recovered from its bracket.
* `polyhedralFn_neg_graphFn_adjointBifun`, `polyhedralFn_concaveBracket`, `dom_concaveBracket`,
  `closedBifun_of_polyhedralBifun` — the same facts for the adjoint side, which
  `Saddle/Kernel.lean` uses for **Corollary 33.2.2**.
* `PolyhedralFn.add_linear`, `polyhedralFn_compLin`, `clConcave_eq_of_mem_domConcave` — three
  general polyhedral lemmas proved here for want of a better home; see the design notes.

## Design notes

**Three polyhedral lemmas are proved here that do not belong here.** `PolyhedralFn.add_linear`
(adding a linear functional preserves polyhedrality) belongs beside `PolyhedralFn.add` in
`Polyhedral/Function.lean`; `polyhedralFn_compLin` and `clConcave_eq_of_mem_domConcave` belong
beside `polyhedralFn_mapLin` and `PolyhedralFn.clFn_eq_of_mem_dom` in
`Optimization/Perturbation.lean`. They are here because Corollary 33.1.3 is the first place that
needs them.

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

/-! ### Corollary 33.1.2

`⟨Fu, x*⟩` and `K(u, ·)*` are inverse bijections. The two round trips are the two halves of
Theorem 33.1: `cl (Fu) = ⟨Fu, ·⟩*` going one way, and Fenchel–Moreau in the second variable going
the other. Each needs the closedness hypothesis on its own side — image-closedness of `F`,
convex-closedness of `K` — which is why both have to be named.

The sections below are cut finely so that each statement carries only the instances its own proof
uses: `saddleOfBifun` is closed for free on the `Y` side, `bifunOfSaddle` on the `X` side, and only
the two round trips need Fenchel–Moreau. -/

section SaddleOfBifun

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The saddle-function attached to a convex bifunction: Rockafellar's `⟨Fu, x*⟩`, read as a
function of the pair. This is `bracket` uncurried; it is named because Corollary 33.1.2 is a
statement about it as a map. -/
noncomputable def saddleOfBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) : U × Y → EReal :=
  fun p => bracket Bx F p.1 p.2

theorem saddleOfBifun_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (p : U × Y) :
    saddleOfBifun Bx F p = bracket Bx F p.1 p.2 := rfl

end SaddleOfBifun

section SaddleOfBifunClosed

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing Bx.flip] {F : Bifun U X}

/-- The saddle-function of a bifunction is convex-closed: every slice is a conjugate. -/
theorem convexClosedFn_saddleOfBifun : ConvexClosedFn (saddleOfBifun Bx F) :=
  convexClosedFn_iff.2 fun u => closedFn_bracket u

end SaddleOfBifunClosed

section SaddleOfBifunConvex

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] {F : Bifun U X}

/-- The saddle-function of a *convex* bifunction is concave-convex — Theorem 33.1. -/
theorem concaveConvexFn_saddleOfBifun (hF : ConvexBifun F) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    ConcaveConvexFn (saddleOfBifun Bx F) := concaveConvexFn_bracket hF Bx

end SaddleOfBifunConvex

section BifunOfSaddleImage

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace X] [IsTopologicalAddGroup X] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing Bx] {K : U × Y → EReal}

/-- The bifunction of a saddle-function is image-closed: every slice is a conjugate. -/
theorem imageClosedBifun_bifunOfSaddle : ImageClosedBifun (bifunOfSaddle Bx K) :=
  fun u => closedFn_conj (B := Bx.flip) (f := fun y => K (u, y))

end BifunOfSaddleImage

section Cor3312Right

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx.flip] {K : U × Y → EReal}

/-- **Corollary 33.1.2**, one round trip: a convex-closed concave-convex `K` is the saddle-function
of the bifunction it defines. -/
theorem saddleOfBifun_bifunOfSaddle (hK : ConcaveConvexFn K) (hcc : ConvexClosedFn K) :
    saddleOfBifun Bx (bifunOfSaddle Bx K) = K :=
  funext fun p => (bracket_bifunOfSaddle hK p).trans (congrFun hcc p)

end Cor3312Right

section Cor3312Left

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F : Bifun U X}

/-- **Corollary 33.1.2**, the other round trip: an image-closed convex bifunction is the
bifunction of the saddle-function it defines. -/
theorem bifunOfSaddle_saddleOfBifun (hF : ConvexBifun F) (hFi : ImageClosedBifun F) :
    bifunOfSaddle Bx (saddleOfBifun Bx F) = F :=
  funext fun u => (clFn_eq_conj_bracket hF u).symm.trans (hFi u)

end Cor3312Left

section Cor3312Equiv

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]

/-- **Rockafellar, Corollary 33.1.2**: `K (u, x*) = ⟨Fu, x*⟩` and `Fu = K(u, ·)*` are inverse
bijections between the image-closed convex bifunctions from `U` to `X` and the convex-closed
concave-convex functions on `U × Y`. -/
noncomputable def bifunSaddleEquiv :
    {F : Bifun U X // ConvexBifun F ∧ ImageClosedBifun F} ≃
      {K : U × Y → EReal // ConcaveConvexFn K ∧ ConvexClosedFn K} where
  toFun F := ⟨saddleOfBifun Bx F.1,
    concaveConvexFn_saddleOfBifun F.2.1 Bx, convexClosedFn_saddleOfBifun⟩
  invFun K := ⟨bifunOfSaddle Bx K.1,
    convexBifun_bifunOfSaddle K.2.1 Bx, imageClosedBifun_bifunOfSaddle⟩
  left_inv F := Subtype.ext (bifunOfSaddle_saddleOfBifun F.2.1 F.2.2)
  right_inv K := Subtype.ext (saddleOfBifun_bifunOfSaddle K.2.1 K.2.2)

end Cor3312Equiv

/-! ### The bracket of a polyhedral bifunction

For a polyhedral convex bifunction `F` both variables of the bracket sharpen from convex to
polyhedral. `⟨Fu, ·⟩` is polyhedral convex, being the conjugate of the polyhedral convex function
`F u`; `⟨F·, y⟩` is polyhedral *concave*, its negative `⨅ x ((Fu)(x) - ⟨x, y⟩)` being the image of
a polyhedral convex function on `U × X` under the projection `(u, x) ↦ u`. That is the proof of
concavity in the first variable, with "convex" replaced by "polyhedral" throughout.

Properness then does the work closedness does in the general correspondence: a proper polyhedral
convex bifunction is image-closed, because a polyhedral epigraph is closed and properness keeps the
slice from taking `-∞`. So `F` is recovered from its bracket, `Fu = ⟨Fu, ·⟩*`, with no closedness
hypothesis at all — the polyhedral form of `bifunSaddleEquiv`'s left inverse.

**"Polyhedral concave" is spelled `PolyhedralFn (fun u => -(⟨Fu, y⟩))`.** The library has no
predicate for a function whose *hypograph* is polyhedral, and one is not worth introducing for a
single clause: the negation is the definition. -/

section PolyhedralLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal}

/-- Adding a finite constant to an `EReal`, read as a condition on epigraph height.

The same statement is `Subgradient/Approx.lean`'s `add_coe_le_coe_iff` and `Saddle/Defs.lean`'s
private twin; none of the three files imports the others, and the lemma really belongs in
`Tdaf/Order/EReal.lean`. -/
private theorem add_coe_le_coe_iff {a : EReal} {c m : ℝ} :
    a + (c : EReal) ≤ (m : EReal) ↔ a ≤ ((m - c : ℝ) : EReal) := by
  rw [_root_.EReal.coe_sub, _root_.EReal.le_sub_iff_add_le (.inl (_root_.EReal.coe_ne_bot c))
    (.inl (_root_.EReal.coe_ne_top c))]

/-- **Adding a linear functional preserves polyhedrality.** The epigraph of `f + φ` is the preimage
of `epi f` under the shear `(x, μ) ↦ (x, μ - φ x)`, and `Polyhedral.comap` asks for nothing beyond
a real vector space — no finite dimension, no topology.

This belongs beside `PolyhedralFn.add` in `Polyhedral/Function.lean`; it is here because
Corollary 33.1.3 is the first place that needs it. -/
theorem PolyhedralFn.add_linear (hf : PolyhedralFn f) (φ : E →ₗ[ℝ] ℝ) :
    PolyhedralFn (fun x => f x + ((φ x : ℝ) : EReal)) := by
  have hepi : epi (fun x => f x + ((φ x : ℝ) : EReal))
      = (LinearMap.prod (LinearMap.fst ℝ E ℝ)
          (LinearMap.snd ℝ E ℝ - φ.comp (LinearMap.fst ℝ E ℝ))) ⁻¹' epi f := by
    ext q
    exact add_coe_le_coe_iff
  change Polyhedral (epi _)
  rw [hepi]
  exact Polyhedral.comap hf _

/-- **Composing with a linear map preserves polyhedrality.** `epi (g A)` is `epi g` pulled back
along `(x, μ) ↦ (A x, μ)`, and a preimage of a polyhedral set under a linear map is polyhedral.

This belongs beside `polyhedralFn_mapLin` in `Optimization/Perturbation.lean`, next to the image
half; it is here because the adjoint bifunction is the first place that needs it. -/
theorem polyhedralFn_compLin {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : G → EReal} (hg : PolyhedralFn g) (A : E →ₗ[ℝ] G) : PolyhedralFn (compLin g A) := by
  change Polyhedral (epi (compLin g A))
  rw [epi_compLin]
  exact Polyhedral.comap hg _

end PolyhedralLinear

section PolyhedralBracket

variable {U X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : Bifun U X}

omit [FiniteDimensional ℝ U] in
/-- **Rockafellar, Corollary 33.1.3**, first clause: `⟨Fu, ·⟩` is a polyhedral convex function of
`y` for each `u`. This is Theorem 19.2 applied to the slice `F u`, which Theorem 29.2 says is
polyhedral. -/
theorem polyhedralFn_bracket (hF : PolyhedralBifun F) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (u : U) :
    PolyhedralFn (bracket Bx F u) := by
  rw [bracket_eq_conj]
  exact PolyhedralFn.conj (B := Bx) (PolyhedralBifun.polyhedralFn_apply hF u)

/-- The bookkeeping of Corollary 33.1.3's concavity clause, with the linear functional
`(u, x) ↦ -⟨x, y⟩` abstracted so that it can be written down once. -/
private theorem polyhedralFn_neg_bracket_aux (hF : PolyhedralBifun F)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (y : Y) (φ : (U × X) →ₗ[ℝ] ℝ)
    (hφ : ∀ p : U × X, φ p = -(Bx p.2 y : ℝ)) :
    PolyhedralFn (fun u => -(bracket Bx F u y)) := by
  have hval : ∀ u : U, (⨅ x : X, (graphFn F (u, x) + ((φ (u, x) : ℝ) : EReal)))
      = -(bracket Bx F u y) := by
    intro u
    rw [bracket_apply, Tdaf.EReal.neg_iSup]
    refine iInf_congr fun x => ?_
    rw [_root_.EReal.neg_sub (.inl (_root_.EReal.coe_ne_bot _))
        (.inl (_root_.EReal.coe_ne_top _)), hφ (u, x), _root_.EReal.coe_neg,
      add_comm (graphFn F (u, x))]
    rfl
  have hfun : (fun u => -(bracket Bx F u y))
      = mapLin (LinearMap.fst ℝ U X) (fun p : U × X => graphFn F p + ((φ p : ℝ) : EReal)) := by
    funext u
    rw [mapLin_fst_apply]
    exact (hval u).symm
  rw [hfun]
  exact polyhedralFn_mapLin (PolyhedralFn.add_linear hF φ) _

/-- **Rockafellar, Corollary 33.1.3**, second clause: `⟨F·, y⟩` is a polyhedral *concave* function
of `u` for each `y`, i.e. its negative is polyhedral convex.

`-⟨Fu, y⟩ = ⨅ x ((Fu)(x) - ⟨x, y⟩)` is the image of a polyhedral convex function on `U × X` under
the projection `(u, x) ↦ u`, and Corollary 19.3.1 says such an image is polyhedral. -/
theorem polyhedralFn_neg_bracket (hF : PolyhedralBifun F) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (y : Y) :
    PolyhedralFn (fun u => -(bracket Bx F u y)) :=
  polyhedralFn_neg_bracket_aux hF Bx y ((-(Bx.flip y)).comp (LinearMap.snd ℝ U X)) fun _ => rfl

omit [FiniteDimensional ℝ U] in
/-- **Rockafellar, Corollary 33.1.3**, third clause, first half: a *proper* polyhedral convex
bifunction is image-closed. Each slice `F u` is polyhedral, hence has a closed epigraph, and
properness of the graph function keeps it from taking `-∞`; `ClosedFn` follows.

This is the polyhedral substitute for the closedness hypothesis of Corollary 33.1.2. -/
theorem imageClosedBifun_of_polyhedralBifun (hF : PolyhedralBifun F) (hp : Proper (graphFn F)) :
    ImageClosedBifun F := fun u =>
  PolyhedralFn.closedFn (PolyhedralBifun.polyhedralFn_apply hF u) fun x => hp.ne_bot (u, x)

omit [FiniteDimensional ℝ U] in
/-- **Rockafellar, Corollary 33.1.3**, third clause: a proper polyhedral convex bifunction is
recovered from its bracket, `Fu = ⟨Fu, ·⟩*`. -/
theorem eq_conj_bracket_of_polyhedralBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    (hF : PolyhedralBifun F) (hp : Proper (graphFn F)) (u : U) :
    F u = conj Bx.flip (bracket Bx F u) :=
  (imageClosedBifun_of_polyhedralBifun hF hp u).symm.trans
    (clFn_eq_conj_bracket (PolyhedralBifun.convexBifun hF) u)

omit [FiniteDimensional ℝ U] in
/-- **Rockafellar, Corollary 33.1.3**, third clause in the book's own notation:
`(Fu)(x) = sup_y {⟨x, y⟩ - ⟨Fu, y⟩}`. -/
theorem eq_iSup_sub_bracket_of_polyhedralBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] (hF : PolyhedralBifun F) (hp : Proper (graphFn F)) (u : U) (x : X) :
    F u x = ⨆ y : Y, ((Bx x y : ℝ) : EReal) - bracket Bx F u y :=
  congrFun (eq_conj_bracket_of_polyhedralBifun Bx hF hp u) x

end PolyhedralBracket

/-! ### The bracket of the adjoint of a polyhedral bifunction

The adjoint `F*` of a polyhedral convex bifunction is polyhedral concave: its negated graph
function is a conjugate composed with the linear reflection `(y, v) ↦ (-v, y)`, and both operations
preserve polyhedrality. The concave bracket `⟨u, F* y⟩` is then polyhedral convex in `y` for each
`u`, by the same partial-minimisation argument that makes `⟨Fu, y⟩` polyhedral concave in `u`.

Those two facts, with the observation that a polyhedral function agrees with its closure on the
whole of its effective domain, are what push the equality of the two brackets out from the relative
interior of an effective domain to all of it. -/

section PolyhedralConcaveClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {g : E → EReal}

/-- **A polyhedral concave function agrees with its closure throughout its effective domain**, not
merely on the relative interior of it. Mirror of `PolyhedralFn.clFn_eq_of_mem_dom`, obtained from
it by negating twice.

This belongs beside `PolyhedralFn.clFn_eq_of_mem_dom` in `Optimization/Perturbation.lean`. -/
theorem clConcave_eq_of_mem_domConcave (hg : PolyhedralFn fun z => -(g z)) {x : E}
    (hx : x ∈ domConcave g) : clConcave g x = g x := by
  have hmem : x ∈ dom fun z => -(g z) := by
    rw [← domConcave_eq_dom_neg]
    exact hx
  rw [clConcave_apply, PolyhedralFn.clFn_eq_of_mem_dom hg hmem, neg_neg]

end PolyhedralConcaveClosure

section PolyhedralAdjoint

variable {U V X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : Bifun U X}

/-- **A proper polyhedral convex bifunction is closed.** Its graph function has a polyhedral, hence
closed, epigraph, and properness rules out the `-∞` branch of `clFn`. -/
theorem closedBifun_of_polyhedralBifun (hF : PolyhedralBifun F) (hp : Proper (graphFn F)) :
    ClosedBifun F := PolyhedralFn.closedFn hF hp.ne_bot

/-- **The adjoint of a polyhedral convex bifunction is polyhedral concave.** `-F*` is the conjugate
of the graph function composed with the reflection `(y, v) ↦ (-v, y)`: Theorem 19.2 makes the
conjugate polyhedral, and `polyhedralFn_compLin` carries it through the reflection.

Neither properness nor closedness is needed, exactly as in the concavity half of Theorem 30.1. -/
theorem polyhedralFn_neg_graphFn_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : PolyhedralBifun F) :
    PolyhedralFn fun q : Y × V => -(graphFn (adjointBifun Bu Bx F) q) := by
  have h : (fun q : Y × V => -(graphFn (adjointBifun Bu Bx F) q))
      = compLin (conj (prodPairing Bu Bx) (graphFn F)) (adjointSwap V Y) := by
    funext q
    rw [graphFn_adjointBifun, neg_neg]
  rw [h]
  exact polyhedralFn_compLin (PolyhedralFn.conj (B := prodPairing Bu Bx) hF) _

end PolyhedralAdjoint

section ConcaveBracketDom

variable {U V Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- **The effective domain of `y ↦ ⟨u, G y⟩` is `dom G`**, for every `u`. The concave bracket is
`+∞` exactly where the slice `G y` is identically `-∞`; this is the mirror of
`domConcave_bracket`. -/
theorem dom_concaveBracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Bifun Y V) (u : U) :
    dom (fun y => concaveBracket Bu G u y) = domConcaveBifun G := by
  ext y
  change concaveConj Bu.flip (G y) u < ⊤ ↔ ∃ v, G y v ≠ ⊥
  rw [lt_top_iff_ne_top, ne_eq, concaveConj_eq_top_iff, not_forall]

end ConcaveBracketDom

section PolyhedralConcaveBracket

variable {U V Y : Type*} [AddCommGroup U] [Module ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] {G : Bifun Y V}

/-- The bookkeeping of `polyhedralFn_concaveBracket`, with the linear functional `(y, v) ↦ ⟨u, v⟩`
abstracted so that it can be written down once. -/
private theorem polyhedralFn_concaveBracket_aux
    (hG : PolyhedralFn fun q : Y × V => -(graphFn G q)) (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u : U)
    (ψ : (Y × V) →ₗ[ℝ] ℝ) (hψ : ∀ q : Y × V, ψ q = (Bu u q.2 : ℝ)) :
    PolyhedralFn (fun y => concaveBracket Bu G u y) := by
  have hval : ∀ y : Y, (⨅ v : V, (-(graphFn G (y, v)) + ((ψ (y, v) : ℝ) : EReal)))
      = concaveBracket Bu G u y := by
    intro y
    rw [concaveBracket_apply]
    refine iInf_congr fun v => ?_
    rw [hψ (y, v), sub_eq_add_neg, add_comm ((Bu u v : ℝ) : EReal) (-(G y v))]
    rfl
  have hfun : (fun y => concaveBracket Bu G u y)
      = mapLin (LinearMap.fst ℝ Y V)
        (fun q : Y × V => -(graphFn G q) + ((ψ q : ℝ) : EReal)) := by
    funext y
    rw [mapLin_fst_apply]
    exact (hval y).symm
  rw [hfun]
  exact polyhedralFn_mapLin (PolyhedralFn.add_linear hG ψ) _

/-- **The concave bracket of a polyhedral concave bifunction is polyhedral convex** in its second
variable: `⟨u, G y⟩ = ⨅ v (⟨u, v⟩ - (G y)(v))` is the image of a polyhedral convex function on
`Y × V` under the projection `(y, v) ↦ y`, and Corollary 19.3.1 says such an image is
polyhedral. -/
theorem polyhedralFn_concaveBracket (hG : PolyhedralFn fun q : Y × V => -(graphFn G q))
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u : U) : PolyhedralFn (fun y => concaveBracket Bu G u y) :=
  polyhedralFn_concaveBracket_aux hG Bu u ((Bu u).comp (LinearMap.snd ℝ Y V)) fun _ => rfl

end PolyhedralConcaveBracket

/-! ### Corollary 33.3.2

`cl₁` and `cl₂` are inverse bijections between the lower closed and the upper closed
concave-convex functions. The two round trips are `LowerClosedFn` and `UpperClosedFn` *by
definition* — `lowerCl = cl₂ ∘ cl₁` and `upperCl = cl₁ ∘ cl₂` — so all the corollary needs is that
each operator lands in the other class, which is the same definitional unfolding once more. -/

section Cor3332

variable {U Y : Type*} [TopologicalSpace U] [TopologicalSpace Y] {K : U × Y → EReal}

/-- `cl₁` of a lower closed saddle-function is upper closed. -/
theorem upperClosedFn_partialCl₁ (h : LowerClosedFn K) : UpperClosedFn (partialCl₁ K) := by
  change partialCl₁ (partialCl₂ (partialCl₁ K)) = partialCl₁ K
  rw [← lowerCl_def, lowerClosedFn_iff.1 h]

/-- `cl₂` of an upper closed saddle-function is lower closed. -/
theorem lowerClosedFn_partialCl₂ (h : UpperClosedFn K) : LowerClosedFn (partialCl₂ K) := by
  change partialCl₂ (partialCl₁ (partialCl₂ K)) = partialCl₂ K
  rw [← upperCl_def, upperClosedFn_iff.1 h]

/-- `cl₂ cl₁ K = K` for a lower closed `K` — the definition, spelled out. -/
theorem partialCl₂_partialCl₁_of_lowerClosedFn (h : LowerClosedFn K) :
    partialCl₂ (partialCl₁ K) = K := h

/-- `cl₁ cl₂ K = K` for an upper closed `K` — the definition, spelled out. -/
theorem partialCl₁_partialCl₂_of_upperClosedFn (h : UpperClosedFn K) :
    partialCl₁ (partialCl₂ K) = K := h

end Cor3332

section Cor3332Equiv

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]

/-- **Rockafellar, Corollary 33.3.2**: `K̄ = cl₁ K̲` and `K̲ = cl₂ K̄` are inverse bijections
between the lower closed and the upper closed concave-convex functions on `U × Y`.

The two pairings are the ones Corollary 33.1.1 needs: `Bu` to know that `cl₁` preserves
concave-convexity, `Bx` for `cl₂`. Neither appears in either closedness condition. -/
noncomputable def lowerUpperClosedEquiv (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx.flip] :
    {K : U × Y → EReal // ConcaveConvexFn K ∧ LowerClosedFn K} ≃
      {K : U × Y → EReal // ConcaveConvexFn K ∧ UpperClosedFn K} where
  toFun K := ⟨partialCl₁ K.1, concaveConvexFn_partialCl₁ Bu K.2.1,
    upperClosedFn_partialCl₁ K.2.2⟩
  invFun K := ⟨partialCl₂ K.1, concaveConvexFn_partialCl₂ Bx K.2.1,
    lowerClosedFn_partialCl₂ K.2.2⟩
  left_inv K := Subtype.ext (partialCl₂_partialCl₁_of_lowerClosedFn K.2.2)
  right_inv K := Subtype.ext (partialCl₁_partialCl₂_of_upperClosedFn K.2.2)

end Cor3332Equiv

end Tdaf.ConvexAnalysis

