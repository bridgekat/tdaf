/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Saddle.Subgradient
import Tdaf.Analysis.Convex.Subgradient.Monotone

/-!
# Existence of saddle-values and saddle-points

`Saddle/Conjugate.lean` proves the `D*` halves of Theorem 37.2, Corollary 37.2.1, Theorem 37.3 and
Corollary 37.3.1, and leaves the `C*` halves open; `Saddle/Subgradient.lean` proves Theorem 37.6
against the hypothesis `(0, 0) ∈ int (dom K*)`. This module supplies the missing halves and turns
both theorems into statements about `K` alone.

The device is the involution `saddleSwap K (y, u) = -K (u, y)`, which exchanges the two variables
of a saddle-function. Under it the equivalence class `Ω (F)` becomes the class `Ω (F♯)` for the
**negated flipped pairings** `-Bx.flip`, `-Bu.flip`, where `F♯` is the bifunction
`(F♯ y) v = -(F* y)(v)`; and the lower and upper conjugates are exchanged. Every `C*` statement is
therefore its `D*` companion read at the swapped data, and no new duality is needed.

## Main results

* `swapAdjointBifun`, `adjointBifun_swapAdjointBifun`, `saddleSwap_mem_bifunSaddleClass` — the
  swap dictionary: `saddleSwap` carries `Ω (F)` onto `Ω (F♯)`, and the adjoint of `F♯` is `-F`.
* `upperConjSaddle_saddleSwap`, `lowerConjSaddle_saddleSwap` — `saddleSwap` exchanges the two
  conjugates.
* `proper_graphFn_of_properSaddleFn` — a proper member of `Ω (F)` forces `Proper (graphFn F)`.
* `zero_mem_interior_dom₁_lowerConjSaddle_iff` — **Corollary 37.2.1**, the `C*` half.
* `hasSaddleValue_of_no_common_direction_of_recession_neg` — **Theorem 37.3**, condition (b).
* `hasSaddleValue_of_isBounded_dom₁` — **Corollary 37.3.1**, the half where `C` is bounded.
* `exists_isSaddlePoint_of_no_common_direction_of_recession` — **Theorem 37.6** with its
  hypotheses stated on `K` itself, as conditions (a) and (b) of Theorem 37.3.
* `exists_isSaddlePoint_of_isBounded_domSaddle`,
  `exists_maximin_eq_coe_of_isBounded_domSaddle` — **Corollary 37.6.1**.
* `saddleStructure_lowerSimpleExt`, `maximin_lowerSimpleExt`, `minimax_lowerSimpleExt`,
  `exists_bifunSaddleClass_lowerSimpleExt` — the transfer of §37 to a finite continuous
  concave-convex function on a closed `C × D`, through Corollaries 34.2.4 and 33.3.3.
* `biSup_biInf_eq_biInf_biSup_of_isBounded_right`, `..._left` — **Corollary 37.3.2**.
* `exists_saddlePoint_of_isBounded` — **Corollary 37.6.2**, the classical minimax theorem.
* `isBifunSubgradientPair_iff_mem_subgradient_graphFn` — **Theorem 37.5**, (c) ⇔ (d): `∂K` is the
  partial inversion of `∂f`, `f` the graph function of `F`.
* `isClosed_setOf_mem_saddleSubgradient` — **Corollary 37.5.1**, closedness clause.

## Design notes

**The swap needs the pairings negated, not merely flipped.** `saddleSwap` negates values, so the
linear terms `⟨u, v⟩ + ⟨x, y⟩` in the two conjugates come back with the opposite sign; only
`-Bx.flip` and `-Bu.flip` restore them. `isCompatiblePairing_neg` and `flip_neg` (in
`Saddle/Minimax.lean`, written for Theorem 36.5) are what make the negated pairings usable, and
`separatingRight_neg_flip` is the third lemma of that family.

**The bifunction of the swapped class is `F♯ = -F*` with its arguments exchanged, not `F_*^*`.**
`F_*^* = inverseBifun (adjointBifun Bu Bx F)` is a bifunction from `V` to `Y` and belongs to the
*conjugate* class `Ω (F_*^*)` on `V × X`; the swapped class lives on `Y × U` and its bifunction
goes from `Y` to `V`. The two differ by `flipBifun`, and `adjointBifun_neg_flipBifun` — a pure
reindexing of one infimum over a product — is what relates them, after which
`adjointBifun_swapAdjointBifun` is the biadjoint identity verbatim.

**`Proper (graphFn F)` had to be derived, not assumed.** Every §37 statement in
`Saddle/Conjugate.lean` and `Saddle/Subgradient.lean` takes it as a hypothesis, whereas
Corollary 34.2.4 and Theorem 34.3 deliver `ProperSaddleFn K`. The bridge is
`proper_graphFn_of_properSaddleFn`, and it needs both halves of properness: `dom₂ K ≠ ∅` rules out
`F u x = -∞` (which would make a bracket `+∞`), and `dom₁ K ≠ ∅` rules out `F ≡ +∞` (which would
make the upper bracket `-∞`).

**Theorem 37.5's (c) needs no hypothesis on `F` at all.** The equivalence between condition (d)
and `(-u*, v) ∈ ∂f (u, v*)` is Theorem 23.5 plus the identity `(F* v)(u*) = -f*(-u*, v)`
(`adjointBifun_eq_neg_conj_graphFn`), and both are unconditional; convexity and closedness enter
only when (a) is brought in, i.e. when a representative `K ∈ Ω (F)` is chosen.

**Corollary 37.3.2 is stated with `EReal`-valued extrema.** The book writes
`inf_D sup_C K = sup_C inf_D K` for a finite `K`, but with only one of `C`, `D` bounded the two
iterated extrema can be `±∞`, so the equality has to be read in `EReal`. Corollary 37.6.2, where
both sets are bounded, is stated with real inequalities exactly as the book displays them.

## What is not here

**Corollary 37.5.1's homeomorphism clause, and Corollary 37.5.2.** That the graph of `∂K` is
homeomorphic to `Rᵐ × Rⁿ` under `(u, v, u*, v*) ↦ (u - u*, v + v*)` is Corollary 31.5.1, and that
`(u, v) ↦ (-∂₁K, ∂₂K)` is maximal monotone is Corollary 31.5.2. Both corollaries are now proved,
in `Optimization/Prox.lean` — but only for `innerₗ E`, i.e. for a space carrying an
`InnerProductSpace ℝ` instance. Theorem 37.5 pairs `U × X` with `V × Y` through `prodPairing`, and
in Mathlib a product of inner-product spaces carries the *supremum* norm, not the Euclidean one, so
`U × X` is not an `InnerProductSpace` and the two corollaries cannot be instantiated here as they
stand. What is needed is `Optimization/Prox.lean` restated over a symmetric, positive-definite,
jointly continuous self-pairing `B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ` in place of `innerₗ E`;
`prodPairing (innerₗ U) (innerₗ X)` is such a pairing on `U × X`, and everything in that file — the
quadratic `w z = ½ B z z`, its subdifferential `{x - z}`, its recession function, and the
monotonicity inequality — is written in terms of `B` alone. The closedness clause of 37.5.1 *is*
here, since it is Theorem 24.4.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §24, §34, §36, §37.
-/

namespace Tdaf.ConvexAnalysis

/-! ### `saddleSwap` and the conjugate saddle-functions -/

section SwapNeg

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- Negating a difference whose minuend is a real number. -/
private theorem neg_coe_sub (r : ℝ) (z : EReal) :
    -(((r : ℝ) : EReal) - z) = z - ((r : ℝ) : EReal) := by
  induction z using EReal.rec with
  | bot => simp
  | coe s => norm_cast; ring
  | top => simp

/-- Reflecting both the real minuend and the `EReal` subtrahend. -/
private theorem coe_neg_sub_neg (r : ℝ) (z : EReal) :
    ((-r : ℝ) : EReal) - -z = z - ((r : ℝ) : EReal) := by
  induction z using EReal.rec with
  | bot => simp
  | coe s => norm_cast; ring
  | top => simp

omit [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X] in
/-- `saddleSwap` negates, so it reverses the pointwise order. -/
theorem saddleSwap_le_saddleSwap {K L : U × X → EReal} (h : K ≤ L) :
    saddleSwap L ≤ saddleSwap K :=
  fun q => EReal.neg_le_neg_iff.2 (h (q.2, q.1))

/-- **The adjoint commutes with `flipBifun` once both pairings are negated and exchanged.**

This is the identity of definitions behind the whole swap dictionary: `adjointBifun` is an
infimum over `U × X` of `F u x + ⟨u, v⟩ - ⟨x, y⟩`, and exchanging the two pairings while negating
both restores exactly that summand with the two bound variables exchanged. -/
theorem adjointBifun_neg_flipBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) :
    adjointBifun (-Bx) (-Bu) (flipBifun F) = flipBifun (adjointBifun Bu Bx F) := by
  funext v y
  rw [flipBifun_apply, adjointBifun_apply, adjointBifun_apply, iInf_prod, iInf_prod, iInf_comm]
  refine iInf_congr fun u => iInf_congr fun x => ?_
  rw [flipBifun_apply]
  congr 2
  simp only [LinearMap.neg_apply]
  ring

omit [AddCommGroup Y] [Module ℝ Y] in
/-- The bracket of `y ↦ -(G y ·)` at the negated flipped pairing is minus the concave bracket
of `G`. This is one of the two halves of the swap dictionary for equivalence classes. -/
theorem bracket_neg_flip_flipBifun_inverseBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Bifun Y V)
    (y : Y) (u : U) :
    bracket (-Bu.flip) (flipBifun (inverseBifun G)) y u = -(concaveBracket Bu G u y) := by
  rw [bracket_apply, concaveBracket_apply, Tdaf.EReal.neg_iInf]
  refine iSup_congr fun v => ?_
  rw [flipBifun_apply, inverseBifun_apply, neg_coe_sub]
  have hr : ((-Bu.flip) v u : ℝ) = -(Bu u v) := by
    simp only [LinearMap.neg_apply, LinearMap.flip_apply]
  rw [hr, coe_neg_sub_neg]

omit [AddCommGroup U] [Module ℝ U] in
/-- The mirror half: the concave bracket of `u ↦ -(H u ·)` at the negated flipped pairing is
minus the bracket of `H`. -/
theorem concaveBracket_neg_flip_flipBifun_inverseBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (H : Bifun U X)
    (y : Y) (u : U) :
    concaveBracket (-Bx.flip) (flipBifun (inverseBifun H)) y u = -(bracket Bx H u y) := by
  rw [concaveBracket_apply, bracket_apply, Tdaf.EReal.neg_iSup]
  refine iInf_congr fun x => ?_
  rw [flipBifun_apply, inverseBifun_apply, neg_coe_sub]
  have hr : ((-Bx.flip) y x : ℝ) = -(Bx x y) := by
    simp only [LinearMap.neg_apply, LinearMap.flip_apply]
  rw [hr, coe_neg_sub_neg]

end SwapNeg

/-! ### The class conjugate to `Ω (F)` seen through `saddleSwap` -/

section SwapClass

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The convex bifunction attached to the **swapped** saddle-function: `(F♯ y) v = -(F* y)(v)`.

`saddleSwap K` is a concave-convex function on `Y × U`, and Theorem 33.3 attaches a convex
bifunction from `Y` to `V` to its class; this is it. The two brackets of `F♯` at the negated
flipped pairings `-Bx.flip`, `-Bu.flip` are the negatives of the two brackets of `F`, exchanged
— which is exactly what `saddleSwap` does to the class `Ω (F)`. -/
noncomputable def swapAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun Y V :=
  flipBifun (inverseBifun (adjointBifun Bu Bx F))

@[simp] theorem swapAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (y : Y) (v : V) :
    swapAdjointBifun Bu Bx F y v = -(adjointBifun Bu Bx F y v) := rfl

/-- `F♯` is a convex bifunction: it is `F_*^*` with its two arguments exchanged. -/
theorem convexBifun_swapAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConvexBifun (swapAdjointBifun Bu Bx F) :=
  convexBifun_flipBifun (convexBifun_inverseBifun_adjointBifun Bu Bx F)

end SwapClass

section SwapClassClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]

/-- `F♯` is a closed bifunction, by Theorem 30.1 for the adjoint. -/
theorem closedBifun_swapAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsContinuousPairing Bu.flip]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsContinuousPairing Bx.flip] (F : Bifun U X) :
    ClosedBifun (swapAdjointBifun Bu Bx F) :=
  closedBifun_flipBifun (closedBifun_inverseBifun_adjointBifun Bu Bx F)

end SwapClassClosed

section SwapClassMem

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {F : Bifun U X} {K : U × Y → EReal}

/-- **The adjoint of `F♯` is `-F`**, which is the biadjoint identity `(F_*^*)^* = F_*` read
through `adjointBifun_neg_flipBifun`. -/
theorem adjointBifun_swapAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] (hF : ConvexBifun F)
    (hcl : ClosedBifun F) :
    adjointBifun (-Bx.flip) (-Bu.flip) (swapAdjointBifun Bu Bx F) = flipBifun (inverseBifun F) := by
  rw [swapAdjointBifun, adjointBifun_neg_flipBifun Bu.flip Bx.flip,
    adjointBifun_flip_inverseBifun_adjointBifun Bu Bx hF hcl]

/-- **The swap dictionary for equivalence classes**: `saddleSwap` carries `Ω (F)` onto `Ω (F♯)`
at the negated flipped pairings. Every §37 statement about the first variable is therefore the
corresponding statement about the second variable, read here. -/
theorem saddleSwap_mem_bifunSaddleClass (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) :
    saddleSwap K ∈ bifunSaddleClass (-Bx.flip) (-Bu.flip) (swapAdjointBifun Bu Bx F) := by
  have h1 : (fun p : Y × U => bracket (-Bu.flip) (swapAdjointBifun Bu Bx F) p.1 p.2)
      = saddleSwap fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2 := by
    funext p
    rw [swapAdjointBifun, bracket_neg_flip_flipBifun_inverseBifun, saddleSwap_apply]
  have h2 : (fun p : Y × U => concaveBracket (-Bx.flip)
        (adjointBifun (-Bx.flip) (-Bu.flip) (swapAdjointBifun Bu Bx F)) p.1 p.2)
      = saddleSwap fun p : U × Y => bracket Bx F p.1 p.2 := by
    funext p
    rw [adjointBifun_swapAdjointBifun Bu Bx hF hcl,
      concaveBracket_neg_flip_flipBifun_inverseBifun, saddleSwap_apply]
  rw [mem_bifunSaddleClass] at hK
  rw [mem_bifunSaddleClass, h1, h2]
  exact ⟨saddleSwap_le_saddleSwap hK.2, saddleSwap_le_saddleSwap hK.1⟩

end SwapClassMem

/-! ### The two conjugates of `saddleSwap K` -/

section SwapConj

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **The upper conjugate of `saddleSwap K` is the swap of the lower conjugate of `K`.**
Negating both pairings turns a supremum-of-infima into an infimum-of-suprema. -/
theorem upperConjSaddle_saddleSwap (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × Y → EReal) :
    upperConjSaddle (-Bx.flip) (-Bu.flip) (saddleSwap K)
      = saddleSwap (lowerConjSaddle Bu Bx K) := by
  funext q
  rw [upperConjSaddle_apply, saddleSwap_apply, lowerConjSaddle_apply, Tdaf.EReal.neg_iSup]
  refine iInf_congr fun y => ?_
  rw [Tdaf.EReal.neg_iInf]
  refine iSup_congr fun u => ?_
  have hr : ((-Bx.flip) y q.1 + (-Bu.flip) q.2 u : ℝ) = -(Bu u q.2 + Bx q.1 y) := by
    simp only [LinearMap.neg_apply, LinearMap.flip_apply]
    ring
  rw [hr, saddleSwap_apply, coe_neg_sub_neg, neg_coe_sub]

/-- **The lower conjugate of `saddleSwap K` is the swap of the upper conjugate of `K`.** -/
theorem lowerConjSaddle_saddleSwap (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × Y → EReal) :
    lowerConjSaddle (-Bx.flip) (-Bu.flip) (saddleSwap K)
      = saddleSwap (upperConjSaddle Bu Bx K) := by
  funext q
  rw [lowerConjSaddle_apply, saddleSwap_apply, upperConjSaddle_apply, Tdaf.EReal.neg_iInf]
  refine iSup_congr fun u => ?_
  rw [Tdaf.EReal.neg_iSup]
  refine iInf_congr fun y => ?_
  have hr : ((-Bx.flip) y q.1 + (-Bu.flip) q.2 u : ℝ) = -(Bu u q.2 + Bx q.1 y) := by
    simp only [LinearMap.neg_apply, LinearMap.flip_apply]
    ring
  rw [hr, saddleSwap_apply, coe_neg_sub_neg, neg_coe_sub]

end SwapConj

/-! ### Properness of the bifunction behind a proper class -/

section ProperGraph

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

/-- **A proper member forces a proper bifunction.** Rockafellar never separates the two
propernesses — the equivalence class `Ω (F)` of a closed proper convex bifunction consists of
proper saddle-functions and conversely — but the §37 API asks for `Proper (graphFn F)` while
Theorem 34.3 and Corollary 34.2.4 deliver `ProperSaddleFn K`, so the bridge has to be crossed
explicitly.

Proof idea: `F u x = ⊥` would make the bracket `⟨Fu, y⟩` identically `+∞`, contradicting
`dom₂ K ≠ ∅` through `⟨Fu, ·⟩ ≤ K (u, ·)`; and `F ≡ +∞` would make the adjoint `+∞` and hence the
upper bracket `-∞`, contradicting `dom₁ K ≠ ∅` through `K ≤ ⟨·, F*·⟩`. -/
theorem proper_graphFn_of_properSaddleFn (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hK : K ∈ bifunSaddleClass Bu Bx F) (hp : ProperSaddleFn K) : Proper (graphFn F) := by
  obtain ⟨u₀, hu₀⟩ := hp.dom₁_nonempty
  obtain ⟨y₀, hy₀⟩ := hp.dom₂_nonempty
  rw [mem_bifunSaddleClass] at hK
  have hbot : ∀ q : U × X, graphFn F q ≠ ⊥ := by
    rintro ⟨u, x⟩ hq
    have hle : ((Bx x y₀ : ℝ) : EReal) - F u x ≤ bracket Bx F u y₀ :=
      le_iSup (fun x => ((Bx x y₀ : ℝ) : EReal) - F u x) x
    have htop : ((Bx x y₀ : ℝ) : EReal) - F u x = ⊤ := by
      rw [show F u x = (⊥ : EReal) from hq]
      simp
    rw [htop] at hle
    exact absurd (top_le_iff.1 (hle.trans (hK.1 (u, y₀)))) (ne_of_lt (hy₀ u))
  refine ⟨?_, hbot⟩
  have hlt : ⊥ < concaveBracket Bu (adjointBifun Bu Bx F) u₀ y₀ := lt_of_lt_of_le (hu₀ y₀)
    (hK.2 (u₀, y₀))
  have hterm : (⊥ : EReal) < ((Bu u₀ 0 : ℝ) : EReal) - adjointBifun Bu Bx F y₀ 0 := by
    refine lt_of_lt_of_le hlt ?_
    rw [concaveBracket_apply]
    exact iInf_le (fun v => ((Bu u₀ v : ℝ) : EReal) - adjointBifun Bu Bx F y₀ v) 0
  have hne : adjointBifun Bu Bx F y₀ 0 ≠ ⊤ := by
    intro hcon
    rw [hcon] at hterm
    simp at hterm
  obtain ⟨q, hq⟩ := iInf_lt_iff.1 (lt_of_le_of_ne le_top hne)
  refine ⟨q, ?_⟩
  by_contra hcon
  rw [mem_dom, not_lt, top_le_iff] at hcon
  rw [show F q.1 q.2 = (⊤ : EReal) from hcon] at hq
  simp at hq

end ProperGraph

/-! ### Corollary 37.2.1 and Theorem 37.3, the `C*` half -/

section SeparatingNeg

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Negating and flipping a pairing exchanges its two separation properties. -/
theorem separatingRight_neg_flip {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} (hB : B.SeparatingLeft) :
    (-B.flip).SeparatingRight := by
  intro x hx
  refine hB x fun y => ?_
  have h := hx y
  simpa using h

end SeparatingNeg

section Cor3721Fst

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

omit [FiniteDimensional ℝ X] in
/-- **Rockafellar, Corollary 37.2.1** (the `C*` half): the origin is an interior point of `C*` if
and only if the convex functions `-K (·, v)`, for `v ∈ ri D`, have no common direction of
recession.

This is the `D*` half read at `saddleSwap K`, whose class is `Ω (F♯)` for the negated flipped
pairings (`saddleSwap_mem_bifunSaddleClass`); `upperConjSaddle_saddleSwap` identifies the second
effective domain of the swapped upper conjugate with `C*`. -/
theorem zero_mem_interior_dom₁_lowerConjSaddle_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hB : Bu.SeparatingLeft)
    (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (hKcc : ConcaveConvexFn K) (hp : ProperSaddleFn K) (hs : SaddleStructure K) :
    (0 : V) ∈ interior (dom₁ (lowerConjSaddle Bu Bx K)) ↔
      ∀ z : U, z ≠ 0 → ∃ y ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, y))) z := by
  have hbu : IsCompatiblePairing (-Bu.flip) := isCompatiblePairing_neg Bu.flip
  have hbx : IsCompatiblePairing (-Bx.flip) := isCompatiblePairing_neg Bx.flip
  have hbuf : IsCompatiblePairing (-Bu.flip).flip := by
    rw [flip_neg, LinearMap.flip_flip]
    exact isCompatiblePairing_neg Bu
  have hswap := saddleSwap_mem_bifunSaddleClass Bu Bx hF hcl hK
  have hprF : Proper (graphFn (swapAdjointBifun Bu Bx F)) :=
    proper_graphFn_of_properSaddleFn (-Bx.flip) (-Bu.flip) hswap hp.saddleSwap
  have hmain := zero_mem_interior_dom₂_upperConjSaddle_iff (-Bx.flip) (-Bu.flip)
    (separatingRight_neg_flip hB) (convexBifun_swapAdjointBifun Bu Bx F)
    (closedBifun_swapAdjointBifun Bu Bx F) hprF hswap (concaveConvexFn_saddleSwap hKcc)
    (by rw [dom₂_saddleSwap]; exact hp.dom₁_nonempty) hs.2
  rw [upperConjSaddle_saddleSwap, dom₂_saddleSwap, dom₁_saddleSwap] at hmain
  exact hmain

/-- **Rockafellar, Theorem 37.3**, condition (b): if the convex functions `-K (·, v)` for
`v ∈ ri D` have no common direction of recession, then the saddle-value of `K` exists. -/
theorem hasSaddleValue_of_no_common_direction_of_recession_neg (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hB : Bu.SeparatingLeft)
    (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (hKcc : ConcaveConvexFn K) (hp : ProperSaddleFn K) (hs : SaddleStructure K)
    (hrec : ∀ z : U, z ≠ 0 → ∃ y ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, y))) z) :
    HasSaddleValue K := by
  refine hasSaddleValue_of_mem_relint_dom₁_lowerConjSaddle Bu Bx hF hcl
    (proper_graphFn_of_properSaddleFn Bu Bx hK hp) hK ?_
  exact interior_subset_intrinsicInterior
    ((zero_mem_interior_dom₁_lowerConjSaddle_iff Bu Bx hB hF hcl hK hKcc hp hs).2 hrec)

/-- **Rockafellar, Corollary 37.3.1** (the `C` half): if the first effective domain of `K` is
bounded, the saddle-value of `K` exists. -/
theorem hasSaddleValue_of_isBounded_dom₁ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hB : Bu.SeparatingLeft) (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) (hs : SaddleStructure K)
    (hbd : Bornology.IsBounded (dom₁ K)) : HasSaddleValue K := by
  refine hasSaddleValue_of_no_common_direction_of_recession_neg Bu Bx hB hF hcl hK hKcc hp hs
    fun z hz => ?_
  obtain ⟨y, hy⟩ := Convex.relint_nonempty hKcc.convex_dom₂ hp.dom₂_nonempty
  have hy' : y ∈ ri (dom₁ (saddleSwap K)) := by rwa [dom₁_saddleSwap]
  have hdom : dom (fun u => -(K (u, y))) = dom₁ K := by
    have h := hs.2.dom_slice y hy'
    rwa [dom₂_saddleSwap] at h
  exact ⟨y, hy, lt_recessionFn_of_isBounded_dom (by rw [hdom]; exact hp.dom₁_nonempty)
    (by rw [hdom]; exact hbd) hz⟩

end Cor3721Fst

/-! ### Theorem 37.6 and Corollary 37.6.1 -/

section Thm376

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

/-- **Rockafellar, Theorem 37.6**: if conditions (a) and (b) of Theorem 37.3 both hold, `K` has a
saddle-point.

Both conditions are translated by Corollary 37.2.1 into `0 ∈ int C*` and `0 ∈ int D*`, and
`exists_isSaddlePoint_of_zero_mem_interior_dom_upperConjSaddle` — Corollary 37.5.3 through
Theorem 37.4 — concludes. -/
theorem exists_isSaddlePoint_of_no_common_direction_of_recession (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hBu : Bu.SeparatingLeft)
    (hBx : Bx.SeparatingRight) (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SaddleStructure K)
    (hrec₂ : ∀ w : Y, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun y => K (u, y)) w)
    (hrec₁ : ∀ z : U, z ≠ 0 → ∃ y ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, y))) z) :
    ∃ q, IsSaddlePoint K q := by
  have hpr : Proper (graphFn F) := proper_graphFn_of_properSaddleFn Bu Bx hK hp
  have h₁ : (0 : V) ∈ interior (dom₁ (upperConjSaddle Bu Bx K)) := by
    rw [← dom₁_conjSaddle_eq Bu Bx hF hcl hpr hK]
    exact (zero_mem_interior_dom₁_lowerConjSaddle_iff Bu Bx hBu hF hcl hK hKcc hp hs).2 hrec₁
  have h₂ : (0 : X) ∈ interior (dom₂ (upperConjSaddle Bu Bx K)) :=
    (zero_mem_interior_dom₂_upperConjSaddle_iff Bu Bx hBx hF hcl hpr hK hKcc hp.dom₂_nonempty
      hs.1).2 hrec₂
  exact exists_isSaddlePoint_of_zero_mem_interior_dom_upperConjSaddle Bu Bx hF hcl hpr hK h₁ h₂

/-- **Rockafellar, Corollary 37.6.1**: if both halves of the effective domain of `K` are bounded,
`K` has a saddle-point. -/
theorem exists_isSaddlePoint_of_isBounded_domSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hBu : Bu.SeparatingLeft)
    (hBx : Bx.SeparatingRight) (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SaddleStructure K) (hbd₁ : Bornology.IsBounded (dom₁ K))
    (hbd₂ : Bornology.IsBounded (dom₂ K)) : ∃ q, IsSaddlePoint K q := by
  refine exists_isSaddlePoint_of_no_common_direction_of_recession Bu Bx hBu hBx hF hcl hK hKcc
    hp hs (fun w hw => ?_) fun z hz => ?_
  · obtain ⟨u, hu⟩ := Convex.relint_nonempty hKcc.convex_dom₁ hp.dom₁_nonempty
    have hdom : dom (fun y => K (u, y)) = dom₂ K := hs.1.dom_slice u hu
    exact ⟨u, hu, lt_recessionFn_of_isBounded_dom (by rw [hdom]; exact hp.dom₂_nonempty)
      (by rw [hdom]; exact hbd₂) hw⟩
  · obtain ⟨y, hy⟩ := Convex.relint_nonempty hKcc.convex_dom₂ hp.dom₂_nonempty
    have hy' : y ∈ ri (dom₁ (saddleSwap K)) := by rwa [dom₁_saddleSwap]
    have hdom : dom (fun u => -(K (u, y))) = dom₁ K := by
      have h := hs.2.dom_slice y hy'
      rwa [dom₂_saddleSwap] at h
    exact ⟨y, hy, lt_recessionFn_of_isBounded_dom (by rw [hdom]; exact hp.dom₁_nonempty)
      (by rw [hdom]; exact hbd₁) hz⟩

/-- **Rockafellar, Corollary 37.6.1**, second clause: the saddle-value is then finite. It is a
value of `K` at a saddle-point, and a proper saddle-function is finite on its effective
domain (Corollary 36.3.1). -/
theorem exists_maximin_eq_coe_of_isBounded_domSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hBu : Bu.SeparatingLeft)
    (hBx : Bx.SeparatingRight) (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SaddleStructure K) (hbd₁ : Bornology.IsBounded (dom₁ K))
    (hbd₂ : Bornology.IsBounded (dom₂ K)) : ∃ r : ℝ, maximin K = (r : EReal) := by
  obtain ⟨q, hq⟩ := exists_isSaddlePoint_of_isBounded_domSaddle Bu Bx hBu hBx hF hcl hK hKcc hp
    hs hbd₁ hbd₂
  exact hq.exists_maximin_eq_coe hp

end Thm376

/-! ### Corollaries 37.3.2 and 37.6.2: a finite continuous saddle-function on `C × D` -/

section SimpleExt

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {C : Set U} {D : Set Y} {K : U × Y → ℝ}

omit [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- **Rockafellar, Theorem 34.3 for the lower simple extension**: it is a closed proper
concave-convex function, so it has the full structural description. -/
theorem saddleStructure_lowerSimpleExt (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    SaddleStructure (lowerSimpleExt C D K) :=
  (closedSaddleFn_iff_saddleStructure (concaveConvexFn_lowerSimpleExt hC hconv hconc)
      (properSaddleFn_lowerSimpleExt hCne hDne)).1
    (closedSaddleFn_of_mem_saddleClass_simpleExt hCcl hDcl hCne hDne hcontD hcontC
      (mem_saddleClass_left (partialCl₂_upperSimpleExt hDcl hDne hcontD)))

omit [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- **Rockafellar, Theorem 36.3** for the lower simple extension: its `sup inf` over the whole
space is the book's `sup inf` over `C × D`. -/
theorem maximin_lowerSimpleExt (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    maximin (lowerSimpleExt C D K) = ⨆ u ∈ C, ⨅ x ∈ D, ((K (u, x) : ℝ) : EReal) := by
  rw [maximin_eq_biSup_biInf (concaveConvexFn_lowerSimpleExt hC hconv hconc)
      (saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC)
      (properSaddleFn_lowerSimpleExt hCne hDne),
    dom₁_lowerSimpleExt (K := K) hDne, dom₂_lowerSimpleExt (K := K) hCne]
  exact iSup_congr fun u => iSup_congr fun hu => iInf_congr fun x => iInf_congr fun hx =>
    lowerSimpleExt_of_mem (p := (u, x)) hu hx

omit [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- **Rockafellar, Theorem 36.3** for the lower simple extension: its `inf sup` over the whole
space is the book's `inf sup` over `C × D`. -/
theorem minimax_lowerSimpleExt (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    minimax (lowerSimpleExt C D K) = ⨅ x ∈ D, ⨆ u ∈ C, ((K (u, x) : ℝ) : EReal) := by
  rw [minimax_eq_biInf_biSup (concaveConvexFn_lowerSimpleExt hC hconv hconc)
      (saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC)
      (properSaddleFn_lowerSimpleExt hCne hDne),
    dom₁_lowerSimpleExt (K := K) hDne, dom₂_lowerSimpleExt (K := K) hCne]
  exact iInf_congr fun x => iInf_congr fun hx => iSup_congr fun u => iSup_congr fun hu =>
    lowerSimpleExt_of_mem (p := (u, x)) hu hx

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [FiniteDimensional ℝ X]
  [FiniteDimensional ℝ Y] in
/-- The unique closed convex bifunction whose lower bracket is the lower simple extension, packaged
with the membership `K₁ ∈ Ω (F)` that every §37 result consumes. -/
theorem exists_bifunSaddleClass_lowerSimpleExt (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    ∃ F : Bifun U X, ConvexBifun F ∧ ClosedBifun F ∧
      lowerSimpleExt C D K ∈ bifunSaddleClass Bu Bx F := by
  obtain ⟨F, ⟨hFconv, hFcl, hbr1, hbr2⟩, -⟩ := exists_unique_bifun_of_simpleExt Bu Bx hC hCcl
    hDcl hCne hconv hconc hDne hcontD hcontC
  refine ⟨F, hFconv, hFcl, ?_⟩
  rw [bifunSaddleClass, hbr1, hbr2]
  exact mem_saddleClass_left (partialCl₂_upperSimpleExt hDcl hDne hcontD)

end SimpleExt

section Cor3732

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {C : Set U} {D : Set Y} {K : U × Y → ℝ}

/-- **Rockafellar, Corollary 37.3.2**, the half where `D` is bounded: a finite continuous
concave-convex function on a product of nonempty closed convex sets, one of them bounded, has
`sup inf = inf sup` over `C × D`.

Proof idea: the lower simple extension is a closed proper concave-convex function with effective
domain `C × D` (Corollary 34.2.4), so Corollary 37.3.1 gives it a saddle-value, and Theorem 36.3
identifies its two iterated extrema with the book's restricted ones. -/
theorem biSup_biInf_eq_biInf_biSup_of_isBounded_right (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hB : Bx.SeparatingRight)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C)
    (hbd : Bornology.IsBounded D) :
    (⨆ u ∈ C, ⨅ x ∈ D, ((K (u, x) : ℝ) : EReal))
      = ⨅ x ∈ D, ⨆ u ∈ C, ((K (u, x) : ℝ) : EReal) := by
  obtain ⟨F, hFconv, hFcl, hmem⟩ := exists_bifunSaddleClass_lowerSimpleExt Bu Bx hC hCcl hDcl
    hCne hDne hconv hconc hcontD hcontC
  have hcc : ConcaveConvexFn (lowerSimpleExt C D K) :=
    concaveConvexFn_lowerSimpleExt hC hconv hconc
  have hp : ProperSaddleFn (lowerSimpleExt C D K) := properSaddleFn_lowerSimpleExt hCne hDne
  have hs : SaddleStructure (lowerSimpleExt C D K) :=
    saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC
  have hsv : HasSaddleValue (lowerSimpleExt C D K) :=
    hasSaddleValue_of_isBounded_dom₂ Bu Bx hB hFconv hFcl
      (proper_graphFn_of_properSaddleFn Bu Bx hmem hp) hmem hcc hp.dom₂_nonempty hp.dom₁_nonempty
      hs.1 (by rw [dom₂_lowerSimpleExt (K := K) hCne]; exact hbd)
  rw [hasSaddleValue_iff, maximin_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC,
    minimax_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC] at hsv
  exact hsv

/-- **Rockafellar, Corollary 37.3.2**, the half where `C` is bounded. -/
theorem biSup_biInf_eq_biInf_biSup_of_isBounded_left (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hB : Bu.SeparatingLeft)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C)
    (hbd : Bornology.IsBounded C) :
    (⨆ u ∈ C, ⨅ x ∈ D, ((K (u, x) : ℝ) : EReal))
      = ⨅ x ∈ D, ⨆ u ∈ C, ((K (u, x) : ℝ) : EReal) := by
  obtain ⟨F, hFconv, hFcl, hmem⟩ := exists_bifunSaddleClass_lowerSimpleExt Bu Bx hC hCcl hDcl
    hCne hDne hconv hconc hcontD hcontC
  have hcc : ConcaveConvexFn (lowerSimpleExt C D K) :=
    concaveConvexFn_lowerSimpleExt hC hconv hconc
  have hp : ProperSaddleFn (lowerSimpleExt C D K) := properSaddleFn_lowerSimpleExt hCne hDne
  have hs : SaddleStructure (lowerSimpleExt C D K) :=
    saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC
  have hsv : HasSaddleValue (lowerSimpleExt C D K) :=
    hasSaddleValue_of_isBounded_dom₁ Bu Bx hB hFconv hFcl hmem hcc hp hs
      (by rw [dom₁_lowerSimpleExt (K := K) hDne]; exact hbd)
  rw [hasSaddleValue_iff, maximin_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC,
    minimax_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC] at hsv
  exact hsv

/-- **Rockafellar, Corollary 37.6.2**: a finite continuous concave-convex function on a product of
nonempty compact convex sets has a saddle-point relative to that product. This is the classical
minimax theorem in the form everyone cites.

Proof idea: the lower simple extension is closed, proper and concave-convex with effective domain
`C × D` (Corollary 34.2.4); Corollary 37.6.1 gives it a saddle-point, Corollary 36.3.1 places that
point in `C × D`, and there the extension agrees with `K`. -/
theorem exists_saddlePoint_of_isBounded (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hBu : Bu.SeparatingLeft) (hBx : Bx.SeparatingRight)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C)
    (hbdC : Bornology.IsBounded C) (hbdD : Bornology.IsBounded D) :
    ∃ q : U × Y, q.1 ∈ C ∧ q.2 ∈ D ∧
      (∀ u ∈ C, K (u, q.2) ≤ K q) ∧ ∀ x ∈ D, K q ≤ K (q.1, x) := by
  obtain ⟨F, hFconv, hFcl, hmem⟩ := exists_bifunSaddleClass_lowerSimpleExt Bu Bx hC hCcl hDcl
    hCne hDne hconv hconc hcontD hcontC
  have hcc : ConcaveConvexFn (lowerSimpleExt C D K) :=
    concaveConvexFn_lowerSimpleExt hC hconv hconc
  have hp : ProperSaddleFn (lowerSimpleExt C D K) := properSaddleFn_lowerSimpleExt hCne hDne
  have hs : SaddleStructure (lowerSimpleExt C D K) :=
    saddleStructure_lowerSimpleExt hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC
  obtain ⟨q, hq⟩ := exists_isSaddlePoint_of_isBounded_domSaddle Bu Bx hBu hBx hFconv hFcl hmem
    hcc hp hs (by rw [dom₁_lowerSimpleExt (K := K) hDne]; exact hbdC)
    (by rw [dom₂_lowerSimpleExt (K := K) hCne]; exact hbdD)
  obtain ⟨hq₁, hq₂⟩ := hq.mem_domSaddle hp
  rw [dom₁_lowerSimpleExt (K := K) hDne] at hq₁
  rw [dom₂_lowerSimpleExt (K := K) hCne] at hq₂
  have hval : lowerSimpleExt C D K q = ((K q : ℝ) : EReal) :=
    lowerSimpleExt_of_mem (p := q) hq₁ hq₂
  refine ⟨q, hq₁, hq₂, fun u hu => ?_, fun x hx => ?_⟩
  · have h := hq.1 u
    rw [lowerSimpleExt_of_mem (p := (u, q.2)) hu hq₂, hval, EReal.coe_le_coe_iff] at h
    exact h
  · have h := hq.2 x
    rw [lowerSimpleExt_of_mem (p := (q.1, x)) hq₁ hx, hval, EReal.coe_le_coe_iff] at h
    exact h

end Cor3732

/-! ### Theorem 37.5, condition (c), and Corollary 37.5.1 -/

section Thm375c

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- Cancelling a real summand on the right of an `EReal` equation. -/
private theorem add_coe_right_inj {a b : EReal} {r : ℝ} :
    a + (r : EReal) = b + (r : EReal) ↔ a = b :=
  ⟨fun h => le_antisymm ((_root_.EReal.addLECancellable_coe r).add_le_add_iff_right.1 h.le)
      ((_root_.EReal.addLECancellable_coe r).add_le_add_iff_right.1 h.ge), fun h => by rw [h]⟩

/-- The arithmetic behind Theorem 37.5's (c) ⇔ (d): with `e = c - d`, the two equations
`-b = e - a` and `a - c = b - d` say the same thing. Both reduce to `a + d = b + c`, where no
`∞ - ∞` can arise because `c` and `d` are real. -/
private theorem neg_eq_coe_sub_iff_sub_coe_eq_sub_coe (a b : EReal) (c d e : ℝ)
    (he : -d + c = e) :
    -b = ((e : ℝ) : EReal) - a ↔ a - ((c : ℝ) : EReal) = b - ((d : ℝ) : EReal) := by
  have hb : -b = -(b - ((0 : ℝ) : EReal)) := by
    rw [_root_.EReal.coe_zero, sub_zero]
  have hkey : b + ((e : ℝ) : EReal) + ((d : ℝ) : EReal) = b + ((c : ℝ) : EReal) := by
    rw [add_assoc, ← _root_.EReal.coe_add]
    congr 2
    linarith
  rw [hb, ← neg_sub_coe a e, _root_.neg_inj, sub_coe_eq_sub_coe_iff, _root_.EReal.coe_zero,
    add_zero, sub_coe_eq_sub_coe_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h]
    exact hkey
  · exact add_coe_right_inj.1 (hkey.trans h.symm)

/-- **Rockafellar, Theorem 37.5**, (c) ⇔ (d): membership in the subdifferential of the class
`Ω (F)` is membership in the subdifferential of the graph function `f` of `F`, with the pair
`(u*, v)` **partially inverted** to `(-u*, v)` and `(u, v*)` read as a point of `U × X`.

This is the identity that makes `∂K` a partial inversion of `∂f`, and hence lets the geometric
results about `∂f` be read off for saddle-functions. -/
theorem isBifunSubgradientPair_iff_mem_subgradient_graphFn (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (p : U × Y) (q : V × X) :
    IsBifunSubgradientPair Bu Bx F p q ↔
      (-q.1, p.2) ∈ subgradient (prodPairing Bu Bx) (graphFn F) (p.1, q.2) := by
  have hconj : conj (prodPairing Bu Bx) (graphFn F) (-q.1, p.2)
      = -(adjointBifun Bu Bx F p.2 q.1) := by
    rw [adjointBifun_eq_neg_conj_graphFn, neg_neg]
  have hpair : (prodPairing Bu Bx (p.1, q.2) (-q.1, p.2) : ℝ)
      = -(Bu p.1 q.1) + Bx q.2 p.2 := by
    simp
  rw [mem_subgradient_iff_conj_eq, hconj, hpair, graphFn_apply, isBifunSubgradientPair_def]
  exact (neg_eq_coe_sub_iff_sub_coe_eq_sub_coe _ _ _ _ _ rfl).symm

end Thm375c

section Cor3751

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : Bifun U X} {K : U × Y → EReal}

/-- **Rockafellar, Corollary 37.5.1**, closedness clause: the graph of `∂K` is closed.

Proof idea: Theorem 37.5 identifies that graph with the preimage of the graph of `∂f` — `f` the
graph function of `F` — under the linear homeomorphism `(u, y, v, x) ↦ ((u, x), (-v, y))`, and
Theorem 24.4 says the graph of `∂f` is closed.

The homeomorphism clause of the corollary is Corollary 31.5.1 (`Optimization/Prox.lean`), which
cannot be instantiated at `prodPairing`: see this module's *What is not here*. -/
theorem isClosed_setOf_mem_saddleSubgradient (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hcu : Continuous fun r : U × V => Bu r.1 r.2)
    (hcx : Continuous fun r : X × Y => Bx r.1 r.2) (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    IsClosed {r : (U × Y) × (V × X) | r.2 ∈ saddleSubgradient Bu Bx.flip K r.1} := by
  have hcont : Continuous fun r : (U × Y) × (V × X) => ((r.1.1, r.2.2), (-r.2.1, r.1.2)) := by
    fun_prop
  have hpairing : Continuous fun r : (U × X) × (V × Y) => (prodPairing Bu Bx) r.1 r.2 := by
    have hgu : Continuous fun r : (U × X) × (V × Y) => (r.1.1, r.2.1) := by fun_prop
    have hgx : Continuous fun r : (U × X) × (V × Y) => (r.1.2, r.2.2) := by fun_prop
    have h1 : Continuous fun r : (U × X) × (V × Y) => Bu r.1.1 r.2.1 := hcu.comp hgu
    have h2 : Continuous fun r : (U × X) × (V × Y) => Bx r.1.2 r.2.2 := hcx.comp hgx
    have h3 : Continuous fun r : (U × X) × (V × Y) => Bu r.1.1 r.2.1 + Bx r.1.2 r.2.2 :=
      h1.add h2
    simpa only [prodPairing_apply] using h3
  have hset : {r : (U × Y) × (V × X) | r.2 ∈ saddleSubgradient Bu Bx.flip K r.1}
      = (fun r : (U × Y) × (V × X) => ((r.1.1, r.2.2), (-r.2.1, r.1.2)))
        ⁻¹' subgradientRel (prodPairing Bu Bx) (graphFn F) := by
    ext r
    rw [Set.mem_preimage, Set.mem_ofPred_eq,
      mem_saddleSubgradient_iff_isBifunSubgradientPair Bu Bx hF hcl hK,
      isBifunSubgradientPair_iff_mem_subgradient_graphFn]
    exact Iff.rfl
  rw [hset]
  exact IsClosed.preimage hcont
    (isClosed_subgradientRel hpairing hpr (ClosedFn.lowerSemicontinuous hcl))

end Cor3751

end Tdaf.ConvexAnalysis
