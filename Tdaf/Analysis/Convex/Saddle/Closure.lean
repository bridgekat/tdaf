/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Saddle.Defs

/-!
# The lower and upper closures of a saddle-function

Rockafellar's §34, first half. Applying `cl₁` and `cl₂` to a concave-convex function in the two
possible orders gives the **lower closure** `cl₂ cl₁ K` and the **upper closure** `cl₁ cl₂ K`.
These do *not* agree — §34 gives three examples of the discrepancy, and it is the reason the
section goes on to equivalence classes — but each is idempotent, which is Theorem 34.1.

## Main definitions

* `lowerCl K`, `upperCl K` — `cl₂ cl₁ K` and `cl₁ cl₂ K`.
* `LowerClosedFn`, `UpperClosedFn`, `FullyClosedFn` — the three closedness notions of §33–§34.
* `saddleSwap K` — the involution `K ↦ -K` with the arguments exchanged, which swaps the roles of
  `cl₁` and `cl₂`, together with its bundling `saddleSwapOrderIso` as an order isomorphism onto
  the order dual.

## Main results

* `fullyClosedFn_iff` — a saddle-function is fully closed iff it is both lower and upper closed.
* `upperClosedFn_upperCl`, `lowerClosedFn_lowerCl` — **Theorem 34.1**: the upper closure is upper
  closed and the lower closure is lower closed. Equivalently, `cl₁ cl₂ cl₁ cl₂ = cl₁ cl₂` and
  `cl₂ cl₁ cl₂ cl₁ = cl₂ cl₁`.

## Design notes

**Theorem 34.1 is Theorem 33.2 twice and Theorem 30.1 once.** For a concave-convex `K`, the
bifunction `F = bifunOfSaddle Bx K` has `⟨Fu, y⟩ = cl₂ K` (Theorem 33.1), so `cl₁ cl₂ K` is
`⟨u, F* y⟩` (Theorem 33.2, first equation). Closing that convexly gives `⟨(cl F) u, y⟩`
(Theorem 33.2, second equation, which is where Theorem 30.1's `F** = cl F` enters), and closing
*that* concavely gives `⟨u, (cl F)* y⟩`. The proof ends because the adjoint does not see the
closure: `(cl F)* = F*` (`adjointBifun_clBifun`, i.e. `conj_clFn` on the graph function).

**The lower half is the upper half at `saddleSwap`.** Negating and exchanging the arguments turns
`cl₁` into `cl₂` and back, so `upperCl (saddleSwap K) = saddleSwap (lowerCl K)` and lower
closedness of `K` is upper closedness of `saddleSwap K`. The price is that the swapped
application needs the pairings on the other side too — `IsCompatiblePairing Bu.flip` as well as
`IsCompatiblePairing Bu` — together with a topology on `V`. In `Rⁿ` all of this is automatic;
here it has to be asked for.

**The auxiliary space is in the hypotheses, not the statement.** `upperCl K` mentions only `U`,
`Y` and `K`, but proving anything about it needs a space `X` paired with `Y` and a space `V`
paired with `U`. Those appear only in the binders, so they have to be supplied explicitly at each
use site; that is the honest form of a theorem which in `Rⁿ` hides behind self-duality.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §33 (the closedness
  notions) and §34 (Theorem 34.1).
-/

namespace Tdaf.ConvexAnalysis

/-! ### The two closures -/

section Defs

variable {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {K : U × X → EReal}

/-- The **lower closure** `cl₂ cl₁ K` of a concave-convex function. -/
noncomputable def lowerCl (K : U × X → EReal) : U × X → EReal := partialCl₂ (partialCl₁ K)

/-- The **upper closure** `cl₁ cl₂ K` of a concave-convex function. -/
noncomputable def upperCl (K : U × X → EReal) : U × X → EReal := partialCl₁ (partialCl₂ K)

theorem lowerCl_def (K : U × X → EReal) : lowerCl K = partialCl₂ (partialCl₁ K) := rfl

theorem upperCl_def (K : U × X → EReal) : upperCl K = partialCl₁ (partialCl₂ K) := rfl

/-- `K` is **lower closed** when it is its own lower closure. -/
def LowerClosedFn (K : U × X → EReal) : Prop := lowerCl K = K

/-- `K` is **upper closed** when it is its own upper closure. -/
def UpperClosedFn (K : U × X → EReal) : Prop := upperCl K = K

/-- `K` is **fully closed** when it is closed in each variable separately. -/
def FullyClosedFn (K : U × X → EReal) : Prop := ConvexClosedFn K ∧ ConcaveClosedFn K

theorem lowerClosedFn_iff : LowerClosedFn K ↔ lowerCl K = K := Iff.rfl

theorem upperClosedFn_iff : UpperClosedFn K ↔ upperCl K = K := Iff.rfl

theorem fullyClosedFn_iff' : FullyClosedFn K ↔ ConvexClosedFn K ∧ ConcaveClosedFn K := Iff.rfl

end Defs

section FullyClosed

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {K : U × X → EReal}

omit [AddCommGroup U] [IsTopologicalAddGroup U] in
/-- A lower closed saddle-function is convex-closed: it *is* a `cl₂`, and `cl₂` is idempotent. -/
theorem LowerClosedFn.convexClosedFn (hK : LowerClosedFn K) : ConvexClosedFn K := by
  rw [← hK, lowerCl_def]
  exact convexClosedFn_partialCl₂ (partialCl₁ K)

omit [AddCommGroup X] [IsTopologicalAddGroup X] in
/-- An upper closed saddle-function is concave-closed. -/
theorem UpperClosedFn.concaveClosedFn (hK : UpperClosedFn K) : ConcaveClosedFn K := by
  rw [← hK, upperCl_def]
  exact concaveClosedFn_partialCl₁ (partialCl₂ K)

/-- **A saddle-function is fully closed exactly when it is both lower closed and upper closed**
(Rockafellar, §33). Both directions are the idempotence of `cl₁` and `cl₂`, which is
Corollary 33.1.1. -/
theorem fullyClosedFn_iff : FullyClosedFn K ↔ LowerClosedFn K ∧ UpperClosedFn K := by
  constructor
  · rintro ⟨h2, h1⟩
    exact ⟨by rw [lowerClosedFn_iff, lowerCl_def, h1, h2],
      by rw [upperClosedFn_iff, upperCl_def, h2, h1]⟩
  · rintro ⟨hl, hu⟩
    exact ⟨hl.convexClosedFn, hu.concaveClosedFn⟩

end FullyClosed

/-! ### The swap involution -/

section Swap

variable {U X : Type*} {K : U × X → EReal}

/-- Negate a saddle-function and exchange its arguments. This is an involution which turns
concave-convex functions into concave-convex functions and exchanges `cl₁` with `cl₂`. -/
noncomputable def saddleSwap (K : U × X → EReal) : X × U → EReal := fun q => -(K (q.2, q.1))

theorem saddleSwap_apply (K : U × X → EReal) (q : X × U) :
    saddleSwap K q = -(K (q.2, q.1)) := rfl

@[simp] theorem saddleSwap_saddleSwap (K : U × X → EReal) : saddleSwap (saddleSwap K) = K :=
  funext fun p => neg_neg (K p)

/-- `saddleSwap` negates, so it reverses the pointwise order. -/
theorem saddleSwap_le_saddleSwap {K L : U × X → EReal} (h : K ≤ L) :
    saddleSwap L ≤ saddleSwap K :=
  fun q => _root_.EReal.neg_le_neg_iff.2 (h (q.2, q.1))

/-- The swap **bundled**: an order isomorphism onto the order dual, because it is a two-sided
inverse of itself (`saddleSwap_saddleSwap`) and reverses the pointwise order
(`saddleSwap_le_saddleSwap`).

It is not an endomorphism — the two factors are exchanged — so `Function.Involutive` does not
apply and the two-sided inverse has to be recorded as an `Equiv`. -/
noncomputable def saddleSwapOrderIso : (U × X → EReal) ≃o (X × U → EReal)ᵒᵈ where
  toFun K := OrderDual.toDual (saddleSwap K)
  invFun K := saddleSwap (OrderDual.ofDual K)
  left_inv := saddleSwap_saddleSwap
  right_inv := saddleSwap_saddleSwap
  map_rel_iff' {K L} := by
    change saddleSwap L ≤ saddleSwap K ↔ K ≤ L
    exact ⟨fun h => by simpa using saddleSwap_le_saddleSwap h, saddleSwap_le_saddleSwap⟩

@[simp] theorem saddleSwapOrderIso_apply (K : U × X → EReal) :
    saddleSwapOrderIso K = saddleSwap K := rfl

theorem saddleSwap_injective :
    Function.Injective (saddleSwap : (U × X → EReal) → X × U → EReal) :=
  (saddleSwapOrderIso (U := U) (X := X)).injective

end Swap

section SwapConvex

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {K : U × X → EReal}

/-- The swap of a concave-convex function is concave-convex. -/
theorem concaveConvexFn_saddleSwap (hK : ConcaveConvexFn K) : ConcaveConvexFn (saddleSwap K) :=
  ⟨fun u => (hK.convex_snd u).concaveFn_neg, fun x => (hK.concave_fst x).convexFn_neg⟩

end SwapConvex

section SwapClosure

variable {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {K : U × X → EReal}

omit [TopologicalSpace U] in
/-- Closing the swap concavely in its first variable is closing `K` convexly in its second. -/
theorem partialCl₁_saddleSwap (K : U × X → EReal) :
    partialCl₁ (saddleSwap K) = saddleSwap (partialCl₂ K) :=
  funext fun q => clConcave_neg (fun x => K (q.2, x)) q.1

omit [TopologicalSpace X] in
/-- Closing the swap convexly in its second variable is closing `K` concavely in its first. -/
theorem partialCl₂_saddleSwap (K : U × X → EReal) :
    partialCl₂ (saddleSwap K) = saddleSwap (partialCl₁ K) :=
  funext fun q => (neg_clConcave (fun u => K (u, q.1)) q.2).symm

theorem upperCl_saddleSwap (K : U × X → EReal) :
    upperCl (saddleSwap K) = saddleSwap (lowerCl K) := by
  rw [upperCl_def, partialCl₂_saddleSwap, partialCl₁_saddleSwap, lowerCl_def]

theorem lowerCl_saddleSwap (K : U × X → EReal) :
    lowerCl (saddleSwap K) = saddleSwap (upperCl K) := by
  rw [lowerCl_def, partialCl₁_saddleSwap, partialCl₂_saddleSwap, upperCl_def]

/-- Lower closedness is upper closedness of the swap. -/
theorem lowerClosedFn_iff_upperClosedFn_saddleSwap :
    LowerClosedFn K ↔ UpperClosedFn (saddleSwap K) := by
  rw [lowerClosedFn_iff, upperClosedFn_iff, upperCl_saddleSwap]
  exact ⟨fun h => by rw [h], fun h => saddleSwap_injective h⟩

end SwapClosure

/-! ### Corollary 33.1.1, the mirror clause -/

section CorMirror

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U] {K : U × X → EReal}

/-- **Rockafellar, Corollary 33.1.1**, the clause mirroring `concaveConvexFn_partialCl₂`: `cl₁ K`
is again concave-convex, and in particular convex in the *second* variable. Swapping turns this
into the `cl₂` statement, so the pairing needed is the one on the concave variable. -/
theorem concaveConvexFn_partialCl₁ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (hK : ConcaveConvexFn K) : ConcaveConvexFn (partialCl₁ K) := by
  have h : partialCl₁ K = saddleSwap (partialCl₂ (saddleSwap K)) := by
    rw [partialCl₂_saddleSwap, saddleSwap_saddleSwap]
  rw [h]
  exact concaveConvexFn_saddleSwap
    (concaveConvexFn_partialCl₂ Bu.flip (concaveConvexFn_saddleSwap hK))

end CorMirror

/-! ### Theorem 34.1 -/

section Thm341

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {K : U × Y → EReal}

/-- **Rockafellar, Theorem 34.1**, upper half: the upper closure of a saddle-function is upper
closed, i.e. `cl₁ cl₂ cl₁ cl₂ K = cl₁ cl₂ K`.

The pairings are explicit arguments: they do not appear in the conclusion, so nothing can infer
them. `Bu` pairs the concave variable, `Bx` the convex one; `Bx` must be compatible on both sides,
because Fenchel–Moreau is applied once on `Y` and once on `U × X`. -/
theorem upperClosedFn_upperCl (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hK : ConcaveConvexFn K) : UpperClosedFn (upperCl K) := by
  have hF : ConvexBifun (bifunOfSaddle Bx K) := convexBifun_bifunOfSaddle hK Bx
  have h2 : partialCl₂ K = fun p : U × Y => bracket Bx (bifunOfSaddle Bx K) p.1 p.2 :=
    (funext fun p => bracket_bifunOfSaddle hK p).symm
  have hup : upperCl K
      = fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx (bifunOfSaddle Bx K)) p.1 p.2 := by
    funext p
    rw [upperCl_def, h2]
    exact (congrFun (concaveBracket_adjointBifun_eq_partialCl₁ (Bu := Bu) hF p.2) p.1).symm
  have h3 : partialCl₂ (upperCl K)
      = fun p : U × Y => bracket Bx (clBifun (bifunOfSaddle Bx K)) p.1 p.2 := by
    funext p
    rw [hup]
    have hb := bracket_concaveAdjointBifun_eq_partialCl₂ (Bu := Bu) (Bx := Bx)
      (concaveBifun_adjointBifun Bu Bx (bifunOfSaddle Bx K)) p.1
    rw [concaveAdjointBifun_adjointBifun_eq_clBifun hF] at hb
    exact (congrFun hb p.2).symm
  rw [upperClosedFn_iff, upperCl_def, h3]
  have h4 : partialCl₁ (fun q : U × Y => bracket Bx (clBifun (bifunOfSaddle Bx K)) q.1 q.2)
      = fun p : U × Y =>
        concaveBracket Bu (adjointBifun Bu Bx (clBifun (bifunOfSaddle Bx K))) p.1 p.2 := by
    funext p
    exact (congrFun (concaveBracket_adjointBifun_eq_partialCl₁ (Bu := Bu) hF.clBifun p.2) p.1).symm
  rw [h4, adjointBifun_clBifun, hup]

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] in
/-- **Rockafellar, Theorem 34.1**, lower half: the lower closure of a saddle-function is lower
closed. This is the upper half applied to `saddleSwap K`, which is why the pairings are needed on
both sides here. -/
theorem lowerClosedFn_lowerCl [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [LocallyConvexSpace ℝ V] (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx.flip]
    (hK : ConcaveConvexFn K) : LowerClosedFn (lowerCl K) := by
  rw [lowerClosedFn_iff_upperClosedFn_saddleSwap, ← upperCl_saddleSwap]
  exact upperClosedFn_upperCl Bx.flip Bu.flip (concaveConvexFn_saddleSwap hK)

end Thm341

end Tdaf.ConvexAnalysis
