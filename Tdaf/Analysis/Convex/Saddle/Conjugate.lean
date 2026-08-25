/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Saddle.Minimax

/-!
# The two conjugates of a saddle-function form a closure pair

`Saddle/Minimax.lean` produces the lower and upper conjugates `K̲*`, `K̄*` of a saddle-function
and identifies each of them, for every `K` in the class `Ω (F)` of a closed convex bifunction `F`,
in terms of `F`. This module completes the picture: the two conjugates are the *two brackets of
one and the same convex bifunction*, so they are a closure pair in the sense of Corollary 33.3.1,
they are equivalent, they have a common effective domain, and they agree wherever one coordinate
is a relative interior point of that domain.

The one new algebraic fact needed is the **biadjoint identity** `(F_*^*)^* = F_*`. It is not a new
theorem: the inverse operation `F ↦ F_*` intertwines the adjoint of a convex bifunction with the
adjoint of a concave one, so the identity is Theorem 30.2 (`F^{**} = cl F`) read through that
intertwining.

## Main results

* `adjointBifun_flip_inverseBifun` — the intertwining
  `(G_*)^* = (G^*)_*` for a concave `G`, with **no hypotheses at all**.
* `adjointBifun_flip_inverseBifun_adjointBifun` — the **biadjoint identity** `(F_*^*)^* = F_*`
  for a closed convex bifunction, i.e. Theorem 30.2 in the inverse picture.
* `saddleLagrangian_eq_concaveBracket` — the Lagrangian *is* the concave bracket of `F_*`,
  which is Rockafellar's own reading `L (v, x) = ⟨v, F_* x⟩` (§36), now available because the
  concave bracket exists in the backbone.
* `upperConjSaddle_eq_concaveBracket_adjointBifun` — the upper conjugate is the **upper** bracket
  of `F_*^*`, the companion of `lowerConjSaddle_eq_bracket_inverseBifun`.
* `partialCl₁_lowerConjSaddle`, `partialCl₂_upperConjSaddle` — **Corollary 37.1.2**, the two
  closure relations `cl₁ K̲* = K̄*` and `cl₂ K̄* = K̲*`.
* `saddleClass_conjSaddle`, `saddleEquiv_lowerConjSaddle_upperConjSaddle` — **Corollary 37.1.2**:
  the class conjugate to `Ω (F)` is `Ω (F_*^*)`, and the two conjugates are equivalent.
* `properSaddleFn_saddleLagrangian`, `properSaddleFn_upperConjSaddle`,
  `properSaddleFn_lowerConjSaddle` — a saddle-function conjugate to a closed proper one is proper.
  Rockafellar states this in a remark; the substance is that a closed proper convex function has
  an affine minorant (`proper_conj`).
* `dom₁_conjSaddle_eq`, `dom₂_conjSaddle_eq`, `domSaddle_conjSaddle_eq` — **Corollary 37.1.2**:
  `C* × D*` is the effective domain of both conjugates.
* `exists_maximin_eq_coe_of_mem_relint_domSaddle` — **Corollary 37.1.3**, last sentence.
* `eq_of_mem_relint_dom₁_of_closure_pair`, `eq_of_mem_relint_dom₂_of_closure_pair` — the two
  halves of Theorem 34.2's last clause for a closure *pair*, rather than for one closed
  saddle-function and its closures.
* `lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₁`,
  `lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₂` — **Corollary 37.1.2**, last clause.
* `hasSaddleValue_of_mem_relint_dom₁_lowerConjSaddle`,
  `hasSaddleValue_of_mem_relint_dom₂_lowerConjSaddle` — **Corollary 37.1.3**: the origin in the
  relative interior of either half of `C* × D*` forces the saddle-value to exist, and it is then
  finite.
* `dom₁_eq_domBifun_of_mem_bifunSaddleClass`, `dom₂_upperConjSaddle` — the two effective
  domains as projections: `C = dom F` for *every* member of `Ω (F)`, and `D*` is the projection
  of `dom F` on `X`.
* `supportFn_dom₂_upperConjSaddle`, `supportFn_dom₂_upperConjSaddle_eq_iSup_recessionFn` —
  **Theorem 37.2**, the `D*` half, in the book's difference-quotient form and in recession-function
  form.
* `zero_mem_interior_dom₂_upperConjSaddle_iff` — **Corollary 37.2.1**, the `D*` half.
* `hasSaddleValue_of_no_common_direction_of_recession` — **Theorem 37.3**, condition (a).
* `hasSaddleValue_of_isBounded_dom₂` — **Corollary 37.3.1**, the half where `D` is bounded.

## Design notes

**`(F_*)^* = (F^*)_*` is a definition in `Minimax.lean`; the identity proved here is the
*biadjoint*.** Rockafellar writes `F_*^*` for the adjoint of the concave inverse; `Minimax.lean`
takes `inverseBifun (adjointBifun Bu Bx F)` as the definition of that object, so his commutation
is a triviality. What is *not* a triviality, and what Corollary 37.1.2 needs, is that adjoining
that object once more returns `F_*`. `adjointBifun_flip_inverseBifun` is the bridge: it says the
adjoint of `G_*` at the flipped pairings is the inverse of the *concave* adjoint of `G`, which is
pure reindexing, and then Theorem 30.2 finishes.

**The pairing flips, and the two spaces exchange roles.** `K̲*` and `K̄*` live on `V × X`, and the
convex bifunction behind them goes from `V` to `Y`. So every §33 lemma is used at `Bu.flip` and
`Bx.flip`, which is why `[IsCompatiblePairing Bu.flip]` and `[IsCompatiblePairing Bx.flip]` appear
throughout, and why `Bx.flip.flip` has to be bridged by hand (it is not found by instance search).

**Properness of the conjugate splits unevenly.** `dom₂ K̄* ≠ ∅` is one line from properness of the
graph function; `dom₁ K̄* ≠ ∅` is the existence of an affine minorant of the graph function, i.e.
`proper_conj`, and it is what makes closedness of `F` a genuine hypothesis of Corollary 37.1.3
rather than a convenience.

**The `ri` clause of Corollary 37.1.2 is Theorem 34.2's last clause, but for a closure pair.**
`Saddle/Kernel.lean` proves it for a closed saddle-function against its own two closures, which
needs `ClosedSaddleFn` and `ProperSaddleFn`; here the two closure relations are known *on the
nose*, so the hypotheses reduce to concave-convexity of one of the two and nonemptiness of one
effective domain. The two statements are stated separately (`eq_of_mem_relint_dom₁_of_closure_pair`
and its mirror) because they need *different* halves of properness and different finite-dimension
instances.

## What is not here

**The `C*` halves of Theorem 37.2, Corollary 37.2.1, Theorem 37.3 and Corollary 37.3.1** are in
`Saddle/Existence.lean`. They are the same statements read through `saddleSwap`, at the negated
flipped pairings `-Bx.flip`, `-Bu.flip`, and the dictionary carrying `bifunSaddleClass` across that
swap is `saddleSwap_mem_bifunSaddleClass`.

**Theorems 37.4–37.6**, which rest on §35's subdifferential `∂K = ∂₁K × ∂₂K`; they live in
`Saddle/Subgradient.lean`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §30, §34, §37.
-/

namespace Tdaf.ConvexAnalysis

/-! ### The inverse intertwines the convex and the concave adjoint -/

section Intertwine

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **The inverse operation intertwines the two adjoints**: for a concave bifunction `G` from `Y`
to `V`, the (convex) adjoint of `G_*` taken at the flipped pairings is the inverse of the concave
adjoint of `G`.

Both sides are the same iterated extremum of the same summands; the proof is one exchange of the
two bound variables, plus the sign bookkeeping that turns `-(a + c)` into `-a + (-c)` for a real
constant `c`. No hypothesis on `G` is needed — this is an identity of definitions. -/
theorem adjointBifun_flip_inverseBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G : Bifun Y V) :
    adjointBifun Bu.flip Bx.flip (inverseBifun G)
      = inverseBifun (concaveAdjointBifun Bu Bx G) := by
  funext x u
  have hpt : ∀ (v : V) (y : Y),
      inverseBifun G v y + ((Bu u v - Bx x y : ℝ) : EReal)
        = -(G y v + ((Bx x y - Bu u v : ℝ) : EReal)) := by
    intro v y
    have hneg : -(G y v + ((Bx x y - Bu u v : ℝ) : EReal))
        = -(G y v) + -(((Bx x y - Bu u v : ℝ) : EReal)) :=
      _root_.EReal.neg_add (.inr (_root_.EReal.coe_ne_top _))
        (.inr (_root_.EReal.coe_ne_bot _))
    have hr : (Bu u v - Bx x y : ℝ) = -(Bx x y - Bu u v) := by ring
    rw [hneg, inverseBifun_apply, hr, _root_.EReal.coe_neg]
  rw [inverseBifun_apply, concaveAdjointBifun_apply, Tdaf.EReal.neg_iSup, iInf_prod,
    adjointBifun_apply, iInf_prod, iInf_comm]
  exact iInf_congr fun y => iInf_congr fun v => hpt v y

end Intertwine

section Biadjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {F : Bifun U X}

/-- **The biadjoint identity `(F_*^*)^* = F_*`** for a closed convex bifunction. This is
Rockafellar's remark that the equivalence class conjugate to `Ω (F)` is `Ω (F_*)` (§37, before
Corollary 37.1.2), and it is what makes Corollary 37.1.2 a statement about a closure pair.

The proof is `adjointBifun_flip_inverseBifun` followed by Theorem 30.2 (`F** = cl F = F`); no
new extremum is computed. -/
theorem adjointBifun_flip_inverseBifun_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    adjointBifun Bu.flip Bx.flip (inverseBifun (adjointBifun Bu Bx F)) = inverseBifun F := by
  rw [adjointBifun_flip_inverseBifun, concaveAdjointBifun_adjointBifun_eq_self hF hcl]

end Biadjoint

/-! ### The Lagrangian is the concave bracket of the inverse -/

section LagrangianBracket

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- **Rockafellar, §36**: `L (v, x) = ⟨v, F_* x⟩`. The Lagrangian of `(P)` is the concave bracket
of the inverse bifunction `F_*`, for the flipped pairing. `Minimax.lean` had to route Theorem 36.5
through `saddleSwap` because the *closedness* half needs the convex Theorem 33.3; the identity
itself is an unfolding, `a - (-b) = a + b`. -/
theorem concaveBracket_inverseBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) (x : X) :
    concaveBracket Bu.flip (inverseBifun F) v x = lagrangian Bu F v x := by
  rw [concaveBracket_apply, lagrangian_apply]
  refine iInf_congr fun u => ?_
  rw [inverseBifun_apply, sub_eq_add_neg, neg_neg, LinearMap.flip_apply]

/-- The saddle-function form of `concaveBracket_inverseBifun`: the Lagrangian read on `V × X` is
the upper bracket of `F_*`. -/
theorem saddleLagrangian_eq_concaveBracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) :
    saddleLagrangian Bu F
      = fun q : V × X => concaveBracket Bu.flip (inverseBifun F) q.1 q.2 :=
  funext fun q => (concaveBracket_inverseBifun Bu F q.1 q.2).symm

end LagrangianBracket

/-! ### Corollary 37.1.2: the two conjugates are the two brackets of `F_*^*` -/

section Cor3712

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] in
/-- **The upper conjugate is the *upper* bracket of `F_*^*`**, the companion of
`lowerConjSaddle_eq_bracket_inverseBifun`. Theorem 37.1 identifies `K̄*` with the Lagrangian of
`F`; the Lagrangian is the concave bracket of `F_*` (`saddleLagrangian_eq_concaveBracket`), and
the biadjoint identity rewrites `F_*` as the adjoint of `F_*^*`. -/
theorem upperConjSaddle_eq_concaveBracket_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) :
    upperConjSaddle Bu Bx K = fun q : V × X => concaveBracket Bu.flip
      (adjointBifun Bu.flip Bx.flip (inverseBifun (adjointBifun Bu Bx F))) q.1 q.2 := by
  rw [upperConjSaddle_eq_saddleLagrangian Bu Bx hF hcl hK,
    adjointBifun_flip_inverseBifun_adjointBifun Bu Bx hF hcl,
    saddleLagrangian_eq_concaveBracket]

/-- **Rockafellar, Corollary 37.1.2**, first equation: `cl₁ K̲* = K̄*`.

Both conjugates are brackets of the single closed convex bifunction `F_*^*`, so this is
Theorem 33.2's first equation (`partialCl₁_bracket`) at the flipped pairings. -/
theorem partialCl₁_lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) :
    partialCl₁ (lowerConjSaddle Bu Bx K) = upperConjSaddle Bu Bx K := by
  have hG : ConvexBifun (inverseBifun (adjointBifun Bu Bx F)) :=
    convexBifun_inverseBifun_adjointBifun Bu Bx F
  rw [lowerConjSaddle_eq_bracket_inverseBifun Bu Bx hF hK,
    partialCl₁_bracket Bu.flip Bx.flip hG,
    upperConjSaddle_eq_concaveBracket_adjointBifun Bu Bx hF hcl hK]

/-- **Rockafellar, Corollary 37.1.2**, second equation: `cl₂ K̄* = K̲*`. This is Theorem 33.2's
second equation, and it is where closedness of `F_*^*` is used. -/
theorem partialCl₂_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) :
    partialCl₂ (upperConjSaddle Bu Bx K) = lowerConjSaddle Bu Bx K := by
  have hflip : IsCompatiblePairing Bx.flip.flip := by rw [LinearMap.flip_flip]; infer_instance
  have hG : ConvexBifun (inverseBifun (adjointBifun Bu Bx F)) :=
    convexBifun_inverseBifun_adjointBifun Bu Bx F
  have hGcl : ClosedBifun (inverseBifun (adjointBifun Bu Bx F)) :=
    closedBifun_inverseBifun_adjointBifun Bu Bx F
  rw [upperConjSaddle_eq_concaveBracket_adjointBifun Bu Bx hF hcl hK,
    partialCl₂_concaveBracket_adjoint Bu.flip Bx.flip hG hGcl,
    lowerConjSaddle_eq_bracket_inverseBifun Bu Bx hF hK]

/-- **Rockafellar, §37**, the sentence before Corollary 37.1.2: the equivalence class conjugate to
`Ω (F)` is `Ω (F_*^*)`, and its two ends are the lower and the upper conjugate of any member of
`Ω (F)`. -/
theorem saddleClass_conjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) :
    bifunSaddleClass Bu.flip Bx.flip (inverseBifun (adjointBifun Bu Bx F))
      = saddleClass (lowerConjSaddle Bu Bx K) (upperConjSaddle Bu Bx K) := by
  rw [bifunSaddleClass, lowerConjSaddle_eq_bracket_inverseBifun Bu Bx hF hK,
    upperConjSaddle_eq_concaveBracket_adjointBifun Bu Bx hF hcl hK]

/-- **Rockafellar, Corollary 37.1.2**: the lower and the upper conjugate are equivalent
saddle-functions, so by Theorem 36.4 they have the same iterated extrema and the same
saddle-points. -/
theorem saddleEquiv_lowerConjSaddle_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    SaddleEquiv (lowerConjSaddle Bu Bx K) (upperConjSaddle Bu Bx K) := by
  have h1 := partialCl₁_lowerConjSaddle Bu Bx hF hcl hK
  have h2 := partialCl₂_upperConjSaddle Bu Bx hF hcl hK
  exact saddleEquiv_of_mem_saddleClass h1 h2 (mem_saddleClass_left h2) (mem_saddleClass_right h2)

end Cor3712

/-! ### Properness of the conjugate saddle-functions -/

section ProperConj

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {F : Bifun U X}

/-- **Rockafellar, §37**, the remark before Corollary 37.1.2: a saddle-function conjugate to a
closed proper one is again proper.

The two halves are quite different. `dom₂ L ≠ ∅` only needs a point where the graph function is
finite: the infimum defining `L (v, x₀)` is then bounded above by one of its terms. `dom₁ L ≠ ∅`
is the existence of an affine minorant of the graph function — `proper_conj`, i.e. Theorem 12.2 —
which is where closedness enters: if `f (u, x) ≥ ⟨u, v₁⟩ + ⟨x, y₁⟩ - c` then `L (-v₁, x)` is
bounded below by `⟨x, y₁⟩ - c` for *every* `x`. -/
theorem properSaddleFn_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hpr : Proper (graphFn F)) :
    ProperSaddleFn (saddleLagrangian Bu F) := by
  obtain ⟨p₀, hp₀⟩ := hpr.dom_nonempty
  obtain ⟨⟨v₁, y₁⟩, hw⟩ :=
    (proper_conj (B := prodPairing Bu Bx) ⟨hF, hcl, hpr⟩).dom_nonempty
  have hw' : conj (prodPairing Bu Bx) (graphFn F) (v₁, y₁) < ⊤ := hw
  have hadj : adjointBifun Bu Bx F y₁ (-v₁) ≠ ⊥ := by
    rw [adjointBifun_eq_neg_conj_graphFn, neg_neg]
    exact fun hcon => absurd (_root_.EReal.neg_eq_bot_iff.1 hcon) (ne_of_lt hw')
  refine ⟨⟨-v₁, ?_⟩, ⟨p₀.2, ?_⟩⟩
  · intro x
    have hterm : ∀ u : U, ((Bu u (-v₁) : ℝ) : EReal) + F u x
        = (F u x + ((Bu u (-v₁) - Bx x y₁ : ℝ) : EReal)) + ((Bx x y₁ : ℝ) : EReal) := by
      intro u
      have hreal : (Bu u (-v₁) - Bx x y₁ : ℝ) + Bx x y₁ = Bu u (-v₁) := by ring
      rw [add_assoc, ← _root_.EReal.coe_add, hreal, add_comm (F u x)]
    have hge : adjointBifun Bu Bx F y₁ (-v₁) + ((Bx x y₁ : ℝ) : EReal)
        ≤ saddleLagrangian Bu F (-v₁, x) := by
      change _ ≤ lagrangian Bu F (-v₁) x
      rw [lagrangian_apply]
      refine le_iInf fun u => ?_
      rw [hterm u, adjointBifun_apply]
      exact add_le_add (iInf_le (fun p : U × X =>
        F p.1 p.2 + ((Bu p.1 (-v₁) - Bx p.2 y₁ : ℝ) : EReal)) (u, x)) le_rfl
    refine lt_of_lt_of_le (bot_lt_iff_ne_bot.2 fun hcon => ?_) hge
    rcases _root_.EReal.add_eq_bot_iff.1 hcon with h | h
    · exact hadj h
    · exact _root_.EReal.coe_ne_bot _ h
  · intro v
    change lagrangian Bu F v p₀.2 < ⊤
    rw [lagrangian_apply]
    refine lt_of_le_of_lt (iInf_le (fun u => ((Bu u v : ℝ) : EReal) + F u p₀.2) p₀.1) ?_
    exact _root_.EReal.add_lt_top (_root_.EReal.coe_ne_top _) (ne_of_lt hp₀)

end ProperConj

/-! ### Theorem 34.2's last clause for a closure pair -/

section ClosurePairRelint

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {Klow Kup : U × X → EReal}

/-- **Rockafellar, Theorem 34.2**, last clause, for a *closure pair*: if `cl₁ K̲ = K̄` and
`cl₂ K̄ = K̲` then the two agree over `ri (dom₁ K̲)`.

`Saddle/Kernel.lean` proves this for a closed saddle-function against its own two closures, at the
cost of `ClosedSaddleFn` and full properness. Here the closure relations hold on the nose, so what
is left is: `K̲ (·, x)` is `cl₂ K̄ (·, x)`, whose concave effective domain is exactly `dom₁ K̄`
(`domConcave_partialCl₂_slice`), and a concave function meets its closure on the relative interior
of that domain. Only `dom₂ K̄ ≠ ∅` is needed. -/
theorem eq_of_mem_relint_dom₁_of_closure_pair (hup : ConcaveConvexFn Kup)
    (hne : (dom₂ Kup).Nonempty) (h1 : partialCl₁ Klow = Kup) (h2 : partialCl₂ Kup = Klow)
    {u : U} (hu : u ∈ ri (dom₁ Klow)) (x : X) : Klow (u, x) = Kup (u, x) := by
  have hd1 : dom₁ Klow = dom₁ Kup := by rw [← h2]; exact dom₁_partialCl₂ hup hne
  have hslice : ConcaveFn fun u => partialCl₂ Kup (u, x) := hup.partialCl₂.concave_fst x
  have hdom : domConcave (fun u => partialCl₂ Kup (u, x)) = dom₁ Kup :=
    domConcave_partialCl₂_slice hup hne x
  have hmem : u ∈ ri (domConcave fun u => partialCl₂ Kup (u, x)) := by
    rw [hdom, ← hd1]; exact hu
  have hcl := hslice.clConcave_eq_of_mem_relint_domConcave hmem
  calc Klow (u, x) = partialCl₂ Kup (u, x) := by rw [h2]
    _ = clConcave (fun u => partialCl₂ Kup (u, x)) u := hcl.symm
    _ = clConcave (fun u => Klow (u, x)) u := by rw [h2]
    _ = partialCl₁ Klow (u, x) := (congrFun (partialCl₁_slice Klow x) u).symm
    _ = Kup (u, x) := by rw [h1]

/-- The mirror of `eq_of_mem_relint_dom₁_of_closure_pair`: a closure pair agrees over
`ri (dom₂ K̄)`. It is not the same statement read at `saddleSwap`, because the two use different
halves of properness — this one needs `dom₁ K̲ ≠ ∅` — so it is proved directly, through
`dom_partialCl₁_slice` and `ConvexFn.clFn_eq_of_mem_relint_dom`. -/
theorem eq_of_mem_relint_dom₂_of_closure_pair (hlow : ConcaveConvexFn Klow)
    (hne : (dom₁ Klow).Nonempty) (h1 : partialCl₁ Klow = Kup) (h2 : partialCl₂ Kup = Klow)
    {x : X} (hx : x ∈ ri (dom₂ Kup)) (u : U) : Klow (u, x) = Kup (u, x) := by
  have hd2 : dom₂ Kup = dom₂ Klow := by rw [← h1]; exact dom₂_partialCl₁ hlow hne
  have hslice : ConvexFn fun x => partialCl₁ Klow (u, x) := hlow.partialCl₁.convex_snd u
  have hdom : dom (fun x => partialCl₁ Klow (u, x)) = dom₂ Klow :=
    dom_partialCl₁_slice hlow hne u
  have hmem : x ∈ ri (dom fun x => partialCl₁ Klow (u, x)) := by
    rw [hdom, ← hd2]; exact hx
  have hcl := hslice.clFn_eq_of_mem_relint_dom hmem
  calc Klow (u, x) = partialCl₂ Kup (u, x) := by rw [h2]
    _ = clFn (fun x => Kup (u, x)) x := congrFun (partialCl₂_slice Kup u) x
    _ = clFn (fun x => partialCl₁ Klow (u, x)) x := by rw [h1]
    _ = partialCl₁ Klow (u, x) := hcl
    _ = Kup (u, x) := by rw [h1]

end ClosurePairRelint

/-! ### Corollary 37.1.2, last clause, and Corollary 37.1.3 -/

section Cor3713

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : Bifun U X} {K : U × Y → EReal}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ X] in
/-- **Rockafellar, Corollary 37.1.2**: the upper conjugate of a member of `Ω (F)` is proper when
`F` is a closed proper convex bifunction. -/
theorem properSaddleFn_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedBifun F) (hpr : Proper (graphFn F))
    (hK : K ∈ bifunSaddleClass Bu Bx F) : ProperSaddleFn (upperConjSaddle Bu Bx K) := by
  rw [upperConjSaddle_eq_saddleLagrangian Bu Bx hF hcl hK]
  exact properSaddleFn_saddleLagrangian Bu Bx hF hcl hpr

omit [FiniteDimensional ℝ V] in
/-- **Rockafellar, Corollary 37.1.2**: the lower conjugate is proper as well — it is `cl₂` of the
upper one, and `cl₂` preserves properness. -/
theorem properSaddleFn_lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    ProperSaddleFn (lowerConjSaddle Bu Bx K) := by
  rw [← partialCl₂_upperConjSaddle Bu Bx hF hcl hK]
  exact ProperSaddleFn.partialCl₂ (concaveConvexFn_upperConjSaddle Bu Bx hF hcl hK)
    (properSaddleFn_upperConjSaddle Bu Bx hF hcl hpr hK)

omit [FiniteDimensional ℝ V] in
/-- **Rockafellar, Corollary 37.1.2**: `C*`, the first half of the common effective domain, does
not depend on which of the two conjugates it is read from. -/
theorem dom₁_conjSaddle_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    dom₁ (lowerConjSaddle Bu Bx K) = dom₁ (upperConjSaddle Bu Bx K) := by
  rw [← partialCl₂_upperConjSaddle Bu Bx hF hcl hK]
  exact dom₁_partialCl₂ (concaveConvexFn_upperConjSaddle Bu Bx hF hcl hK)
    (properSaddleFn_upperConjSaddle Bu Bx hF hcl hpr hK).dom₂_nonempty

/-- **Rockafellar, Corollary 37.1.2**: the same for `D*`. -/
theorem dom₂_conjSaddle_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    dom₂ (lowerConjSaddle Bu Bx K) = dom₂ (upperConjSaddle Bu Bx K) := by
  rw [← partialCl₁_lowerConjSaddle Bu Bx hF hcl hK]
  exact (dom₂_partialCl₁ (concaveConvexFn_lowerConjSaddle Bu Bx hF hK)
    (properSaddleFn_lowerConjSaddle Bu Bx hF hcl hpr hK).dom₁_nonempty).symm

/-- **Rockafellar, Corollary 37.1.2**: `C* × D*` is the effective domain of *both* conjugates. -/
theorem domSaddle_conjSaddle_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    domSaddle (lowerConjSaddle Bu Bx K) = domSaddle (upperConjSaddle Bu Bx K) := by
  rw [domSaddle, domSaddle, dom₁_conjSaddle_eq Bu Bx hF hcl hpr hK,
    dom₂_conjSaddle_eq Bu Bx hF hcl hpr hK]

/-- **Rockafellar, Corollary 37.1.2**, last clause: the two conjugates agree wherever the first
coordinate is a relative interior point of `C*`. -/
theorem lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₁ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    {v : V} (hv : v ∈ ri (dom₁ (lowerConjSaddle Bu Bx K))) (x : X) :
    lowerConjSaddle Bu Bx K (v, x) = upperConjSaddle Bu Bx K (v, x) :=
  eq_of_mem_relint_dom₁_of_closure_pair (concaveConvexFn_upperConjSaddle Bu Bx hF hcl hK)
    (properSaddleFn_upperConjSaddle Bu Bx hF hcl hpr hK).dom₂_nonempty
    (partialCl₁_lowerConjSaddle Bu Bx hF hcl hK) (partialCl₂_upperConjSaddle Bu Bx hF hcl hK)
    hv x

/-- **Rockafellar, Corollary 37.1.2**, last clause: and wherever the second coordinate is a
relative interior point of `D*`. -/
theorem lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₂ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    {x : X} (hx : x ∈ ri (dom₂ (lowerConjSaddle Bu Bx K))) (v : V) :
    lowerConjSaddle Bu Bx K (v, x) = upperConjSaddle Bu Bx K (v, x) := by
  refine eq_of_mem_relint_dom₂_of_closure_pair (concaveConvexFn_lowerConjSaddle Bu Bx hF hK)
    (properSaddleFn_lowerConjSaddle Bu Bx hF hcl hpr hK).dom₁_nonempty
    (partialCl₁_lowerConjSaddle Bu Bx hF hcl hK) (partialCl₂_upperConjSaddle Bu Bx hF hcl hK)
    ?_ v
  rwa [← dom₂_conjSaddle_eq Bu Bx hF hcl hpr hK]

/-- **Rockafellar, Corollary 37.1.3**: if the origin of the dual of the concave variable lies in
`ri C*`, the saddle-value of `K` exists.

The two iterated extrema of `K` are the two conjugates at the origin
(`hasSaddleValue_iff_conjSaddle_zero_eq`), and Corollary 37.1.2 makes them agree there. -/
theorem hasSaddleValue_of_mem_relint_dom₁_lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (h0 : (0 : V) ∈ ri (dom₁ (lowerConjSaddle Bu Bx K))) : HasSaddleValue K :=
  (hasSaddleValue_iff_conjSaddle_zero_eq Bu Bx K).2
    (lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₁ Bu Bx hF hcl hpr hK h0 0).symm

/-- **Rockafellar, Corollary 37.1.3**, mirror half: the origin in `ri D*` suffices as well. -/
theorem hasSaddleValue_of_mem_relint_dom₂_lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (h0 : (0 : X) ∈ ri (dom₂ (lowerConjSaddle Bu Bx K))) : HasSaddleValue K :=
  (hasSaddleValue_iff_conjSaddle_zero_eq Bu Bx K).2
    (lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₂ Bu Bx hF hcl hpr hK h0 0).symm

/-- **Rockafellar, Corollary 37.1.3**, last sentence: if the origin lies in the relative interior
of *both* halves of `C* × D*`, the saddle-value is finite. It is then a value of the conjugate on
its own effective domain, where a saddle-function is finite by definition. -/
theorem exists_maximin_eq_coe_of_mem_relint_domSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (h1 : (0 : V) ∈ ri (dom₁ (lowerConjSaddle Bu Bx K)))
    (h2 : (0 : X) ∈ ri (dom₂ (lowerConjSaddle Bu Bx K))) :
    ∃ r : ℝ, maximin K = (r : EReal) := by
  have hmem : ((0 : V), (0 : X)) ∈ domSaddle (lowerConjSaddle Bu Bx K) :=
    ⟨intrinsicInterior_subset h1, intrinsicInterior_subset h2⟩
  obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top
    (ne_of_gt (bot_lt_of_mem_domSaddle hmem)) (lt_top_of_mem_domSaddle hmem)
  refine ⟨-r, ?_⟩
  have heq : upperConjSaddle Bu Bx K 0 = ((r : ℝ) : EReal) := by
    have h := lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₁ Bu Bx hF hcl hpr hK h1 0
    change lowerConjSaddle Bu Bx K 0 = upperConjSaddle Bu Bx K 0 at h
    rw [← h]
    exact hr
  rw [maximin_eq_neg_upperConjSaddle_zero Bu Bx K, heq, _root_.EReal.coe_neg]

end Cor3713

/-! ### Theorem 37.2: the effective domains of the conjugate saddle-functions

Rockafellar's Theorem 37.2 computes the support functions of `C* = dom₁ K*` and `D* = dom₂ K*`,
for `K ∈ Ω (F)`, in terms of `K` itself. The `D*` half is the one with content: `D*` is the
projection on `X` of `dom F`, and the support function of that projection is assembled from the
support functions of the individual slices `dom (F u)`, each of which is a recession function by
Theorem 13.3.

The lemmas of this block are the bookkeeping. `D*` and `C*` are projections; support functions do
not see relative interiors; and the relative interior of a projection is the union of the relative
interiors of the slices taken over `ri` of the other projection (Theorems 6.6 and 6.8). -/

section DomLagrangian

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- **Rockafellar, Theorem 37.2 (the set `D*`)**: the second effective domain of the Lagrangian
`L (v, x) = inf_u {⟨u, v⟩ + F (u, x)}` is the projection of `dom F` on `X`, with no hypotheses on
`F` whatsoever.

Proof idea: `L (v, x) ≤ ⟨u, v⟩ + F (u, x)` gives `⊇` at once. For `⊆` it is enough to test
`v = 0`, where `L (0, x) = inf_u F (u, x)`; an infimum below `⊤` has a term below `⊤`. -/
theorem dom₂_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) :
    dom₂ (saddleLagrangian Bu F) = Prod.snd '' dom (graphFn F) := by
  ext x
  constructor
  · intro hx
    have h0 : lagrangian Bu F 0 x < ⊤ := hx 0
    rw [lagrangian_apply] at h0
    have h1 : ⨅ u, F u x < ⊤ := by
      refine lt_of_le_of_lt (le_of_eq (iInf_congr fun u => ?_)) h0
      rw [map_zero, _root_.EReal.coe_zero, zero_add]
    obtain ⟨u, hu⟩ := iInf_lt_iff.1 h1
    exact ⟨(u, x), hu, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    intro v
    change lagrangian Bu F v p.2 < ⊤
    rw [lagrangian_apply]
    refine lt_of_le_of_lt (iInf_le (fun u => ((Bu u v : ℝ) : EReal) + F u p.2) p.1) ?_
    exact _root_.EReal.add_lt_top (_root_.EReal.coe_ne_top _) (ne_of_lt hp)

end DomLagrangian

section DomProjection

variable {U X : Type*}

/-- `dom F ⊆ U` is the projection on `U` of the effective domain of the graph function: both say
that some value `F (u, x)` is `< ⊤`. -/
theorem domBifun_eq_image_fst (F : Bifun U X) : domBifun F = Prod.fst '' dom (graphFn F) := by
  ext u
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(u, x), lt_top_iff_ne_top.2 hx, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, ne_of_lt hp⟩

end DomProjection

section DomBracket

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The first effective domain of the lower bracket `⟨Fu, y⟩` is `dom F`: the bracket is `-∞`
exactly where the slice `F u` is identically `+∞`, uniformly in `y` (`domConcave_bracket`). -/
theorem dom₁_bracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) :
    dom₁ (fun p : U × Y => bracket Bx F p.1 p.2) = domBifun F := by
  ext u
  constructor
  · intro hu
    have h : u ∈ domConcave fun u => bracket Bx F u (0 : Y) := hu 0
    rwa [domConcave_bracket] at h
  · intro hu y
    have h : u ∈ domConcave fun u => bracket Bx F u y := by
      rw [domConcave_bracket]; exact hu
    exact h

end DomBracket

section SupportRelint

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- **The support function does not see the relative interior**: `δ*(· | ri C) = δ*(· | C)` for
convex `C`. Proof idea: support functions do not see closures (`supportFn_closure`), and
`cl (ri C) = cl C` by Theorem 6.3. -/
theorem supportFn_relint (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] {C : Set E}
    (hC : Convex ℝ C) : supportFn B (ri C) = supportFn B C := by
  rw [← supportFn_closure (B := B) (ri C), Convex.closure_relint hC, supportFn_closure]

end SupportRelint

section RelintProjection

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- **Theorems 6.6 and 6.8 combined**: the relative interior of the projection on `X` of a convex
set `S ⊆ U × X` is the union, over `u` in the relative interior of the projection on `U`, of the
relative interiors of the slices of `S`.

Proof idea: `ri (A '' S) = A '' ri S` for the linear projection `A` (Theorem 6.6), and
`(u, x) ∈ ri S ↔ u ∈ ri (proj S) ∧ x ∈ ri (slice u)` (Theorem 6.8). -/
theorem relint_image_snd_eq_iUnion {S : Set (U × X)} (hS : Convex ℝ S) :
    ri (Prod.snd '' S) = ⋃ u ∈ ri (Prod.fst '' S), ri {x | (u, x) ∈ S} := by
  have hsnd : ri (Prod.snd '' S) = Prod.snd '' ri S := by
    have h := Convex.relint_image hS (LinearMap.snd ℝ U X)
    rwa [show ⇑(LinearMap.snd ℝ U X) = Prod.snd from rfl] at h
  rw [hsnd]
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    have h := (Convex.mem_relint_prod_iff hS (y := p.1) (z := p.2)).1 hp
    exact Set.mem_iUnion₂.2 ⟨p.1, h.1, h.2⟩
  · intro hx
    obtain ⟨u, hu, hx'⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨(u, x), (Convex.mem_relint_prod_iff hS).2 ⟨hu, hx'⟩, rfl⟩

end RelintProjection

section SupportUnion

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The support function of a set-indexed union is the pointwise supremum of the support
functions: `supportFn_iUnion` applied to the two nested unions of `⋃ i ∈ s, t i`. -/
theorem supportFn_biUnion {ι : Type*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set ι) (t : ι → Set E)
    (y : F) : supportFn B (⋃ i ∈ s, t i) y = ⨆ i ∈ s, supportFn B (t i) y := by
  simp only [supportFn_iUnion]

end SupportUnion

section Thm372

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- **The first effective domain of any `K ∈ Ω (F)` is `dom F`.** Rockafellar identifies `C` with
`dom F` silently throughout §37; this is the proof.

Proof idea: `cl₂` does not move `dom₁` (`dom₁_partialCl₂`), and on the interval `Ω (F)` the
operation `cl₂` is constant at the lower bracket (Theorem 34.2), whose `dom₁` is `dom F` because
`⟨Fu, y⟩ = -∞` exactly where `F u ≡ +∞`. -/
theorem dom₁_eq_domBifun_of_mem_bifunSaddleClass (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K) (hne : (dom₂ K).Nonempty) :
    dom₁ K = domBifun F := by
  have hcl₂ : partialCl₂ K = fun p : U × Y => bracket Bx F p.1 p.2 :=
    partialCl₂_eq_of_mem_saddleClass (partialCl₂_concaveBracket_adjoint Bu Bx hF hcl) hK
  rw [← dom₁_partialCl₂ hKcc hne, hcl₂, dom₁_bracket]

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- **The support function of `dom (F u)` is the recession function of `K (u, ·)`**, for `u` in
`ri (dom₁ K)` and `F = bifunOfSaddle Bx K`.

Proof idea: over `ri (dom₁ K)` the slice `K (u, ·)` is closed proper convex (Theorem 34.3) and
`F u` is its conjugate, so this is Theorem 13.3 for that slice, read through
`Bx.flip.flip = Bx`. -/
theorem recessionFn_slice_eq_supportFn_dom (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx.flip] (hK : ConcaveConvexFn K) (hs : ConvexSliceStructure K) {u : U}
    (hu : u ∈ ri (dom₁ K)) :
    recessionFn (fun y => K (u, y)) = supportFn Bx (dom (bifunOfSaddle Bx K u)) := by
  have hcpc : ClosedProperConvexFn fun y => K (u, y) :=
    ⟨hK.convex_snd u, hs.closedFn_slice u hu, hs.proper_slice u (intrinsicInterior_subset hu)⟩
  have h := recessionFn_eq_supportFn_dom_conj (B := Bx.flip) hcpc
  rwa [LinearMap.flip_flip] at h

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- **The inner half of Rockafellar, Theorem 37.2**: for `u` in `ri (dom₁ K)` the support function
of the slice `dom (F u)` — where `F = bifunOfSaddle Bx K` — is the difference quotient supremum
`sup_{y ∈ D} {K (u, y + w) - K (u, y)}`.

Proof idea: over `ri (dom₁ K)` the slice `K (u, ·)` is closed proper convex with effective domain
exactly `D = dom₂ K` (Theorem 34.3), and `F u` is its conjugate. Theorem 13.3 turns the support
function of `dom (F u) = dom (K (u, ·)*)` into the recession function of `K (u, ·)`, and
Theorem 8.5 evaluates that recession function as a supremum of difference quotients over the
effective domain. -/
theorem supportFn_dom_bifunOfSaddle_eq_iSup_sub (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx.flip] (hK : ConcaveConvexFn K) (hs : ConvexSliceStructure K) {u : U}
    (hu : u ∈ ri (dom₁ K)) (w : Y) :
    supportFn Bx (dom (bifunOfSaddle Bx K u)) w = ⨆ y ∈ dom₂ K, (K (u, y + w) - K (u, y)) := by
  have hconv : ConvexFn fun y => K (u, y) := hK.convex_snd u
  have hp : Proper fun y => K (u, y) := hs.proper_slice u (intrinsicInterior_subset hu)
  rw [← recessionFn_slice_eq_supportFn_dom Bx hK hs hu,
    recessionFn_apply_eq_iSup_sub hconv hp.ne_bot w, hs.dom_slice u hu]

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- The second effective domain of the upper conjugate is the projection of `dom F` on `X`: the
upper conjugate is the Lagrangian of `F` (Corollary 37.1.1) and `dom₂_saddleLagrangian` applies. -/
theorem dom₂_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    dom₂ (upperConjSaddle Bu Bx K) = Prod.snd '' dom (graphFn F) := by
  rw [upperConjSaddle_eq_saddleLagrangian Bu Bx hF hcl hK, dom₂_saddleLagrangian]

/-- **Rockafellar, Theorem 37.2** (the `D*` half): the support function of the second effective
domain of the conjugate saddle-function is

`δ*(w | D*) = sup_{u ∈ ri C} sup_{y ∈ D} {K (u, y + w) - K (u, y)}`,

where `C = dom₁ K` and `D = dom₂ K`.

Proof idea: `D*` is the projection of `dom F` on `X`, and a support function does not see the
relative interior. By Theorems 6.6 and 6.8 the relative interior of that projection is the union
over `u ∈ ri C` of the relative interiors of the slices `dom (F u)`, so the support function is the
supremum of the slice support functions; each of those is
`supportFn_dom_bifunOfSaddle_eq_iSup_sub`. -/
theorem supportFn_dom₂_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (hKcc : ConcaveConvexFn K) (hne : (dom₂ K).Nonempty) (hs : ConvexSliceStructure K) (w : Y) :
    supportFn Bx (dom₂ (upperConjSaddle Bu Bx K)) w
      = ⨆ u ∈ ri (dom₁ K), ⨆ y ∈ dom₂ K, (K (u, y + w) - K (u, y)) := by
  have hFK : bifunOfSaddle Bx K = F := bifunOfSaddle_eq_of_mem_bifunSaddleClass Bu Bx hF hcl hK
  have hG : Convex ℝ (dom (graphFn F)) := ConvexFn.convex_dom hF
  have hC : dom₁ K = Prod.fst '' dom (graphFn F) := by
    rw [dom₁_eq_domBifun_of_mem_bifunSaddleClass Bu Bx hF hcl hK hKcc hne, domBifun_eq_image_fst]
  have hsndconv : Convex ℝ (Prod.snd '' dom (graphFn F)) :=
    hG.linear_image (LinearMap.snd ℝ U X)
  calc supportFn Bx (dom₂ (upperConjSaddle Bu Bx K)) w
      = supportFn Bx (ri (Prod.snd '' dom (graphFn F))) w := by
        rw [dom₂_upperConjSaddle Bu Bx hF hcl hK, supportFn_relint Bx hsndconv]
    _ = supportFn Bx (⋃ u ∈ ri (dom₁ K), ri {x | (u, x) ∈ dom (graphFn F)}) w := by
        rw [relint_image_snd_eq_iUnion hG, hC]
    _ = ⨆ u ∈ ri (dom₁ K), supportFn Bx (ri {x | (u, x) ∈ dom (graphFn F)}) w :=
        supportFn_biUnion Bx (ri (dom₁ K)) (fun u => ri {x | (u, x) ∈ dom (graphFn F)}) w
    _ = ⨆ u ∈ ri (dom₁ K), ⨆ y ∈ dom₂ K, (K (u, y + w) - K (u, y)) := by
        refine iSup_congr fun u => iSup_congr fun hu => ?_
        have hslice : {x | (u, x) ∈ dom (graphFn F)} = dom (bifunOfSaddle Bx K u) := by
          rw [hFK]; rfl
        have hconvu : ConvexFn (bifunOfSaddle Bx K u) := by
          rw [hFK]; exact ConvexBifun.convexFn_apply hF u
        rw [hslice, supportFn_relint Bx (ConvexFn.convex_dom hconvu)]
        exact supportFn_dom_bifunOfSaddle_eq_iSup_sub Bx hKcc hs hu w

/-- **Rockafellar, Theorem 37.2**, in recession-function form: the support function of `D*` is the
pointwise supremum, over `u ∈ ri C`, of the recession functions of the slices `K (u, ·)`. This is
the shape the proof of Corollary 37.2.1 uses. -/
theorem supportFn_dom₂_upperConjSaddle_eq_iSup_recessionFn (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K) (hne : (dom₂ K).Nonempty)
    (hs : ConvexSliceStructure K) (w : Y) :
    supportFn Bx (dom₂ (upperConjSaddle Bu Bx K)) w
      = ⨆ u ∈ ri (dom₁ K), recessionFn (fun y => K (u, y)) w := by
  rw [supportFn_dom₂_upperConjSaddle Bu Bx hF hcl hK hKcc hne hs w]
  refine iSup_congr fun u => iSup_congr fun hu => ?_
  exact (supportFn_dom_bifunOfSaddle_eq_iSup_sub Bx hKcc hs hu w).symm.trans
    (congrFun (recessionFn_slice_eq_supportFn_dom Bx hKcc hs hu) w).symm

/-- **Rockafellar, Corollary 37.2.1** (the `D*` half): the origin is an interior point of `D*` if
and only if the convex functions `K (u, ·)`, for `u ∈ ri C`, have no common direction of recession
— that is, no `w ≠ 0` is a direction of recession of all of them at once.

Proof idea: `0 ∈ int D*` iff `δ*(w | D*) > 0` for every `w ≠ 0` (Theorem 13.1, `int` clause), and
Theorem 37.2 evaluates `δ*(w | D*)` as the supremum of the `(K (u, ·))∞ (w)`; a supremum is
positive exactly when one of its terms is.

`Bx.SeparatingRight` is the hypothesis that makes `w ≠ 0` and `⟨·, w⟩ ≠ 0` the same condition; in
Rockafellar's setting, where a space is paired with itself, it is automatic. -/
theorem zero_mem_interior_dom₂_upperConjSaddle_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hB : Bx.SeparatingRight) (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (hKcc : ConcaveConvexFn K) (hne : (dom₂ K).Nonempty) (hs : ConvexSliceStructure K) :
    (0 : X) ∈ interior (dom₂ (upperConjSaddle Bu Bx K)) ↔
      ∀ w : Y, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun y => K (u, y)) w := by
  have hconv : Convex ℝ (dom₂ (upperConjSaddle Bu Bx K)) :=
    (concaveConvexFn_upperConjSaddle Bu Bx hF hcl hK).convex_dom₂
  have hnex : (dom₂ (upperConjSaddle Bu Bx K)).Nonempty :=
    (properSaddleFn_upperConjSaddle Bu Bx hF hcl hpr hK).dom₂_nonempty
  rw [mem_interior_iff_lt_supportFn (B := Bx) hconv hnex hB 0]
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  rw [map_zero, LinearMap.zero_apply, _root_.EReal.coe_zero,
    supportFn_dom₂_upperConjSaddle_eq_iSup_recessionFn Bu Bx hF hcl hK hKcc hne hs w]
  simp only [lt_iSup_iff, exists_prop]

end Thm372

/-! ### Theorem 37.3: existence of the saddle-value -/

section Thm373

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

/-- **Rockafellar, Theorem 37.3**, condition (a): if the convex functions `K (u, ·)` for
`u ∈ ri C` have no common direction of recession, then the saddle-value of `K` exists.

Proof idea: Corollary 37.2.1 turns the recession hypothesis into `0 ∈ int D*`, hence into
`0 ∈ ri D*`, and Corollary 37.1.3 concludes. -/
theorem hasSaddleValue_of_no_common_direction_of_recession (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hB : Bx.SeparatingRight)
    (hF : ConvexBifun F) (hcl : ClosedBifun F) (hpr : Proper (graphFn F))
    (hK : K ∈ bifunSaddleClass Bu Bx F) (hKcc : ConcaveConvexFn K) (hne : (dom₂ K).Nonempty)
    (hs : ConvexSliceStructure K)
    (hrec : ∀ w : Y, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun y => K (u, y)) w) :
    HasSaddleValue K := by
  refine hasSaddleValue_of_mem_relint_dom₂_lowerConjSaddle Bu Bx hF hcl hpr hK ?_
  rw [dom₂_conjSaddle_eq Bu Bx hF hcl hpr hK]
  exact interior_subset_intrinsicInterior
    ((zero_mem_interior_dom₂_upperConjSaddle_iff Bu Bx hB hF hcl hpr hK hKcc hne hs).2 hrec)

end Thm373

section BoundedRecession

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal}

/-- **A function with a nonempty bounded effective domain has no nonzero direction of recession**:
`f0⁺ (w) > 0` for every `w ≠ 0`.

Proof idea: `f0⁺ (w) ≤ 0` makes `f` nonincreasing along `w`, so the whole ray `y₀ + a • w`,
`a ≥ 0`, stays in `dom f` (`add_smul_le_of_recessionFn_nonpos`). A ray in a direction `w ≠ 0`
leaves every ball, contradicting boundedness. -/
theorem lt_recessionFn_of_isBounded_dom (hne : (dom f).Nonempty)
    (hb : Bornology.IsBounded (dom f)) {w : E} (hw : w ≠ 0) : 0 < recessionFn f w := by
  rw [lt_iff_not_ge]
  intro h
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.1 hb
  have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw
  have hy₀r : ‖y₀‖ ≤ r := hr y₀ hy₀
  have hy₀nn : (0 : ℝ) ≤ ‖y₀‖ := norm_nonneg y₀
  set a : ℝ := (r + ‖y₀‖ + 1) / ‖w‖ with hadef
  have hann : (0 : ℝ) ≤ a := by
    rw [hadef]
    exact div_nonneg (by linarith) hwpos.le
  have hmem : y₀ + a • w ∈ dom f :=
    lt_of_le_of_lt (add_smul_le_of_recessionFn_nonpos h y₀ hann) hy₀
  have h1 : ‖y₀ + a • w‖ ≤ r := hr _ hmem
  have h2 : a * ‖w‖ = r + ‖y₀‖ + 1 := div_mul_cancel₀ _ (ne_of_gt hwpos)
  have h3 : ‖a • w‖ ≤ ‖y₀ + a • w‖ + ‖y₀‖ := by
    have hsub : (y₀ + a • w) - y₀ = a • w := add_sub_cancel_left y₀ (a • w)
    calc ‖a • w‖ = ‖(y₀ + a • w) - y₀‖ := by rw [hsub]
      _ ≤ ‖y₀ + a • w‖ + ‖y₀‖ := norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hann, h2] at h3
  linarith

end BoundedRecession

section Cor3731

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

/-- **Rockafellar, Corollary 37.3.1** (the `D` half): if the second effective domain of `K` is
bounded, the saddle-value of `K` exists. Over a compact `D` this is the classical minimax theorem.

Proof idea: for `u ∈ ri C` the slice `K (u, ·)` has effective domain exactly `D` (Theorem 34.3),
which is bounded, so it has no nonzero direction of recession; condition (a) of Theorem 37.3 is
therefore satisfied, and `ri C` is nonempty because `C` is. -/
theorem hasSaddleValue_of_isBounded_dom₂ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hB : Bx.SeparatingRight) (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (hKcc : ConcaveConvexFn K) (hne : (dom₂ K).Nonempty) (hne₁ : (dom₁ K).Nonempty)
    (hs : ConvexSliceStructure K) (hbd : Bornology.IsBounded (dom₂ K)) : HasSaddleValue K := by
  refine hasSaddleValue_of_no_common_direction_of_recession Bu Bx hB hF hcl hpr hK hKcc hne hs
    fun w hw => ?_
  obtain ⟨u, hu⟩ := Convex.relint_nonempty hKcc.convex_dom₁ hne₁
  have hdom : dom (fun y => K (u, y)) = dom₂ K := hs.dom_slice u hu
  exact ⟨u, hu, lt_recessionFn_of_isBounded_dom (by rw [hdom]; exact hne)
    (by rw [hdom]; exact hbd) hw⟩

end Cor3731

end Tdaf.ConvexAnalysis
