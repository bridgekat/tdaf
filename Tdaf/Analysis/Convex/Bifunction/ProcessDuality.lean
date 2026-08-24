/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Bifunction.Process
import Tdaf.Analysis.Convex.Saddle.Kernel

/-!
# The two inner products of a convex process

Rockafellar's §39, Theorem 39.3. A convex process `A` carries two inner products,

  `⟨Au, x*⟩ = sup {⟨x, x*⟩ | x ∈ A u}`  and  `⟨u, A* x*⟩ = inf {⟨u, u*⟩ | u* ∈ A* x*}`,

the first a maximisation over a value of `A`, the second a minimisation over a value of `A*`. They
are the bracket and the concave bracket of §33, taken at the indicator bifunction of `A` and at its
adjoint, so everything that separates them is a partial closure. `Bifunction/Process.lean` proves
the clauses that need only Theorem 33.2's first equation; this module adds the ones that need the
*second* — closedness of `A` — and the ones that need relative interiors.

## Main results

* `ConvexProcess.closedBifun_indicatorBifun_iff` — `A` is a closed convex process exactly when its
  indicator bifunction is a closed convex bifunction.
* `ConvexProcess.domConcaveBifun_adjointBifun_indicatorBifun` — `dom (F*) = dom (A*)`.
* `ConvexProcess.partialCl₂_concaveBracket_adjointBifun_indicatorBifun` — **Theorem 39.3**, fourth
  assertion: `⟨Au, x*⟩ = cl_{x*} ⟨u, A* x*⟩` for a closed convex process.
* `bracket_eq_concaveBracket_adjointBifun_of_mem_relint_domConcaveBifun` — the dual half of
  **Corollary 33.2.1**, for a general closed convex bifunction: the two brackets agree at every
  relative interior point of `dom F*`.
* `ConvexProcess.bracket_eq_concaveBracket_of_mem_relint_dom` and
  `ConvexProcess.bracket_eq_concaveBracket_of_mem_relint_dom_adjoint` — **Theorem 39.3**, last
  assertion: `⟨Au, x*⟩ = ⟨u, A* x*⟩` whenever `u ∈ ri (dom A)` or `x* ∈ ri (dom A*)`.

## Design notes

**The `u` side of Theorem 39.3's last assertion needs no closedness.** Rockafellar prefixes both
halves with "if `A` is closed", but the `u` half is Corollary 33.2.1, whose only input is that a
concave function agrees with its concave closure on the relative interior of its effective domain.
Closedness is genuinely needed only on the `x*` side, where Theorem 33.2's *second* equation —
which rests on `F** = cl F` — is what identifies `cl_{x*} ⟨u, A* x*⟩` with `⟨Au, x*⟩`.

**Closedness of a process is closedness of its indicator bifunction, in both directions.**
`clFn (δ(· | S)) = δ(· | cl S)` (Rockafellar §7) makes the equivalence an unfolding, once one
observes that `δ(· | ·)` is injective as a function of the set. This is what lets the §33 theorems
be applied to a process without a separate closedness argument.

**The dual half of Corollary 33.2.1 was missing from the backbone.** `Saddle/Kernel.lean` proves
only the `u` side; the `y` side is its mirror, with `ConvexFn.clFn_eq_of_mem_relint_dom` in place
of `ConcaveFn.clConcave_eq_of_mem_relint_domConcave` and `dom_concaveBracket` in place of
`domConcave_bracket`, and it needs `Y` finite-dimensional rather than `U`. It is stated here for a
general bifunction because that is the level at which it is true; see the relocation note.

## What is not here

Theorem 39.4 — the one-to-one correspondence between lower closed positively homogeneous
concave-convex functions vanishing at the origin and closed convex processes. Theorem 33.3 supplies
the correspondence with closed convex *bifunctions*; what is missing is Rockafellar's "easy
exercise", namely that the bifunction produced by Theorem 33.3 is an indicator bifunction exactly
when `K` carries the extra homogeneity.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §39.
-/

open Set

namespace Tdaf.ConvexAnalysis

/-! ### Closedness, and the effective domain of the adjoint -/

section Closedness

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [TopologicalSpace U]
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]

namespace ConvexProcess

/-- A convex process is closed exactly when its indicator bifunction is a closed convex
bifunction.

The indicator function of a set determines the set, and `cl δ(· | S) = δ(· | cl S)`
(`clFn_indicatorFn`), so `ClosedBifun` for an indicator bifunction *is* `closure (graph A) =
graph A`. This is the bridge that lets §33's theorems be read for processes. -/
theorem closedBifun_indicatorBifun_iff (A : ConvexProcess U X) :
    ClosedBifun A.indicatorBifun ↔ IsClosed (A.graph : Set (U × X)) := by
  have hgr : ClosedBifun A.indicatorBifun
      ↔ clFn (indicatorFn (A.graph : Set (U × X))) = indicatorFn (A.graph : Set (U × X)) := by
    rw [ClosedBifun, graphFn_indicatorBifun]
    exact Iff.rfl
  rw [hgr, clFn_indicatorFn, ← closure_eq_iff_isClosed]
  constructor
  · intro h
    refine Subset.antisymm (fun p hp => ?_) subset_closure
    by_contra hc
    have e1 : indicatorFn (closure (A.graph : Set (U × X))) p = 0 := indicatorFn_of_mem hp
    rw [h, indicatorFn_of_notMem hc] at e1
    exact absurd e1 (by simp)
  · intro h
    rw [h]

end ConvexProcess

end Closedness

section DomAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- The concave effective domain of the adjoint of an indicator bifunction is the effective domain
of the adjoint process: `⟨u, A* x*⟩` is `+∞` exactly where `A* x*` is empty. This is the last
missing entry of the §38/§39 dictionary. -/
@[simp] theorem domConcaveBifun_adjointBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    domConcaveBifun (adjointBifun Bu Bx A.indicatorBifun) = (adjointProcess Bu Bx A).dom := by
  ext y
  simp only [mem_domConcaveBifun, mem_dom, Set.Nonempty]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    by_contra hc
    exact hv (by
      simp [adjointBifun_indicatorBifun, indicatorBifun_apply, indicatorFn_of_notMem hc])
  · rintro ⟨v, hv⟩
    exact ⟨v, by
      simp [adjointBifun_indicatorBifun, indicatorBifun_apply, indicatorFn_of_mem hv]⟩

end ConvexProcess

end DomAdjoint

/-! ### Theorem 39.3 for a closed convex process -/

section Thm393Closed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]

namespace ConvexProcess

/-- **Rockafellar, Theorem 39.3**, fourth assertion: for a *closed* convex process,
`⟨Au, x*⟩ = cl_{x*} ⟨u, A* x*⟩`.

This is Theorem 33.2's second equation, which is where closedness enters: it runs through
`F** = cl F = F`, whereas the first equation `⟨u, A* x*⟩ = cl_u ⟨Au, x*⟩`
(`concaveBracket_adjointBifun_indicatorBifun_eq_partialCl₁`) holds for every convex process. -/
theorem partialCl₂_concaveBracket_adjointBifun_indicatorBifun (A : ConvexProcess U X)
    (hA : IsClosed (A.graph : Set (U × X))) :
    partialCl₂ (fun p : U × Y =>
        concaveBracket Bu (adjointBifun Bu Bx A.indicatorBifun) p.1 p.2)
      = fun p : U × Y => bracket Bx A.indicatorBifun p.1 p.2 :=
  partialCl₂_concaveBracket_adjoint Bu Bx A.convexBifun_indicatorBifun
    ((closedBifun_indicatorBifun_iff A).2 hA)

end ConvexProcess

end Thm393Closed

/-! ### Corollary 33.2.1 on the dual side -/

section Cor3321Dual

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- **Rockafellar, Corollary 33.2.1**, on the dual side: for a closed convex bifunction the two
brackets `⟨Fu, y⟩` and `⟨u, F* y⟩` already agree at every relative interior point of `dom F*`.

The proof is the mirror of `bracket_eq_concaveBracket_adjointBifun_of_mem_relint`: Theorem 33.2's
second equation says the two differ by the convex closure in `y`; `⟨u, F*·⟩` is convex with
effective domain `dom F*` (`convexFn_concaveBracket`, `dom_concaveBracket`), and a convex function
agrees with its closure on the relative interior of its effective domain. Note that it is `Y`, not
`U`, that has to be finite-dimensional. -/
theorem bracket_eq_concaveBracket_adjointBifun_of_mem_relint_domConcaveBifun
    (hF : ConvexBifun F) (hcl : ClosedBifun F) (u : U)
    {y : Y} (hy : y ∈ ri (domConcaveBifun (adjointBifun Bu Bx F))) :
    bracket Bx F u y = concaveBracket Bu (adjointBifun Bu Bx F) u y := by
  have hcl2 : clFn (fun w => concaveBracket Bu (adjointBifun Bu Bx F) u w) y
      = bracket Bx F u y :=
    congrFun (partialCl₂_concaveBracket_adjoint Bu Bx hF hcl) (u, y)
  rw [← hcl2]
  exact ConvexFn.clFn_eq_of_mem_relint_dom
    (convexFn_concaveBracket (concaveBifun_adjointBifun Bu Bx F) Bu u)
    (by rw [dom_concaveBracket]; exact hy)

end Cor3321Dual

/-! ### Theorem 39.3: where the two inner products agree -/

section Thm393RelintDom

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}

namespace ConvexProcess

/-- **Rockafellar, Theorem 39.3**, last assertion, on the `u` side: `⟨Au, x*⟩ = ⟨u, A* x*⟩` at
every relative interior point of `dom A`.

Rockafellar prefixes the assertion with "if `A` is closed"; **no closedness is needed here**. The
statement is Corollary 33.2.1 for the indicator bifunction, and Corollary 33.2.1 asks only that a
concave function meet its concave closure on `ri` of its effective domain. -/
theorem bracket_eq_concaveBracket_of_mem_relint_dom (A : ConvexProcess U X) {u : U}
    (hu : u ∈ ri A.dom) (y : Y) :
    bracket Bx A.indicatorBifun u y
      = concaveBracket Bu (adjointBifun Bu Bx A.indicatorBifun) u y :=
  bracket_eq_concaveBracket_adjointBifun_of_mem_relint Bu Bx A.convexBifun_indicatorBifun
    (by rw [domBifun_indicatorBifun]; exact hu) y

end ConvexProcess

end Thm393RelintDom

section Thm393RelintDomAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]

namespace ConvexProcess

/-- **Rockafellar, Theorem 39.3**, last assertion, on the `x*` side: for a *closed* convex process,
`⟨Au, x*⟩ = ⟨u, A* x*⟩` at every relative interior point of `dom A*`, and for every `u`.

Unlike the `u` side, this one really does need `A` closed: it goes through Theorem 33.2's second
equation. -/
theorem bracket_eq_concaveBracket_of_mem_relint_dom_adjoint (A : ConvexProcess U X)
    (hA : IsClosed (A.graph : Set (U × X))) (u : U)
    {y : Y} (hy : y ∈ ri (adjointProcess Bu Bx A).dom) :
    bracket Bx A.indicatorBifun u y
      = concaveBracket Bu (adjointBifun Bu Bx A.indicatorBifun) u y :=
  bracket_eq_concaveBracket_adjointBifun_of_mem_relint_domConcaveBifun
    A.convexBifun_indicatorBifun ((closedBifun_indicatorBifun_iff A).2 hA) u
    (by rw [domConcaveBifun_adjointBifun_indicatorBifun]; exact hy)

end ConvexProcess

end Thm393RelintDomAdjoint

end Tdaf.ConvexAnalysis
