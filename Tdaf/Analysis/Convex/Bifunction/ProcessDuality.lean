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
* `ConvexProcess.isClosed_eval`, `ConvexProcess.concaveConvexFn_bracket_indicatorBifun`,
  `ConvexProcess.lowerClosedFn_bracket_indicatorBifun`,
  `ConvexProcess.eval_eq_supportSet_bracket_indicatorBifun` — the four properties of `⟨Au, x*⟩`
  that **Theorem 39.4** turns into a characterisation.
* `exists_unique_convexProcess_bracket_indicatorBifun_eq` — **Theorem 39.4**: a lower closed
  concave-convex `K` with `K (0, 0) = 0` that is positively homogeneous in each variable
  separately is `⟨Au, x*⟩` for exactly one closed convex process `A`.

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

**Theorem 39.4's "easy exercise" hides Corollary 7.2.1.** Rockafellar gets the correspondence from
Theorem 33.3 and leaves it to the reader that the bifunction `F` it produces is an indicator
bifunction. The step that needs an argument is that `F u` is nowhere `⊥` — without it,
`conj_eq_indicatorFn_of_posHomogeneous` does not apply and `F u` need not be `δ(· | ·)`. Nothing in
the hypotheses says so directly. What does say so is `K (0, 0) = 0`: it forces `F 0` to be
somewhere finite, and then Corollary 7.2.1 (`ConvexFn.eq_bot_or_eq_top`) applied to the closed
convex `graphFn F` spreads `≠ ⊥` to every `u`. So the book's hypotheses *are* sufficient — no extra
properness hypothesis is added here — but the exercise is not one line.

**Theorem 39.4 is stated as a `∃!`, with closedness inside it.** The correspondence is between
closed convex processes and kernels, so `IsClosed (A.graph)` belongs to the property being
characterised rather than to the hypotheses; uniqueness is then uniqueness among closed processes,
which is what `ConvexProcess.indicatorBifun_injective` and Theorem 33.3's own uniqueness deliver.

## What is not here

The infimum-oriented mirror of Theorem 39.4. Rockafellar states the correspondence for
supremum-oriented processes and notes that the infimum-oriented one is the same statement with
convexity and concavity exchanged; by gotcha 9 that mirror is not obtainable by `simp`-normalising
through negation, so it is a separate piece of work.

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

/-- Every value of a closed convex process is a closed set: `A u` is the preimage of the graph
under the continuous map `x ↦ (u, x)`. -/
theorem isClosed_eval {A : ConvexProcess U X} (hA : IsClosed (A.graph : Set (U × X))) (u : U) :
    IsClosed (A.eval u) :=
  hA.preimage (continuous_const.prodMk continuous_id)

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

/-! ### Theorem 39.4: which saddle-functions are inner products of processes

Theorem 33.3 matches the lower closed concave-convex functions on `U × Y` with the closed convex
bifunctions from `U` to `X`. Cutting it down to *processes* costs exactly two further conditions on
`K`: it vanishes at the origin, and it is positively homogeneous in each variable separately. -/

section Thm394

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {K : U × Y → EReal}

namespace ConvexProcess

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
  [LocallyConvexSpace ℝ U] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- **Rockafellar, Theorem 39.4**, the forward direction: the inner product of a convex process is
concave-convex. -/
theorem concaveConvexFn_bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    ConcaveConvexFn fun p : U × Y => bracket Bx A.indicatorBifun p.1 p.2 :=
  concaveConvexFn_bracket A.convexBifun_indicatorBifun Bx

/-- **Rockafellar, Theorem 39.4**, the forward direction: the inner product of a *closed* convex
process is lower closed. This is Theorem 33.3 read at the indicator bifunction. -/
theorem lowerClosedFn_bracket_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (A : ConvexProcess U X) (hA : IsClosed (A.graph : Set (U × X))) :
    LowerClosedFn fun p : U × Y => bracket Bx A.indicatorBifun p.1 p.2 :=
  lowerClosedFn_bracket Bu Bx A.convexBifun_indicatorBifun
    ((closedBifun_indicatorBifun_iff A).2 hA)

omit [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- **Rockafellar, Theorem 39.4**, second displayed relation: a closed convex process is recovered
from its inner product by `A u = {x | ⟨x, x*⟩ ≤ K (u, x*) for every x*}`.

This is Theorem 13.1 for the closed convex set `A u`, whose support function is `⟨Au, ·⟩`
(`bracket_indicatorBifun`). -/
theorem eval_eq_supportSet_bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] (A : ConvexProcess U X)
    (hA : IsClosed (A.graph : Set (U × X))) (u : U) :
    A.eval u = supportSet Bx.flip (bracket Bx A.indicatorBifun u) := by
  rw [bracket_indicatorBifun]
  exact (supportSet_supportFn (A.convex_eval u) (isClosed_eval hA u)).symm

end ConvexProcess

/-- **Rockafellar, Theorem 39.4**: `K (u, x*) = ⟨Au, x*⟩` is a one-to-one correspondence between
the closed convex processes from `U` to `X` and the lower closed concave-convex functions on
`U × Y` that vanish at the origin and are positively homogeneous in each variable separately. The
inverse map is `A u = {x | ⟨x, x*⟩ ≤ K (u, x*) for every x*}`
(`ConvexProcess.eval_eq_supportSet_bracket_indicatorBifun`).

Theorem 33.3 does all the work on the bifunction side; what remains is Rockafellar's "easy
exercise", that the closed convex bifunction it produces is an indicator bifunction. Three steps
do it. `K (0, 0) = 0` bounds `F 0` below by `0` and makes it finite somewhere, so the closed convex
`graphFn F` cannot take `-∞` (Corollary 7.2.1) and hence no slice `K (u, ·)` is identically `+∞`.
The conjugate of a positively homogeneous function that is not identically `+∞` is an indicator
function (`conj_eq_indicatorFn_of_posHomogeneous`), so each `F u` is one. And positive homogeneity
in `u` makes the resulting set a cone, its convexity coming from convexity of `F`. -/
theorem exists_unique_convexProcess_bracket_indicatorBifun_eq
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hK : ConcaveConvexFn K) (hlc : LowerClosedFn K) (hK₀ : K (0, 0) = 0)
    (hhu : ∀ y : Y, PosHomogeneous fun u : U => K (u, y))
    (hhy : ∀ u : U, PosHomogeneous fun y : Y => K (u, y)) :
    ∃! A : ConvexProcess U X, IsClosed (A.graph : Set (U × X)) ∧
      (fun p : U × Y => bracket Bx A.indicatorBifun p.1 p.2) = K := by
  obtain ⟨F, ⟨hFconv, hFcl, hFbr⟩, huniq⟩ := exists_unique_convexBifun_bracket_eq Bu Bx hK hlc
  have hbr0 : ∀ (u : U) (y : Y), conj Bx (F u) y = K (u, y) := fun u y => congrFun hFbr (u, y)
  -- `K (0, 0) = 0` bounds `F 0` below and makes it finite somewhere.
  have hzero : ∀ x : X, (0 : EReal) ≤ F 0 x := by
    intro x
    have h1 : ((Bx x (0 : Y) : ℝ) : EReal) - F 0 x ≤ K (0, 0) := by
      rw [← hbr0 0 0]
      exact sub_le_conj Bx (F 0) x 0
    rw [hK₀, map_zero, _root_.EReal.coe_zero] at h1
    have hz : (0 : EReal) - F 0 x = -(F 0 x) := zero_add _
    rw [hz] at h1
    have h3 := _root_.EReal.neg_le.1 h1
    rwa [neg_zero] at h3
  have hex0 : ∃ x : X, F 0 x ≠ ⊤ := by
    by_contra hc
    push Not at hc
    have hbot : conj Bx (F 0) (0 : Y) = ⊥ := conj_eq_bot_iff.2 hc
    rw [hbr0 0 0, hK₀] at hbot
    exact absurd hbot (by simp)
  -- Hence `graphFn F` never takes `-∞`: Corollary 7.2.1 would otherwise forbid both.
  have hFnb : ∀ (u : U) (x : X), F u x ≠ ⊥ := by
    intro u x hux
    obtain ⟨x₀, hx₀⟩ := hex0
    have hgc : ConvexFn (graphFn F) := hFconv
    have hcl' : ClosedFn (graphFn F) := hFcl
    have hgbot : graphFn F (u, x) = ⊥ := hux
    rcases hgc.eq_bot_or_eq_top (ClosedFn.lowerSemicontinuous hcl') ⟨(u, x), hgbot⟩ (0, x₀) with
      h | h
    · have h' : F 0 x₀ = ⊥ := h
      have hle := hzero x₀
      rw [h'] at hle
      exact absurd hle (by simp)
    · exact hx₀ h
  -- `F u` is the conjugate of `K (u, ·)`, because a closed bifunction is image-closed.
  have hFconj : ∀ u : U, F u = conj Bx.flip (fun y : Y => K (u, y)) := by
    intro u
    have hcl : clFn (F u) = F u := ClosedBifun.imageClosedBifun hFcl u
    have h1 : clFn (F u) = conj Bx.flip (bracket Bx F u) := clFn_eq_conj_bracket hFconv u
    have h2 : bracket Bx F u = fun y : Y => K (u, y) := funext fun y => hbr0 u y
    rw [hcl, h2] at h1
    exact h1
  have hKne : ∀ u : U, ∃ y : Y, K (u, y) ≠ ⊤ := by
    intro u
    by_contra hc
    push Not at hc
    have hbot : conj Bx.flip (fun y : Y => K (u, y)) (0 : X) = ⊥ := conj_eq_bot_iff.2 hc
    rw [← hFconj u] at hbot
    exact hFnb u 0 hbot
  have hK0nb : ∀ y : Y, K (0, y) ≠ ⊥ := by
    intro y
    obtain ⟨x₀, hx₀⟩ := hex0
    rw [← hbr0 0 y]
    exact conj_ne_bot ⟨x₀, lt_top_iff_ne_top.2 hx₀⟩ y
  have hK0nn : ∀ y : Y, (0 : EReal) ≤ K (0, y) := by
    intro y
    have htri : K (0, y) = 0 ∨ K (0, y) = ⊤ ∨ K (0, y) = ⊥ :=
      (hhu y).map_zero_trichotomy
    rcases htri with h | h | h
    · exact le_of_eq h.symm
    · rw [h]; exact le_top
    · exact absurd h (hK0nb y)
  -- Each `F u` is an indicator function, `K (u, ·)` being positively homogeneous.
  have hFind : ∀ u : U,
      F u = indicatorFn {x : X | ∀ y : Y, ((Bx x y : ℝ) : EReal) ≤ K (u, y)} := by
    intro u
    have hset : supportSet Bx.flip (fun y : Y => K (u, y))
        = {x : X | ∀ y : Y, ((Bx x y : ℝ) : EReal) ≤ K (u, y)} := rfl
    rw [hFconj u, conj_eq_indicatorFn_of_posHomogeneous (B := Bx.flip) (hhy u) (hKne u), hset]
  -- The graph of the process to come.
  obtain ⟨G, hG⟩ : ∃ S : Set (U × X),
      S = {p : U × X | ∀ y : Y, ((Bx p.2 y : ℝ) : EReal) ≤ K (p.1, y)} := ⟨_, rfl⟩
  have hmem : ∀ p : U × X, p ∈ G ↔ ∀ y : Y, ((Bx p.2 y : ℝ) : EReal) ≤ K (p.1, y) := by
    rw [hG]; exact fun _ => Iff.rfl
  have hgraphFn : graphFn F = indicatorFn G := by
    funext p
    rw [graphFn_apply, hFind p.1]
    by_cases hp : p ∈ G
    · have h1 : p.2 ∈ {x : X | ∀ y : Y, ((Bx x y : ℝ) : EReal) ≤ K (p.1, y)} := (hmem p).1 hp
      rw [indicatorFn_of_mem h1, indicatorFn_of_mem hp]
    · have h1 : p.2 ∉ {x : X | ∀ y : Y, ((Bx x y : ℝ) : EReal) ≤ K (p.1, y)} :=
        fun hc => hp ((hmem p).2 hc)
      rw [indicatorFn_of_notMem h1, indicatorFn_of_notMem hp]
  have hGconv : Convex ℝ G := by
    refine convexFn_indicatorFn.1 ?_
    rw [← hgraphFn]
    exact hFconv
  have hG0 : (0 : U × X) ∈ G := by
    refine (hmem 0).2 fun y => ?_
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero, LinearMap.zero_apply,
      _root_.EReal.coe_zero]
    exact hK0nn y
  have hGsmul : ∀ c : ℝ, 0 ≤ c → ∀ p ∈ G, c • p ∈ G := by
    intro c hc p hp
    rcases eq_or_lt_of_le hc with rfl | hcpos
    · rw [zero_smul]
      exact hG0
    · refine (hmem _).2 fun y => ?_
      have hK' : K ((c • p).1, y) = (c : EReal) * K (p.1, y) := hhu y c hcpos p.1
      have hB : ((Bx (c • p).2 y : ℝ) : EReal) = (c : EReal) * ((Bx p.2 y : ℝ) : EReal) := by
        simp only [Prod.smul_snd, map_smul, smul_eq_mul, LinearMap.smul_apply]
        rw [_root_.EReal.coe_mul]
      rw [hK', hB]
      exact mul_le_mul_of_nonneg_left ((hmem p).1 hp y) (by exact_mod_cast hcpos.le)
  have hGadd : ∀ p ∈ G, ∀ q ∈ G, p + q ∈ G := by
    intro p hp q hq
    have hmid : (2 : ℝ)⁻¹ • p + (2 : ℝ)⁻¹ • q ∈ G :=
      hGconv hp hq (by norm_num) (by norm_num) (by norm_num)
    have h2 := hGsmul 2 (by norm_num) _ hmid
    have hval : (2 : ℝ) • ((2 : ℝ)⁻¹ • p + (2 : ℝ)⁻¹ • q) = p + q := by
      rw [smul_add, smul_smul, smul_smul]
      norm_num
    rwa [hval] at h2
  obtain ⟨A, hAgraph⟩ : ∃ A : ConvexProcess U X, (A.graph : Set (U × X)) = G :=
    ⟨⟨{ carrier := G
        zero_mem' := hG0
        add_mem' := fun {p q} hp hq => hGadd p hp q hq
        smul_mem' := fun c p hp => hGsmul (c : ℝ) c.2 p hp }⟩, rfl⟩
  have hAind : A.indicatorBifun = F := by
    funext u x
    have heval : A.eval u = {z : X | ∀ y : Y, ((Bx z y : ℝ) : EReal) ≤ K (u, y)} := by
      ext z
      rw [ConvexProcess.mem_eval, ← SetLike.mem_coe, hAgraph]
      exact hmem (u, z)
    rw [ConvexProcess.indicatorBifun_apply, heval, hFind u]
  refine ⟨A, ⟨?_, ?_⟩, ?_⟩
  · exact (ConvexProcess.closedBifun_indicatorBifun_iff A).1 (by rw [hAind]; exact hFcl)
  · rw [hAind]; exact hFbr
  · rintro A' ⟨hA'cl, hA'br⟩
    refine ConvexProcess.indicatorBifun_injective ?_
    rw [hAind]
    exact huniq A'.indicatorBifun
      ⟨A'.convexBifun_indicatorBifun, (ConvexProcess.closedBifun_indicatorBifun_iff A').2 hA'cl,
        hA'br⟩

end Thm394

end Tdaf.ConvexAnalysis
