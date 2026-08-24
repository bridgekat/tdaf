/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Pairing
import Tdaf.Analysis.Convex.Operations.Closed
import Tdaf.Analysis.Convex.Optimization.Lagrangian

/-!
# Adjoint bifunctions and dual programs

Rockafellar's §30. The **adjoint** of a convex bifunction `F : U → X → EReal` is the concave
bifunction

`(F* y)(v) = ⨅ (u, x) {F u x - ⟨x, y⟩ + ⟨u, v⟩}`,

and the concave program `(P*)` dual to `(P)` is "maximise `F* 0` over `V`". The point of the
section is that the adjoint is the conjugate of the graph function, read with a sign flip on the
first factor.

## Main definitions

* `adjointBifun Bu Bx F` — Rockafellar's `F*`.
* `concaveAdjointBifun Bu Bx G` — the adjoint of a *concave* bifunction: the same formula with a
  supremum in place of the infimum.
* `ConcaveBifun` — a bifunction whose graph function is concave.
* `clBifun F`, `ClosedBifun F` — Rockafellar's `cl F` and its fixed points: the closure is taken
  on the graph function, jointly in `(u, x)`.

## Main results

* `adjointBifun_eq_neg_conj_graphFn` — **Theorem 30.1**'s computation: `(F* y)(v) = -f*(-v, y)`
  where `f` is the graph function of `F` and `f*` is its conjugate under `prodPairing`.
* `concaveFn_graphFn_adjointBifun`, `closedConcaveFn_graphFn_adjointBifun`,
  `concaveBifun_adjointBifun` — **Theorem 30.1**: `F*` is a *closed* concave bifunction, with no
  hypothesis on `F` at all.
* `concaveAdjointBifun_adjointBifun_eq_clBifun` — **Theorem 30.1**'s biconjugation, `F** = cl F`;
* `exists_adjointBifun_ne_bot` — **Theorem 30.1**'s properness half: the adjoint of a closed
  proper convex bifunction is finite somewhere.
  `concaveAdjointBifun_adjointBifun_eq_self` is the fixed-point form for closed convex `F`.
* `adjointBifun_zero_eq_concaveConj` — **Theorem 30.2**: the dual objective `F* 0` is the *concave*
  conjugate of the concave function `-inf F`.
* `adjointBifun_zero_le` — **Corollary 30.2.2**, weak duality: every dual value is below the
  optimal value of `(P)`.
* `mem_kuhnTucker_iff_adjointBifun_zero_eq` — the Kuhn–Tucker vectors are exactly the `v` at which
  the dual objective attains the optimal value of `(P)`; this is the half of **Theorem 30.5** that
  holds without normality.

## Design notes

**The sign flip lives in the argument, not in a new pairing.** Rockafellar reads
`⟨u, -v⟩ + ⟨x, y⟩` as the pairing of `(u, x)` with `(-v, y)`, so `F*` is `conj` at a reflected
point rather than `conj` for the reflected pairing `negFst (prodPairing Bu Bx)`. Both descriptions
are available; the reflected-point one keeps `conj`'s own lemmas usable verbatim, which is why
`concaveFn_graphFn_adjointBifun` is `convexFn_conj` composed with a linear reflection.

**The two finite terms are grouped inside a single coercion.** `F u x - ⟨x, y⟩ + ⟨u, v⟩` is written
`F u x + ((⟨u, v⟩ - ⟨x, y⟩ : ℝ) : EReal)`, which is the same number and never produces `∞ - ∞`.

**Closedness travels along the reflection, once the reflection is linear.** `adjointSwap` is a
`LinearMap`, so `closedFn_compLin` (`Operations/Closed.lean`) applies; the instance binder must be
`[IsContinuousPairing (prodPairing Bu Bx).flip]`, not the un-flipped form, because `closedFn_conj`
asks for continuity on the side where the conjugate lives. The un-flipped class would demand a
topology on `U × X`, which nothing in §30 supplies.

**The two reflections cancel by reindexing, not by cancellation of signs.** `F*` is a conjugate
at `adjointSwap q = (-v, y)` and `F**` is a conjugate of that at the same reflection, so `F**` is a
supremum over `q : Y × V` of the biconjugate's summands evaluated at `adjointSwap q`.
`adjointSwap` is onto (`surjective_adjointSwap`), and `Function.Surjective.iSup_comp` turns that
supremum into the biconjugate itself. No sign lemma is needed anywhere in
`concaveAdjointBifun_adjointBifun_eq_biconj`; the whole content is the reindexing.

**Fenchel–Moreau on `U × X` comes from the factors.** `biconj_eq_clFn` asks for
`IsCompatiblePairing (prodPairing Bu Bx)`, and `Duality/Pairing.lean` now derives it from
compatibility of `Bu` and `Bx` (`instIsCompatiblePairingProd`) — a continuous functional on
`U × X` splits as `g (u, 0) + g (0, x)`. Mathlib supplies the rest of the product structure, so
Theorem 30.1 needs no hypothesis about `U × X` itself.

**Theorem 30.2 needs the concave conjugate.** `F* 0` is the conjugate of `-inf F` *as a concave
function*; it is not the convex conjugate of `inf F`, and `g* ≠ -(-g)*`. Everything here goes
through `concaveConj`.

## What is not here

**Theorems 30.3, 30.4 and 30.5.** Normality (Theorems 30.3 and 30.4) is a statement about
`cl (inf F)` at the origin, so it needs §7's closure operations transported to `infBifun` — which
is *not* `clBifun`, the joint closure defined here — and the "sufficient conditions" of
Theorem 30.4 are §16's exactness results again. Theorem 30.5's converse half needs normality
too; the direction that holds without it is `mem_kuhnTucker_iff_adjointBifun_zero_eq`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §30 (Theorem 30.1,
  Theorem 30.2, Corollary 30.2.2).
-/

namespace Tdaf.ConvexAnalysis

section Defs

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {v : V} {y : Y}

/-- The **adjoint** of a convex bifunction: `(F* y)(v) = ⨅ (u, x) {F u x - ⟨x, y⟩ + ⟨u, v⟩}`. The
result is a *concave* bifunction from `Y` to `V`. -/
noncomputable def adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun Y V :=
  fun y v => ⨅ p : U × X, (F p.1 p.2 + ((Bu p.1 v - Bx p.2 y : ℝ) : EReal))

theorem adjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X)
    (y : Y) (v : V) :
    adjointBifun Bu Bx F y v = ⨅ p : U × X, (F p.1 p.2 + ((Bu p.1 v - Bx p.2 y : ℝ) : EReal)) :=
  rfl

/-- Negating a difference in which the subtrahend is the only infinite term. -/
private theorem neg_coe_sub {c : ℝ} {w : EReal} :
    -(((-c : ℝ) : EReal) - w) = w + (c : EReal) := by
  rw [sub_eq_add_neg, _root_.EReal.neg_add (.inl (_root_.EReal.coe_ne_bot _))
      (.inl (_root_.EReal.coe_ne_top _)), sub_eq_add_neg, neg_neg, _root_.EReal.coe_neg, neg_neg,
    add_comm]

/-- **Rockafellar, Theorem 30.1**, the computation the whole section rests on: the adjoint is the
conjugate of the graph function, negated and evaluated at a reflected point. -/
theorem adjointBifun_eq_neg_conj_graphFn (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (y : Y) (v : V) :
    adjointBifun Bu Bx F y v = -(conj (prodPairing Bu Bx) (graphFn F) (-v, y)) := by
  rw [adjointBifun_apply, conj_apply, Tdaf.EReal.neg_iSup]
  refine iInf_congr fun p => ?_
  have hpair : (prodPairing Bu Bx p (-v, y) : ℝ) = -(Bu p.1 v - Bx p.2 y) := by
    rw [prodPairing_apply, map_neg]
    ring
  rw [hpair]
  exact (neg_coe_sub).symm

end Defs

/-! ### Theorem 30.1: the adjoint is a closed concave bifunction -/

section Closed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- A bifunction is **concave** when its graph function is. This is what the adjoint operation
produces (Theorem 30.1) and what the concave adjoint consumes. -/
def ConcaveBifun (G : Bifun U X) : Prop := ConcaveFn (graphFn G)

theorem concaveBifun_iff {G : Bifun U X} : ConcaveBifun G ↔ ConcaveFn (graphFn G) := Iff.rfl

/-- The reflection `(y, v) ↦ (-v, y)` that turns the adjoint into a conjugate. -/
def adjointSwap (V Y : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup Y] [Module ℝ Y] :
    (Y × V) →ₗ[ℝ] (V × Y) :=
  LinearMap.prod (-LinearMap.snd ℝ Y V) (LinearMap.fst ℝ Y V)

@[simp] theorem adjointSwap_apply (V Y : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup Y]
    [Module ℝ Y] (q : Y × V) : adjointSwap V Y q = (-q.2, q.1) := rfl

/-- The graph function of the adjoint is minus a conjugate composed with a linear reflection. -/
theorem graphFn_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : graphFn (adjointBifun Bu Bx F)
      = fun q => -(compLin (conj (prodPairing Bu Bx) (graphFn F)) (adjointSwap V Y) q) :=
  funext fun q => adjointBifun_eq_neg_conj_graphFn Bu Bx F q.1 q.2

/-- **Rockafellar, Theorem 30.1**, concavity half: the adjoint of *any* bifunction is a concave
bifunction. No convexity, properness or closedness of `F` is needed — the conjugate does the
work. -/
theorem concaveFn_graphFn_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConcaveFn (graphFn (adjointBifun Bu Bx F)) := by
  rw [concaveFn_iff_convexFn_neg]
  have h : (fun q => -(graphFn (adjointBifun Bu Bx F) q))
      = compLin (conj (prodPairing Bu Bx) (graphFn F)) (adjointSwap V Y) := by
    funext q
    rw [graphFn_adjointBifun, neg_neg]
  rw [h]
  exact convexFn_compLin _ (convexFn_conj _ _)

/-- **Rockafellar, Theorem 30.1**, concavity half, packaged as a statement about bifunctions. -/
theorem concaveBifun_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConcaveBifun (adjointBifun Bu Bx F) :=
  concaveFn_graphFn_adjointBifun Bu Bx F

end Closed

section ClosedTopology

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing (prodPairing Bu Bx).flip] {F : Bifun U X}

omit [IsTopologicalAddGroup Y] [IsContinuousPairing (prodPairing Bu Bx).flip] in
theorem continuous_adjointSwap : Continuous (adjointSwap V Y) := by
  change Continuous fun q : Y × V => ((-q.2, q.1) : V × Y)
  exact (continuous_neg.comp continuous_snd).prodMk continuous_fst

/-- **Rockafellar, Theorem 30.1**, closedness half: the adjoint of *any* bifunction is
concave-closed. Like the concavity clause it needs no hypothesis on `F`: the conjugate is closed
(`closedFn_conj`) and closedness survives the linear reflection (`closedFn_compLin`). -/
theorem closedConcaveFn_graphFn_adjointBifun :
    ClosedConcaveFn (graphFn (adjointBifun Bu Bx F)) := by
  rw [closedConcaveFn_iff]
  have h : (fun q => -(graphFn (adjointBifun Bu Bx F) q))
      = compLin (conj (prodPairing Bu Bx) (graphFn F)) (adjointSwap V Y) := by
    funext q
    rw [graphFn_adjointBifun, neg_neg]
  rw [h]
  exact closedFn_compLin closedFn_conj continuous_adjointSwap

end ClosedTopology

/-! ### The closure of a bifunction -/

section BifunClosure

variable {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {F : Bifun U X}

/-- The **closure of a bifunction**: the bifunction whose graph function is the closure of the
graph function of `F`. Rockafellar defines `cl F` exactly this way in §30, and Theorem 30.1 says
that it is what the adjoint operation returns after two applications. -/
noncomputable def clBifun (F : Bifun U X) : Bifun U X := fun u x => clFn (graphFn F) (u, x)

theorem clBifun_apply (F : Bifun U X) (u : U) (x : X) :
    clBifun F u x = clFn (graphFn F) (u, x) := rfl

@[simp] theorem graphFn_clBifun (F : Bifun U X) : graphFn (clBifun F) = clFn (graphFn F) := rfl

/-- A bifunction is **closed** when its graph function is. -/
def ClosedBifun (F : Bifun U X) : Prop := ClosedFn (graphFn F)

theorem closedBifun_iff : ClosedBifun F ↔ ClosedFn (graphFn F) := Iff.rfl

theorem clBifun_le (F : Bifun U X) : clBifun F ≤ F := fun u x => clFn_le (graphFn F) (u, x)

theorem ClosedBifun.clBifun_eq (hF : ClosedBifun F) : clBifun F = F :=
  funext fun u => funext fun x => congrFun hF (u, x)

theorem closedBifun_iff_clBifun_eq : ClosedBifun F ↔ clBifun F = F := by
  refine ⟨fun hF => hF.clBifun_eq, fun hF => ?_⟩
  change clFn (graphFn F) = graphFn F
  exact funext fun p => congrFun (congrFun hF p.1) p.2

end BifunClosure

section BifunClosureClosed

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]

theorem closedBifun_clBifun (F : Bifun U X) : ClosedBifun (clBifun F) :=
  closedFn_clFn (graphFn F)

end BifunClosureClosed

section ImageClosed

variable {U X : Type*} [TopologicalSpace X] {F : Bifun U X}

/-- A bifunction is **image-closed** when each of its values `F u` is a closed function.
Rockafellar's brackets see only this much of `F`, which is why §33's correspondence is stated for
image-closed bifunctions. -/
def ImageClosedBifun (F : Bifun U X) : Prop := ∀ u, ClosedFn (F u)

theorem imageClosedBifun_iff : ImageClosedBifun F ↔ ∀ u, ClosedFn (F u) := Iff.rfl

end ImageClosed

section ImageClosedSlice

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {F : Bifun U X}

/-- A closed bifunction is image-closed: a slice of a closed function is closed. The converse
fails — image-closedness says nothing about the joint behaviour in `(u, x)`. -/
theorem ClosedBifun.imageClosedBifun (hF : ClosedBifun F) : ImageClosedBifun F := by
  intro u
  rcases closedFn_iff.1 (closedBifun_iff.1 hF) with h | ⟨hlsc, hne⟩
  · exact closedFn_iff.2 (Or.inl (funext fun x => congrFun h (u, x)))
  · exact closedFn_iff.2 (Or.inr ⟨lowerSemicontinuous_comp hlsc
      (continuous_const.prodMk continuous_id), fun x => hne (u, x)⟩)

end ImageClosedSlice

section BifunClosureConvex

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [TopologicalSpace X] [AddCommGroup X]
  [Module ℝ X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] {F : Bifun U X}

theorem ConvexBifun.clBifun (hF : ConvexBifun F) : ConvexBifun (Tdaf.ConvexAnalysis.clBifun F) :=
  convexFn_clFn hF

end BifunClosureConvex

section AdjointClosure

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [TopologicalSpace X] [IsTopologicalAddGroup X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsContinuousPairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing Bx] {F : Bifun U X}

/-- **The adjoint sees only the closure**: `(cl F)* = F*`. This is `conj_clFn` read on the graph
function, and it is what makes the closure operations of §34 terminate. -/
theorem adjointBifun_clBifun : adjointBifun Bu Bx (clBifun F) = adjointBifun Bu Bx F := by
  funext y v
  rw [adjointBifun_eq_neg_conj_graphFn, adjointBifun_eq_neg_conj_graphFn, graphFn_clBifun,
    conj_clFn]

end AdjointClosure

/-! ### Theorem 30.1: `F** = cl F` -/

section ConcaveAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **adjoint of a concave bifunction**: the defining formula of `adjointBifun` with the
infimum replaced by a supremum. A concave `G` from `Y` to `V` has an adjoint `G*` from `U` to
`X`. -/
noncomputable def concaveAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G : Bifun Y V) : Bifun U X :=
  fun u x => ⨆ q : Y × V, (G q.1 q.2 + ((Bx x q.1 - Bu u q.2 : ℝ) : EReal))

theorem concaveAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G : Bifun Y V) (u : U) (x : X) :
    concaveAdjointBifun Bu Bx G u x
      = ⨆ q : Y × V, (G q.1 q.2 + ((Bx x q.1 - Bu u q.2 : ℝ) : EReal)) := rfl

/-- The reflection is onto: `(y, v) ↦ (-v, y)` hits `(v, y)` at `(y, -v)`. -/
theorem surjective_adjointSwap : Function.Surjective (adjointSwap V Y) :=
  fun w => ⟨(w.2, -w.1), by rw [adjointSwap_apply, neg_neg]⟩

/-- **Rockafellar, Theorem 30.1**, the algebraic core of the biconjugation: applying the concave
adjoint to `F*` gives the *biconjugate* of the graph function of `F`. Both adjoints are conjugates
read at reflected points, and the two reflections cancel — which is `surjective_adjointSwap`
reindexing the supremum. -/
theorem concaveAdjointBifun_adjointBifun_eq_biconj (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (u : U) (x : X) :
    concaveAdjointBifun Bu Bx (adjointBifun Bu Bx F) u x
      = biconj (prodPairing Bu Bx) (graphFn F) (u, x) := by
  rw [concaveAdjointBifun_apply, biconj_apply,
    ← (surjective_adjointSwap (V := V) (Y := Y)).iSup_comp
      (fun w : V × Y => ((prodPairing Bu Bx (u, x) w : ℝ) : EReal)
        - conj (prodPairing Bu Bx) (graphFn F) w)]
  refine iSup_congr fun q => ?_
  rw [adjointBifun_eq_neg_conj_graphFn, adjointSwap_apply]
  have hpair : (prodPairing Bu Bx (u, x) (-q.2, q.1) : ℝ) = Bx x q.1 - Bu u q.2 := by
    rw [prodPairing_apply, map_neg]
    ring
  rw [hpair]
  exact add_comm _ _

end ConcaveAdjoint

section Thm301

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F : Bifun U X}

/-- **Rockafellar, Theorem 30.1**: `F** = cl F`. The two adjoints compose to the biconjugate of the
graph function, and Fenchel–Moreau turns that into its closure. The product pairing is compatible
because both factors are (`instIsCompatiblePairingProd`), so no hypothesis beyond compatibility of
`Bu` and `Bx` is needed. -/
theorem concaveAdjointBifun_adjointBifun_eq_clBifun (hF : ConvexBifun F) :
    concaveAdjointBifun Bu Bx (adjointBifun Bu Bx F) = clBifun F := by
  funext u x
  rw [concaveAdjointBifun_adjointBifun_eq_biconj, clBifun_apply]
  exact congrFun (biconj_eq_clFn (B := prodPairing Bu Bx) hF) (u, x)

/-- **Rockafellar, Theorem 30.1**, the fixed-point form: `F** = F` for a closed convex
bifunction. -/
theorem concaveAdjointBifun_adjointBifun_eq_self (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    concaveAdjointBifun Bu Bx (adjointBifun Bu Bx F) = F := by
  rw [concaveAdjointBifun_adjointBifun_eq_clBifun hF, hcl.clBifun_eq]

/-- **Rockafellar, Theorem 30.1**, properness half: the adjoint of a *closed proper* convex
bifunction is finite somewhere.

`concaveFn_graphFn_adjointBifun` and `closedConcaveFn_graphFn_adjointBifun` say that `F*` is
closed concave with no hypothesis at all; this supplies the remaining clause of "`F*` is a closed
proper concave bifunction". The proof is Theorem 12.2's properness half (`proper_conj`) read
through `adjointBifun_eq_neg_conj_graphFn`: `F*` is the negated conjugate of the graph function at
a reflected point, so `F*` is somewhere `> -∞` exactly when `(graph F)*` is somewhere `< +∞`. -/
theorem exists_adjointBifun_ne_bot (hF : ClosedProperConvexFn (graphFn F)) :
    ∃ (y : Y) (v : V), adjointBifun Bu Bx F y v ≠ ⊥ := by
  obtain ⟨q, hq⟩ := (proper_conj (B := prodPairing Bu Bx) hF).dom_nonempty
  refine ⟨q.2, -q.1, ?_⟩
  rw [adjointBifun_eq_neg_conj_graphFn, neg_neg]
  simpa using hq.ne

end Thm301

/-! ### Theorem 30.2: the dual objective -/

section Dual

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {v : V}

/-- The dual objective, unfolded: `(F* 0)(v) = ⨅ u (⟨u, v⟩ + inf F u)`. -/
theorem adjointBifun_zero_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (v : V) :
    adjointBifun Bu Bx F 0 v = ⨅ u, (((Bu u v : ℝ) : EReal) + infBifun F u) := by
  rw [adjointBifun_apply, iInf_prod]
  refine iInf_congr fun u => ?_
  have hzero : ∀ x : X, (Bu u v - Bx x 0 : ℝ) = Bu u v := fun x => by
    rw [map_zero, sub_zero]
  simp only [hzero]
  rw [infBifun_apply, add_comm, Tdaf.EReal.iInf_add_coe]

/-- **Rockafellar, Theorem 30.2**: the objective function of the dual program is the *concave*
conjugate of the concave function `-inf F`. -/
theorem adjointBifun_zero_eq_concaveConj (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) :
    adjointBifun Bu Bx F 0 = concaveConj Bu (fun u => -(infBifun F u)) := by
  funext v
  rw [adjointBifun_zero_apply, concaveConj_apply]
  exact iInf_congr fun u => by rw [sub_eq_add_neg, neg_neg]

/-- **Rockafellar, Corollary 30.2.2** (weak duality): every value of the dual objective is at most
the optimal value of `(P)`. This needs no hypothesis at all. -/
theorem adjointBifun_zero_le (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X)
    (v : V) : adjointBifun Bu Bx F 0 v ≤ infBifun F 0 := by
  rw [adjointBifun_zero_apply]
  exact iInf_add_infBifun_le Bu F v

/-- **Rockafellar, Theorem 30.5**, the half that holds without normality: the Kuhn–Tucker vectors
of `(P)` are exactly the points at which the dual objective attains the optimal value of `(P)`. -/
theorem mem_kuhnTucker_iff_adjointBifun_zero_eq (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    v ∈ KuhnTucker Bu F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      adjointBifun Bu Bx F 0 v = infBifun F 0 := by
  rw [KuhnTucker, Set.mem_ofPred_eq, adjointBifun_zero_apply]

/-- **Rockafellar, Corollary 30.2.2**, in the form used for normality: the supremum of the dual
objective never exceeds the optimal value of `(P)`. -/
theorem iSup_adjointBifun_zero_le (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : (⨆ v, adjointBifun Bu Bx F 0 v) ≤ infBifun F 0 :=
  iSup_le (adjointBifun_zero_le Bu Bx F)

end Dual

end Tdaf.ConvexAnalysis
