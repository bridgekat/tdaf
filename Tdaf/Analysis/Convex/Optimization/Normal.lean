/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Optimization.Adjoint

/-!
# Normality of a dual pair of convex programs

Rockafellar's §30, from Corollary 30.2.2 onwards. A convex program `(P)` is **normal** when its
perturbation function is closed at the origin,

`(cl (inf F))(0) = (inf F)(0)`,

and the point of the section is that this single condition is equivalent to the absence of a
duality gap, and to normality of the dual program `(P*)`.

The computation behind all of it is `clFn_zero_eq_iSup_iInf`: for a convex `f`,

`(cl f)(0) = ⨆ y, ⨅ x, (⟨x, y⟩ + f x)`,

which is Fenchel–Moreau read at the origin. Applied to `f = inf F` the inner infimum is exactly the
dual objective `(F* 0)(y)` (`adjointBifun_zero_apply`), so `(cl (inf F))(0) = sup F* 0` — the first
formula of Corollary 30.2.2.

## Main definitions

* `Normal F` — Rockafellar's normality of the convex program associated with `F`.
* `supBifun G` — the concave counterpart of `infBifun`: the optimal value of the concave program
  `G y` as a function of the perturbation `y`.
* `domConcaveBifun G`, `ConcaveConsistent G`, `ConcaveStronglyConsistent G`, `ConcaveNormal G` —
  the concave counterparts of `domBifun`, `Consistent`, `StronglyConsistent` and `Normal`, needed
  to state the dual half of every result here.

## Main results

* `clFn_infBifun_zero_eq_iSup_adjointBifun`, `clConcave_supBifun_adjointBifun_zero_eq` —
  **Corollary 30.2.2**, the two closure formulas.
* `normal_iff_iSup_adjointBifun_eq`, `concaveNormal_adjointBifun_iff`,
  `normal_iff_concaveNormal_adjointBifun` — **Theorem 30.3**, the three equivalent conditions.
* `StronglyConsistent.normal`, `normal_of_concaveStronglyConsistent_adjointBifun`,
  `normal_of_kuhnTucker_nonempty` — **Theorem 30.4**, clauses (a), (b) and (c).
* `mem_kuhnTucker_iff_adjointBifun_zero_eq_iSup`, `kuhnTucker_eq_setOf_isMax` — **Theorem 30.5**:
  under normality the Kuhn–Tucker vectors of `(P)` are precisely the optimal solutions of `(P*)`.

## Implementation notes

**Corollary 30.2.2 needs no closedness for its first formula.** Rockafellar states the whole
corollary for closed convex `F`. The formula `(cl (inf F))(0) = sup F* 0` only uses Fenchel–Moreau
for `inf F`, so `ConvexBifun F` suffices; closedness of `F` enters only in the second formula,
where `F** = cl F` has to be turned back into `F`. Consequently the equivalence (a) ⟺ (c) of
Theorem 30.3 holds for every convex bifunction, and only (b) needs `ClosedBifun F`.

**Theorem 30.4(c) does not go through subgradients.** Rockafellar's own argument for (c) is
Theorem 23.5; here `mem_kuhnTucker_iff_adjointBifun_zero_eq` already says that a Kuhn–Tucker vector
is a point where the dual objective attains `inf F 0`, and weak duality
(`iSup_adjointBifun_zero_le`) then pins the dual optimal value down, so normality is immediate from
Theorem 30.3. This also removes the finite-dimensionality that the subgradient route would need.

**The concave mirror of Theorem 7.4 is not proved here.** It is
`ConcaveFn.clConcave_eq_of_mem_relint_domConcave` in `Saddle/Kernel.lean`, together with the rest
of its family; `Normal.lean` cannot import that module, so `ConcaveStronglyConsistent.concaveNormal`
inlines the two-line proof. Both copies want a common home: the `clConcave` block of
`Duality/ConcaveConj.lean` split into a `ConcaveClosure.lean` that `RelativeInterior.lean` can
import, so the concave Theorem 7.4 can sit next to the convex one.
-/

namespace Tdaf.ConvexAnalysis

/-! ### The closure of a convex function at the origin -/

section ClosureAtZero

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- Negating a difference whose minuend is finite. -/
private theorem neg_coe_sub_eq {c : ℝ} {w : EReal} :
    -(((c : ℝ) : EReal) - w) = w + ((-c : ℝ) : EReal) := by
  rw [sub_eq_add_neg, _root_.EReal.neg_add (.inl (_root_.EReal.coe_ne_bot _))
      (.inl (_root_.EReal.coe_ne_top _)), sub_eq_add_neg, neg_neg, ← _root_.EReal.coe_neg,
    add_comm]

/-- **Fenchel–Moreau at the origin.** For a convex `f`, the closure at `0` is the supremum over the
dual variable of the infimum of the affine functions `x ↦ ⟨x, y⟩ + f x`.

This is the one computation §30 rests on: with `f = inf F` the inner infimum is the dual objective
`(F* 0)(y)`, so this reads `(cl (inf F))(0) = sup F* 0`. -/
theorem clFn_zero_eq_iSup_iInf (hf : ConvexFn f) :
    clFn f 0 = ⨆ y : F, ⨅ x : E, (((B x y : ℝ) : EReal) + f x) := by
  have hsurj : Function.Surjective (fun y : F => -y) := fun y => ⟨-y, neg_neg y⟩
  have hterm : ∀ y : F, ((B (0 : E) y : ℝ) : EReal) - conj B f y
      = ⨅ x : E, (((B x (-y) : ℝ) : EReal) + f x) := by
    intro y
    rw [map_zero, LinearMap.zero_apply, _root_.EReal.coe_zero, zero_sub, conj_apply,
      Tdaf.EReal.neg_iSup]
    refine iInf_congr fun x => ?_
    have hb : (B x (-y) : ℝ) = -(B x y) := by rw [map_neg]
    rw [neg_coe_sub_eq, hb, add_comm]
  rw [← biconj_eq_clFn (B := B) hf, biconj_apply, iSup_congr hterm]
  exact hsurj.iSup_comp fun y : F => ⨅ x : E, (((B x y : ℝ) : EReal) + f x)

end ClosureAtZero

/-! ### Normality -/

section Normal

variable {U X : Type*} [AddCommGroup U] [TopologicalSpace U] {F : Bifun U X}

/-- A convex program is **normal** when its perturbation function is closed at the origin
(Rockafellar §30):

`(cl (inf F))(0) = (inf F)(0)`.

When `0 ∈ cl (dom F)` this is exactly lower semicontinuity of `u ↦ inf F u` at `u = 0`: without it
the program is unstable in some direction of perturbation. -/
def Normal (F : Bifun U X) : Prop := clFn (infBifun F) 0 = infBifun F 0

theorem normal_iff : Normal F ↔ clFn (infBifun F) 0 = infBifun F 0 := Iff.rfl

end Normal

/-! ### The concave counterparts of §29's vocabulary -/

section ConcaveVocabulary

variable {V Y : Type*} {G : Bifun Y V}

/-- The optimal value of the concave program `G y`, as a function of the perturbation `y`: the
mirror of `infBifun`. Rockafellar writes `sup G`. -/
noncomputable def supBifun (G : Bifun Y V) : Y → EReal := fun y => ⨆ v, G y v

theorem supBifun_apply (G : Bifun Y V) (y : Y) : supBifun G y = ⨆ v, G y v := rfl

/-- The mirror of `domBifun`: the perturbations for which the concave program is consistent. -/
def domConcaveBifun (G : Bifun Y V) : Set Y := {y | ∃ v, G y v ≠ ⊥}

theorem mem_domConcaveBifun {y : Y} : y ∈ domConcaveBifun G ↔ ∃ v, G y v ≠ ⊥ := Iff.rfl

/-- Negating a concave bifunction turns its `sup` into the `inf` of the negation. -/
theorem neg_supBifun (G : Bifun Y V) :
    (fun y => -(supBifun G y)) = infBifun fun y v => -(G y v) := by
  funext y
  rw [supBifun_apply, Tdaf.EReal.neg_iSup, infBifun_apply]

/-- The mirror of `dom_infBifun`. -/
theorem domConcave_supBifun (G : Bifun Y V) : domConcave (supBifun G) = domConcaveBifun G := by
  ext y
  simp only [mem_domConcave, supBifun_apply, mem_domConcaveBifun, bot_lt_iff_ne_bot, ne_eq,
    iSup_eq_bot, not_forall]

end ConcaveVocabulary

section ConcaveConsistency

variable {V Y : Type*} [AddCommGroup Y] {G : Bifun Y V}

/-- The mirror of `Consistent`: the unperturbed concave program has a point where it is not
`-∞`. -/
def ConcaveConsistent (G : Bifun Y V) : Prop := (0 : Y) ∈ domConcaveBifun G

theorem concaveConsistent_iff : ConcaveConsistent G ↔ ∃ v, G 0 v ≠ ⊥ := Iff.rfl

end ConcaveConsistency

section ConcaveNormality

variable {V Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] {G : Bifun Y V}

/-- The mirror of `Normal` for a concave program: `(cl (sup G))(0) = (sup G)(0)`, the closure taken
in the concave sense. -/
def ConcaveNormal (G : Bifun Y V) : Prop := clConcave (supBifun G) 0 = supBifun G 0

theorem concaveNormal_iff : ConcaveNormal G ↔ clConcave (supBifun G) 0 = supBifun G 0 := Iff.rfl

end ConcaveNormality

section ConcaveStrongConsistency

variable {V Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {G : Bifun Y V}

/-- The mirror of `StronglyConsistent`. -/
def ConcaveStronglyConsistent (G : Bifun Y V) : Prop := (0 : Y) ∈ ri (domConcaveBifun G)

theorem ConcaveStronglyConsistent.concaveConsistent (h : ConcaveStronglyConsistent G) :
    ConcaveConsistent G :=
  intrinsicInterior_subset h

end ConcaveStrongConsistency

/-! ### Concavity of the dual perturbation function -/

section ConcaveFnSup

variable {V Y : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup Y] [Module ℝ Y]
  {G : Bifun Y V}

/-- The mirror of `convexFn_infBifun`: the optimal value of a concave program is a concave function
of the perturbation. -/
theorem concaveFn_supBifun (hG : ConcaveBifun G) : ConcaveFn (supBifun G) :=
  concaveFn_iff_convexFn_neg.2 (by
    rw [neg_supBifun]
    exact convexFn_infBifun (concaveFn_iff_convexFn_neg.1 hG))

end ConcaveFnSup

/-! ### Corollary 30.2.2: the two optimal values -/

section Cor3022

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X}

/-- **Rockafellar, Corollary 30.2.2**, first formula: `(cl (inf F))(0) = sup F* 0`.

Unlike in the book, `F` need not be closed: the formula is Fenchel–Moreau for `inf F`, and `F*`
does not see the difference between `F` and `cl F` anyway (`adjointBifun_clBifun`). -/
theorem clFn_infBifun_zero_eq_iSup_adjointBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    clFn (infBifun F) 0 = ⨆ v : V, adjointBifun Bu Bx F 0 v := by
  rw [clFn_zero_eq_iSup_iInf (B := Bu) (convexFn_infBifun hF)]
  exact iSup_congr fun v => (adjointBifun_zero_apply Bu Bx F v).symm

/-- **Rockafellar, Theorem 30.3**, (a) ⟺ (c): normality is exactly the absence of a duality gap. -/
theorem normal_iff_iSup_adjointBifun_eq (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    Normal F ↔ (⨆ v : V, adjointBifun Bu Bx F 0 v) = infBifun F 0 := by
  rw [normal_iff, clFn_infBifun_zero_eq_iSup_adjointBifun (Bu := Bu) Bx hF]

end Cor3022

section Cor3022Dual

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx.flip]
  {G : Bifun Y V}

/-- Negating a sum whose second summand is finite. -/
private theorem neg_neg_add_coe {a : EReal} {c : ℝ} :
    -(-a + (c : EReal)) = a + ((-c : ℝ) : EReal) := by
  rw [_root_.EReal.neg_add (.inr (_root_.EReal.coe_ne_top _)) (.inr (_root_.EReal.coe_ne_bot _)),
    neg_neg, sub_eq_add_neg, ← _root_.EReal.coe_neg]

/-- The dual of `clFn_infBifun_zero_eq_iSup_adjointBifun`, obtained from it by negation: the
concave closure of the dual perturbation function at the origin is the optimal value of the program
associated with the *concave* adjoint. -/
theorem clConcave_supBifun_zero_eq_infBifun_concaveAdjointBifun (hG : ConcaveBifun G) :
    clConcave (supBifun G) 0 = infBifun (concaveAdjointBifun Bu Bx G) 0 := by
  have hsurj : Function.Surjective (fun x : X => -x) := fun x => ⟨-x, neg_neg x⟩
  have hneg : ConvexBifun fun y v => -(G y v) := concaveFn_iff_convexFn_neg.1 hG
  have hpt : ∀ x : X, -(adjointBifun Bx.flip Bu.flip (fun y v => -(G y v)) 0 x)
      = concaveAdjointBifun Bu Bx G 0 (-x) := by
    intro x
    rw [adjointBifun_apply, Tdaf.EReal.neg_iInf, concaveAdjointBifun_apply]
    refine iSup_congr fun q => ?_
    have h1 : (Bx.flip q.1 x - Bu.flip q.2 (0 : U) : ℝ) = Bx x q.1 := by
      rw [LinearMap.flip_apply, LinearMap.flip_apply, map_zero, LinearMap.zero_apply, sub_zero]
    have h2 : (Bx (-x) q.1 - Bu (0 : U) q.2 : ℝ) = -(Bx x q.1) := by
      rw [map_zero, LinearMap.zero_apply, sub_zero, map_neg, LinearMap.neg_apply]
    rw [h1, h2, neg_neg_add_coe]
  rw [clConcave_apply, neg_supBifun,
    clFn_infBifun_zero_eq_iSup_adjointBifun (Bu := Bx.flip) Bu.flip hneg, Tdaf.EReal.neg_iSup,
    iInf_congr hpt]
  exact hsurj.iInf_comp fun x : X => concaveAdjointBifun Bu Bx G 0 x

end Cor3022Dual

/-! ### Theorem 30.3: normality of `(P)`, of `(P*)`, and the absence of a duality gap -/

section Thm303

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- **Rockafellar, Corollary 30.2.2**, second formula: `(cl (sup F*))(0) = inf F 0` for a closed
convex bifunction. Closedness is what turns `F**` back into `F`. -/
theorem clConcave_supBifun_adjointBifun_zero_eq (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    clConcave (supBifun (adjointBifun Bu Bx F)) 0 = infBifun F 0 := by
  rw [clConcave_supBifun_zero_eq_infBifun_concaveAdjointBifun (Bu := Bu) (Bx := Bx)
      (concaveBifun_adjointBifun Bu Bx F),
    concaveAdjointBifun_adjointBifun_eq_clBifun hF, hcl.clBifun_eq]

/-- **Rockafellar, Theorem 30.3**, (b) ⟺ (c). -/
theorem concaveNormal_adjointBifun_iff (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    ConcaveNormal (adjointBifun Bu Bx F)
      ↔ (⨆ v : V, adjointBifun Bu Bx F 0 v) = infBifun F 0 := by
  rw [concaveNormal_iff, clConcave_supBifun_adjointBifun_zero_eq hF hcl]
  exact eq_comm

/-- **Rockafellar, Theorem 30.3**, (a) ⟺ (b): a convex program is normal exactly when its dual
is. -/
theorem normal_iff_concaveNormal_adjointBifun (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    Normal F ↔ ConcaveNormal (adjointBifun Bu Bx F) :=
  (normal_iff_iSup_adjointBifun_eq (Bu := Bu) Bx hF).trans
    (concaveNormal_adjointBifun_iff hF hcl).symm

end Thm303

/-! ### Theorem 30.4: sufficient conditions for normality -/

section Thm304KuhnTucker

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X} {v : V}

/-- **Rockafellar, Theorem 30.4(c)**: if a Kuhn–Tucker vector exists then normality holds. (The
finiteness of the optimal value that the book asks for is already part of `KuhnTucker`.)

A Kuhn–Tucker vector is a point at which the dual objective reaches `inf F 0`
(`mem_kuhnTucker_iff_adjointBifun_zero_eq`), and weak duality says it can never exceed it, so the
dual optimal value *is* `inf F 0`. -/
theorem normal_of_kuhnTucker_nonempty (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F)
    (h : (KuhnTucker Bu F).Nonempty) : Normal F := by
  obtain ⟨w, hw⟩ := h
  rw [mem_kuhnTucker_iff_adjointBifun_zero_eq (Bx := Bx)] at hw
  rw [normal_iff_iSup_adjointBifun_eq (Bu := Bu) Bx hF]
  refine le_antisymm (iSup_adjointBifun_zero_le Bu Bx F) ?_
  rw [← hw.2.2]
  exact le_iSup (fun z : V => adjointBifun Bu Bx F 0 z) w

/-- **Rockafellar, Theorem 30.5**: under normality the Kuhn–Tucker vectors of `(P)` are exactly the
optimal solutions of `(P*)`. -/
theorem mem_kuhnTucker_iff_adjointBifun_zero_eq_iSup (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F)
    (hn : Normal F) (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    v ∈ KuhnTucker Bu F
      ↔ adjointBifun Bu Bx F 0 v = ⨆ w : V, adjointBifun Bu Bx F 0 w := by
  rw [mem_kuhnTucker_iff_adjointBifun_zero_eq (Bx := Bx),
    (normal_iff_iSup_adjointBifun_eq (Bu := Bu) Bx hF).1 hn]
  exact ⟨fun h => h.2.2, fun h => ⟨ht, hb, h⟩⟩

/-- **Rockafellar, Theorem 30.5**, as an equation between sets. -/
theorem kuhnTucker_eq_setOf_isMax (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) (hn : Normal F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker Bu F
      = {v : V | adjointBifun Bu Bx F 0 v = ⨆ w : V, adjointBifun Bu Bx F 0 w} :=
  Set.ext fun _ => mem_kuhnTucker_iff_adjointBifun_zero_eq_iSup Bx hF hn ht hb

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
  [LocallyConvexSpace ℝ U] [IsCompatiblePairing Bu] in
/-- A Kuhn–Tucker vector is a dual optimal solution, and the common optimal value is `inf F 0`.
This half of Theorem 30.5 needs no normality hypothesis: existence of a Kuhn–Tucker vector supplies
it (`normal_of_kuhnTucker_nonempty`). -/
theorem isGreatest_adjointBifun_zero_of_mem_kuhnTucker (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hv : v ∈ KuhnTucker Bu F) :
    IsGreatest (Set.range (adjointBifun Bu Bx F 0)) (infBifun F 0) := by
  rw [mem_kuhnTucker_iff_adjointBifun_zero_eq (Bx := Bx)] at hv
  exact ⟨⟨v, hv.2.2⟩, by rintro _ ⟨w, rfl⟩; exact adjointBifun_zero_le Bu Bx F w⟩

end Thm304KuhnTucker

section Thm304Strong

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup X] [Module ℝ X] {F : Bifun U X}

/-- **Rockafellar, Theorem 30.4(a)**: a strongly consistent convex program is normal. This is
Theorem 7.4 for `inf F`: the origin is a relative interior point of its effective domain, and `cl`
changes nothing there. -/
theorem StronglyConsistent.normal (hs : StronglyConsistent F) (hF : ConvexBifun F) : Normal F := by
  have hri : (0 : U) ∈ ri (dom (infBifun F)) := by rwa [dom_infBifun]
  exact (convexFn_infBifun hF).clFn_eq_of_mem_relint_dom hri

/-- **Rockafellar, Theorem 30.4(a)**, strict form. -/
theorem StrictlyConsistent.normal (hs : StrictlyConsistent F) (hF : ConvexBifun F) : Normal F :=
  hs.stronglyConsistent.normal hF

end Thm304Strong

/-! ### The concave mirror of Theorem 7.4, and Theorem 30.4(b) -/

section ConcaveThm304

variable {V Y : Type*} [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] {G : Bifun Y V}

/-- The concave mirror of **Theorem 30.4(a)**: a strongly consistent concave program is normal. -/
theorem ConcaveStronglyConsistent.concaveNormal (hs : ConcaveStronglyConsistent G)
    (hG : ConcaveBifun G) : ConcaveNormal G := by
  have hri : (0 : Y) ∈ ri (dom fun z => -(supBifun G z)) := by
    rw [← domConcave_eq_dom_neg, domConcave_supBifun]
    exact hs
  rw [ConcaveNormal, clConcave_apply,
    (concaveFn_supBifun hG).convexFn_neg.clFn_eq_of_mem_relint_dom hri, neg_neg]

end ConcaveThm304

section Thm304Dual

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- **Rockafellar, Theorem 30.4(b)**: if the *dual* program is strongly consistent then normality
holds for the pair. -/
theorem normal_of_concaveStronglyConsistent_adjointBifun (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hs : ConcaveStronglyConsistent (adjointBifun Bu Bx F)) : Normal F :=
  (normal_iff_concaveNormal_adjointBifun hF hcl).2
    (hs.concaveNormal (concaveBifun_adjointBifun Bu Bx F))

end Thm304Dual

end Tdaf.ConvexAnalysis
