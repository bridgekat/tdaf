/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Operations.Image
import Tdaf.Analysis.Convex.Subgradient.Existence

/-!
# Convex bifunctions and generalized convex programs

Rockafellar's §29. A *bifunction* `F : U → X → EReal` is a family of minimisation problems indexed
by a perturbation parameter `u`. The **generalized convex program** `(P)` associated with `F` is
"minimise `F 0` over `X`, with the perturbations `F u` on offer"; its **perturbation function** is
`inf F : u ↦ ⨅ x, F u x`, and its **Kuhn–Tucker vectors** are the prices at which no perturbation
is worth buying.

## Main definitions

* `Bifun U X` — a bifunction, i.e. a curried `U → X → EReal`.
* `graphFn F` — the same data as a function on `U × X`; `ConvexBifun F` is convexity of it.
* `infBifun F` — the perturbation function `inf F`.
* `domBifun F` — the effective domain `{u | F u ≢ ⊤}`.
* `KuhnTucker B F` — Rockafellar's Kuhn–Tucker vectors, defined exactly as in the book: the `v`
  for which `⨅ u (⟨u, v⟩ + inf F u)` is finite and equal to the optimal value `inf F 0`.
* `Consistent`, `StronglyConsistent`, `StrictlyConsistent` — the constraint qualifications of
  Part VI, as `0 ∈ dom F`, `0 ∈ ri (dom F)` and `0 ∈ int (dom F)`.

## Main results

* `convexFn_infBifun`, `dom_infBifun` — **Theorem 29.1**, first assertion: the perturbation
  function is convex and its effective domain is `dom F`.
* `mem_kuhnTucker_iff_forall_le` — the reformulation Rockafellar gives immediately after the
  definition: `v` is a Kuhn–Tucker vector iff `inf F 0` is finite and `inf F u + ⟨u, v⟩ ≥ inf F 0`
  for every `u`.
* `mem_kuhnTucker_iff_neg_mem_subgradient` — **Theorem 29.1**, second assertion: when the optimal
  value is finite, `v` is a Kuhn–Tucker vector exactly when `-v ∈ ∂(inf F)(0)`.
* `kuhnTucker_eq_neg_subgradient`, `convex_kuhnTucker`, `isClosed_kuhnTucker` — the Kuhn–Tucker set
  is a reflected subdifferential, hence closed and convex (part of Corollary 29.1.1).
* `kuhnTucker_nonempty_of_stronglyConsistent` — Theorem 23.4 applied to `inf F`: a strongly
  consistent program has a Kuhn–Tucker vector.

## Design notes

**`KuhnTucker` is Rockafellar's definition, not Theorem 29.1's conclusion.** The book defines `v`
to be a Kuhn–Tucker vector when `⨅ u (⟨u, v⟩ + inf F u)` is finite and equal to `inf F 0`; the
inequality form `inf F 0 ≤ ⟨u, v⟩ + inf F u` is a two-line consequence
(`mem_kuhnTucker_iff_forall_le`), because the infimum is automatically `≤ inf F 0` by evaluating at
`u = 0`. Defining `KuhnTucker` by the inequality would have made Theorem 29.1 an `Iff.rfl`.

**The perturbation function is a partial minimisation, not a new construction.**
`infBifun F = mapLin (LinearMap.fst ℝ U X) (graphFn F)` up to unfolding, so `convexFn_iInf_right`
(Theorem 5.7 at a projection) proves Theorem 29.1's convexity clause with no separate argument.

**The Kuhn–Tucker set carries the sign flip.** `v ∈ KuhnTucker B F ↔ -v ∈ ∂(inf F)(0)`, so
`KuhnTucker B F = -(∂(inf F)(0))` as sets and every property of subdifferentials transfers through
`Set` negation, which is a preimage.

## What is not here

**Corollaries 29.1.2, 29.1.3, 29.1.5 and 29.1.6, and Theorems 29.2, 29.3, 29.4.** The
directional-derivative corollaries need §23's two-sided derivative and §25's differentiability
criteria; Theorem 29.2 needs the polyhedral calculus of §19 applied to bifunctions; Theorems 29.3
and 29.4 need §36's saddle-point correspondence on top of the Lagrangian
(`Optimization/Lagrangian.lean`). Compactness of the Kuhn–Tucker set under *strict* consistency
(Corollary 29.1.4) needs the boundedness half of Theorem 23.4, which
`Subgradient/Existence.lean` does not have.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §29 (Theorem 29.1).
-/

open Pointwise

namespace Tdaf.ConvexAnalysis

/-! ### Bifunctions and the perturbation function -/

section Defs

variable {U X : Type*}

/-- A **bifunction** from `U` to `X`: a family of `EReal`-valued functions on `X` indexed by a
perturbation parameter in `U`. Rockafellar writes `F u` for the member at `u`, and identifies the
generalized convex program `(P)` with `F` itself. -/
abbrev Bifun (U X : Type*) := U → X → EReal

/-- The **graph function** of a bifunction: the same data as a single function on `U × X`. Every
convexity statement about `F` is a statement about `graphFn F`. -/
def graphFn (F : Bifun U X) : U × X → EReal := fun p => F p.1 p.2

@[simp] theorem graphFn_apply (F : Bifun U X) (u : U) (x : X) : graphFn F (u, x) = F u x := rfl

/-- The **perturbation function** `inf F` of the program associated with `F`. Its value at `0` is
the optimal value of the program. -/
noncomputable def infBifun (F : Bifun U X) : U → EReal := fun u => ⨅ x, F u x

theorem infBifun_apply (F : Bifun U X) (u : U) : infBifun F u = ⨅ x, F u x := rfl

/-- The **effective domain** of a bifunction: the perturbations for which `F u` is not identically
`⊤`. -/
def domBifun (F : Bifun U X) : Set U := {u | ∃ x, F u x ≠ ⊤}

@[simp] theorem mem_domBifun {F : Bifun U X} {u : U} :
    u ∈ domBifun F ↔ ∃ x, F u x ≠ ⊤ := Iff.rfl

/-- **Rockafellar, Theorem 29.1**, first assertion (the domain half): the effective domain of the
perturbation function is the effective domain of the bifunction. -/
theorem dom_infBifun (F : Bifun U X) : dom (infBifun F) = domBifun F := by
  ext u
  constructor
  · intro h
    by_contra hcon
    have hall : ∀ x, F u x = ⊤ := fun x => by
      by_contra hx
      exact hcon ⟨x, hx⟩
    have htop : (⨅ x, F u x) = ⊤ := le_antisymm le_top (le_iInf fun x => (hall x).ge)
    rw [mem_dom, infBifun_apply, htop] at h
    exact absurd h (lt_irrefl ⊤)
  · rintro ⟨x, hx⟩
    exact mem_dom.2 (lt_of_le_of_lt (iInf_le _ x) (lt_top_iff_ne_top.2 hx))

end Defs

/-! ### Convexity -/

section Convex

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {F : Bifun U X}

/-- A bifunction is **convex** when its graph function is a convex function on `U × X`. -/
def ConvexBifun (F : Bifun U X) : Prop := ConvexFn (graphFn F)

theorem convexBifun_iff : ConvexBifun F ↔ ConvexFn (graphFn F) := Iff.rfl

/-- **Rockafellar, Theorem 29.1**, first assertion (the convexity half): the perturbation function
of a convex bifunction is convex. This is Theorem 5.7 at the projection `(u, x) ↦ u`. -/
theorem convexFn_infBifun (hF : ConvexBifun F) : ConvexFn (infBifun F) :=
  convexFn_iInf_right hF

/-- Each image `F u` of a convex bifunction is a convex function. The slice `x` of a jointly
convex function is convex because `a * u + b * u = u` when `a + b = 1`; there is no linear map to
compose with, so this is `epi_combo` applied by hand. -/
theorem ConvexBifun.convexFn_apply (hF : ConvexBifun F) (u : U) : ConvexFn (F u) := by
  refine convexFn_of_epi_combo fun x y mu nu hx hy a b ha hb hab => ?_
  have h := hF.epi_combo (x := (u, x)) (y := (u, y)) hx hy ha hb hab
  have hu : a • (u, x) + b • (u, y) = (u, a • x + b • y) := by
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul]
  rwa [hu] at h

end Convex

/-! ### Consistency -/

section Consistency

variable {U X : Type*} [AddCommGroup U] {F : Bifun U X}

/-- `(P)` is **consistent** when it has a feasible solution, i.e. when its optimal value is
`< ⊤`. -/
def Consistent (F : Bifun U X) : Prop := (0 : U) ∈ domBifun F

theorem consistent_iff : Consistent F ↔ ∃ x, F 0 x ≠ ⊤ := Iff.rfl

end Consistency

section ConsistencyTopology

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] {F : Bifun U X}

/-- `(P)` is **strongly consistent** when `0` is a *relative interior* point of `dom F`: the
qualification behind the existence of Kuhn–Tucker vectors. -/
def StronglyConsistent (F : Bifun U X) : Prop := (0 : U) ∈ ri (domBifun F)

/-- `(P)` is **strictly consistent** when `0` is an interior point of `dom F`. -/
def StrictlyConsistent (F : Bifun U X) : Prop := (0 : U) ∈ interior (domBifun F)

theorem StrictlyConsistent.stronglyConsistent (h : StrictlyConsistent F) :
    StronglyConsistent F :=
  interior_subset_intrinsicInterior h

theorem StronglyConsistent.consistent (h : StronglyConsistent F) : Consistent F :=
  intrinsicInterior_subset h

end ConsistencyTopology

/-! ### Theorem 29.1: Kuhn–Tucker vectors -/

section KuhnTucker

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X} {v : V}

/-- **Kuhn–Tucker vectors** for the program associated with `F`, in Rockafellar's own definition
(§29): the prices `v` at which `⨅ u (⟨u, v⟩ + inf F u)` is finite and equal to the optimal value
`inf F 0`, so that no perturbation is worth buying. -/
def KuhnTucker (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : Set V :=
  {v | infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
    (⨅ u, (((B u v : ℝ) : EReal) + infBifun F u)) = infBifun F 0}

/-- Evaluating at `u = 0` shows that the infimum in the definition of a Kuhn–Tucker vector is never
above the optimal value, whatever `v` is. -/
theorem iInf_add_infBifun_le (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) :
    (⨅ u, (((B u v : ℝ) : EReal) + infBifun F u)) ≤ infBifun F 0 := by
  refine le_trans (iInf_le _ 0) (le_of_eq ?_)
  rw [map_zero, LinearMap.zero_apply, _root_.EReal.coe_zero, zero_add]

/-- The reformulation Rockafellar states immediately after the definition: a Kuhn–Tucker vector is
a price at which every perturbation costs at least what it saves. -/
theorem mem_kuhnTucker_iff_forall_le :
    v ∈ KuhnTucker B F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      ∀ u, infBifun F 0 ≤ ((B u v : ℝ) : EReal) + infBifun F u := by
  constructor
  · rintro ⟨ht, hb, heq⟩
    refine ⟨ht, hb, fun u => ?_⟩
    rw [← heq]
    exact iInf_le _ u
  · rintro ⟨ht, hb, hall⟩
    exact ⟨ht, hb, le_antisymm (iInf_add_infBifun_le B F v) (le_iInf hall)⟩

/-- Moving a real constant across an `EReal` inequality; the `⊥` and `⊤` cases are the reason this
cannot be `linarith`. -/
private theorem coe_add_neg_le_iff {c p : ℝ} {w : EReal} :
    (c : EReal) + ((-p : ℝ) : EReal) ≤ w ↔ (c : EReal) ≤ (p : EReal) + w := by
  induction w with
  | bot => simp
  | coe q =>
      rw [← _root_.EReal.coe_add, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff,
        _root_.EReal.coe_le_coe_iff]
      constructor <;> intro h <;> linarith
  | top => simp

/-- **Rockafellar, Theorem 29.1**, second assertion: when the optimal value is finite, the
Kuhn–Tucker vectors are exactly the `v` with `-v ∈ ∂(inf F)(0)`.

The subgradient inequality for `inf F` at `0` in the direction `-v` says precisely that no
perturbation is worth buying at the price `v`. -/
theorem mem_kuhnTucker_iff_neg_mem_subgradient (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    v ∈ KuhnTucker B F ↔ -v ∈ subgradient B (infBifun F) 0 := by
  obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  have hiff : ∀ u : U, (infBifun F 0 ≤ ((B u v : ℝ) : EReal) + infBifun F u)
      ↔ (infBifun F 0 + ((B (u - 0) (-v) : ℝ) : EReal) ≤ infBifun F u) := by
    intro u
    rw [sub_zero, map_neg, hc]
    exact coe_add_neg_le_iff.symm
  rw [mem_kuhnTucker_iff_forall_le, mem_subgradient]
  exact ⟨fun h u => (hiff u).1 (h.2.2 u), fun h => ⟨ht, hb, fun u => (hiff u).2 (h u)⟩⟩

/-- **Rockafellar, Theorem 29.1**, as an equation between sets: the Kuhn–Tucker set is the
reflected subdifferential of the perturbation function at the origin. -/
theorem kuhnTucker_eq_neg_subgradient (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker B F = -(subgradient B (infBifun F) 0) := by
  ext v
  rw [Set.mem_neg]
  exact mem_kuhnTucker_iff_neg_mem_subgradient ht hb

/-- **Rockafellar, Corollary 29.1.1**, convexity half: the Kuhn–Tucker vectors form a convex
set. -/
theorem convex_kuhnTucker (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    Convex ℝ (KuhnTucker B F) := by
  rw [kuhnTucker_eq_neg_subgradient ht hb]
  exact (convex_subgradient B (infBifun F) 0).neg

end KuhnTucker

/-! ### Closedness and existence -/

section Topology

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- **Rockafellar, Corollary 29.1.1**, closedness half: the Kuhn–Tucker vectors form a closed
set. -/
theorem isClosed_kuhnTucker [IsContinuousPairing B.flip] (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : IsClosed (KuhnTucker B F) := by
  rw [kuhnTucker_eq_neg_subgradient ht hb]
  exact (isClosed_subgradient (B := B) (infBifun F) 0).neg

end Topology

section Existence

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup X] [Module ℝ X]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- **Rockafellar, Corollary 29.1.4**, existence half: a strongly consistent convex program whose
perturbation function is proper has a Kuhn–Tucker vector.

This is Theorem 23.4 (`subgradient_nonempty_of_mem_relint_dom`) applied to `inf F` at the origin,
which `dom_infBifun` places in `ri (dom F)`. -/
theorem kuhnTucker_nonempty_of_stronglyConsistent [IsCompatiblePairing B] (hF : ConvexBifun F)
    (hp : Proper (infBifun F)) (hs : StronglyConsistent F) (ht : infBifun F 0 ≠ ⊤) :
    (KuhnTucker B F).Nonempty := by
  have hri : (0 : U) ∈ ri (dom (infBifun F)) := by rwa [dom_infBifun]
  obtain ⟨y, hy⟩ :=
    subgradient_nonempty_of_mem_relint_dom (B := B) (convexFn_infBifun hF) hp hri
  refine ⟨-y, ?_⟩
  rw [mem_kuhnTucker_iff_neg_mem_subgradient ht (hp.ne_bot 0), neg_neg]
  exact hy

end Existence

end Tdaf.ConvexAnalysis
