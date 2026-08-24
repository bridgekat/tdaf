/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Optimization.Adjoint

/-!
# Saddle-functions and partial conjugacy

Rockafellar's §33. A **concave-convex** function on `U × X` is concave in its first argument for
each value of the second and convex in the second for each value of the first; convex-concave
functions are the mirror image, and both are called **saddle-functions**.

The section's point is a correspondence: a convex bifunction `F` from `U` to `X` gives rise to the
**bracket** `⟨Fu, y⟩ = (F u)*(y)`, which is a concave-convex function of `(u, y)`, closed convex in
`y`; and conversely every such function arises this way. The bracket is the *partial* conjugate of
the graph function of `F` — the conjugate taken in the second variable only — so the whole of §33 is
`Duality/Conjugate.lean` applied uniformly in a parameter.

## Main definitions

* `ConcaveConvexFn`, `ConvexConcaveFn`, `SaddleFn` — the three predicates of §33.
* `dom₁`, `dom₂` — the two effective domains of a saddle-function (§34).
* `partialConj₂ Bx f` — the conjugate of `f : U × X → EReal` in its second variable only.
* `partialCl₁`, `partialCl₂` — Rockafellar's `cl₁` and `cl₂`. `cl₂` closes convexly and `cl₁`
  closes *concavely*; the asymmetry is genuine.
* `bracket Bx F` — Rockafellar's `⟨Fu, y⟩`.
* `concaveBracket Bu G` — Rockafellar's `⟨u, G y⟩`, the bracket of a *concave* bifunction: the
  concave conjugate in the first variable where `bracket` is the convex conjugate in the second.
* `bifunOfSaddle Bx K` — the convex bifunction attached to a saddle-function, `F u = K(u, ·)*`.

## Main results

* `convexFn_bracket`, `closedFn_bracket`, `concaveFn_bracket` — **Theorem 33.1**, first half: the
  bracket of a convex bifunction is concave-convex and convex-closed. Convexity and closedness in
  `y` need no hypothesis on `F` at all; only concavity in `u` uses `ConvexBifun F`.
* `clFn_eq_conj_bracket` — **Theorem 33.1**'s inversion formula `cl (F u) = ⟨F u, ·⟩*`.
* `convexBifun_bifunOfSaddle`, `bracket_bifunOfSaddle` — **Theorem 33.1**, second half: the
  bifunction attached to a concave-convex `K` is convex, and its bracket is `cl₂ K`.
* `convexFn_partialCl₂`, `convexClosedFn_partialCl₂`, `concaveFn_partialCl₁`,
  `concaveClosedFn_partialCl₁` — **Corollary 33.1.1**.
* `convexFn_concaveBracket` — **Theorem 33.1** for a concave bifunction: `⟨u, G ·⟩` is convex.
* `adjointBifun_eq_concaveConj_bracket`, `concaveAdjointBifun_eq_conj_concaveBracket` — the bridge
  to §30, in both directions: each adjoint is one conjugation of the corresponding bracket.
* `concaveConj_adjointBifun_eq_partialCl₁`, `concaveBracket_adjointBifun_eq_partialCl₁` —
  **Theorem 33.2**, first equation: `⟨u, F* y⟩ = cl₁ ⟨Fu, y⟩`.
* `bracket_concaveAdjointBifun_eq_partialCl₂`, `partialCl₂_concaveBracket_adjointBifun` —
  **Theorem 33.2**, second equation: `cl₂ ⟨u, F* y⟩ = ⟨(cl F) u, y⟩`.

## Design notes

**`cl₁` is not `cl₂` with the arguments swapped.** For a concave-convex `K`, `cl₂ K` closes
`K(u, ·)` as a *convex* function and `cl₁ K` closes `K(·, y)` as a *concave* one. `partialCl₁` is
therefore built from `clConcave`, the concave closure that `Duality/ConcaveConj.lean` had promised
and now defines; every `clConcave` lemma is its `clFn` counterpart conjugated by negation, and each
is one line.

**The plan's `dom₁ K = {u | ∃ x, K (u, x) ≠ ⊥}` was wrong.** Rockafellar (§34) writes
`dom₁ K = {u | K(u, v) > -∞ for **all** v}` — an intersection of effective domains, not a union —
and says so explicitly ("`dom₁ K` is the intersection of the effective domains of the concave
functions `K(·, v)`"). With the existential reading, convexity of `dom₁ K` would be false; with the
universal one it is `convex_iInter`.

**The two equations of Theorem 33.2 are the same theorem twice, in opposite variables.** The
first is concave Fenchel–Moreau in `u`, applied to `⟨F·, y⟩`; the second is convex Fenchel–Moreau
in `y`, applied to `⟨u, F*·⟩`. Rockafellar gets the second by "applying the formula to `F*` in
place of `F`", and that is exactly how it is proved here: the general statement
`bracket_concaveAdjointBifun_eq_partialCl₂` is about an arbitrary concave bifunction `G`, and
Theorem 33.2 is that statement at `G := F*` composed with Theorem 30.1. The hypotheses do not
match between the two halves — the first needs a compatible `Bu` and a topology on `U`, the second
a compatible `Bx.flip` and a topology on `Y` — which is invisible in `Rⁿ`.

**The bracket is `conj`, not a new operator.** `bracket Bx F u = conj Bx (F u)`, so `ConvexFn`,
`ClosedFn`, the Fenchel inequality and Fenchel–Moreau all apply pointwise in `u` with no work. The
only clause of Theorem 33.1 that is not an instant application is concavity in `u`, which is
Theorem 5.7 (`convexFn_iInf_right`) after `-⨆ = ⨅ -`.

## What is not here

**Corollaries 33.1.2, 33.1.3, 33.2.1, 33.2.2 and Theorem 33.3.** Corollary 33.1.2 is the
bijection between convex-closed concave-convex functions and image-closed convex bifunctions; both
halves of it are proved here as separate statements, but packaging them as an `Equiv` needs an
`ImageClosed` predicate and a subtype, which belongs with §34's equivalence classes.
Corollary 33.1.3 is the polyhedral case and needs `PolyhedralFn` transported to bifunctions.
Corollaries 33.2.1 and 33.2.2 say that the two brackets agree off a small set — on
`ri (dom F)`, and everywhere but one exceptional pair in the polyhedral case — which is §7's
"a closed concave function agrees with its closure on the relative interior of its effective
domain" applied to `⟨F·, y⟩`. Theorem 33.3 and all of §34 (`cl₁ cl₂` idempotence, equivalence
classes, kernels) are the next file.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §33 (Theorem 33.1,
  Corollary 33.1.1, Theorem 33.2) and §34 (the effective domains).
-/

namespace Tdaf.ConvexAnalysis

/-! ### Three rearrangements over `EReal` -/

section ERealAux

/-- Negating a difference whose minuend is real. -/
private theorem neg_coe_sub' {c : ℝ} {w : EReal} :
    -((c : EReal) - w) = ((-c : ℝ) : EReal) + w := by
  induction w with
  | bot => rw [_root_.EReal.coe_sub_bot, _root_.EReal.neg_top, _root_.EReal.add_bot]
  | coe r =>
    rw [← _root_.EReal.coe_sub, ← _root_.EReal.coe_neg, ← _root_.EReal.coe_add,
      _root_.EReal.coe_eq_coe_iff]
    ring
  | top => rw [_root_.EReal.sub_top, _root_.EReal.neg_bot, _root_.EReal.coe_add_top]

/-- A difference with a real minuend, read as a sum. -/
private theorem coe_sub_eq_neg_add {c : ℝ} {w : EReal} :
    (c : EReal) - w = -w + (c : EReal) := by
  change (c : EReal) + -w = -w + (c : EReal)
  exact add_comm _ _

end ERealAux

/-! ### The two effective domains -/

section SaddleDom

variable {U X : Type*} {K : U × X → EReal}

/-- The **first effective domain**: the `u` at which `K (u, ·)` is nowhere `-∞`. Rockafellar's
`dom₁ K`, an *intersection* of concave effective domains. -/
def dom₁ (K : U × X → EReal) : Set U := {u | ∀ x, ⊥ < K (u, x)}

/-- The **second effective domain**: the `x` at which `K (·, x)` is nowhere `+∞`. -/
def dom₂ (K : U × X → EReal) : Set X := {x | ∀ u, K (u, x) < ⊤}

@[simp] theorem mem_dom₁ {u : U} : u ∈ dom₁ K ↔ ∀ x, ⊥ < K (u, x) := Iff.rfl

@[simp] theorem mem_dom₂ {x : X} : x ∈ dom₂ K ↔ ∀ u, K (u, x) < ⊤ := Iff.rfl

theorem dom₁_eq_iInter (K : U × X → EReal) :
    dom₁ K = ⋂ x, domConcave fun u => K (u, x) := by
  ext u
  simp [dom₁, domConcave]

theorem dom₂_eq_iInter (K : U × X → EReal) : dom₂ K = ⋂ u, dom fun x => K (u, x) := by
  ext x
  simp [dom₂, dom]

end SaddleDom

/-! ### Concave-convex functions -/

section SaddleDefs

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {K : U × X → EReal}

/-- `K` is **concave-convex**: concave in the first argument, convex in the second. -/
structure ConcaveConvexFn (K : U × X → EReal) : Prop where
  /-- `K (·, x)` is concave for every `x`. -/
  concave_fst : ∀ x, ConcaveFn fun u => K (u, x)
  /-- `K (u, ·)` is convex for every `u`. -/
  convex_snd : ∀ u, ConvexFn fun x => K (u, x)

/-- `K` is **convex-concave**: convex in the first argument, concave in the second. -/
structure ConvexConcaveFn (K : U × X → EReal) : Prop where
  /-- `K (·, x)` is convex for every `x`. -/
  convex_fst : ∀ x, ConvexFn fun u => K (u, x)
  /-- `K (u, ·)` is concave for every `u`. -/
  concave_snd : ∀ u, ConcaveFn fun x => K (u, x)

/-- A **saddle-function** is one of the two. -/
def SaddleFn (K : U × X → EReal) : Prop := ConcaveConvexFn K ∨ ConvexConcaveFn K

theorem ConcaveConvexFn.convexConcaveFn_neg (h : ConcaveConvexFn K) :
    ConvexConcaveFn fun p => -(K p) :=
  ⟨fun x => (h.concave_fst x).convexFn_neg, fun u => (h.convex_snd u).concaveFn_neg⟩

theorem ConvexConcaveFn.concaveConvexFn_neg (h : ConvexConcaveFn K) :
    ConcaveConvexFn fun p => -(K p) :=
  ⟨fun x => (h.convex_fst x).concaveFn_neg, fun u => (h.concave_snd u).convexFn_neg⟩

theorem ConcaveConvexFn.saddleFn (h : ConcaveConvexFn K) : SaddleFn K := Or.inl h

theorem ConvexConcaveFn.saddleFn (h : ConvexConcaveFn K) : SaddleFn K := Or.inr h

/-- `dom₁` of a concave-convex function is convex: it is an intersection of concave domains. -/
theorem ConcaveConvexFn.convex_dom₁ (h : ConcaveConvexFn K) : Convex ℝ (dom₁ K) := by
  rw [dom₁_eq_iInter]
  exact convex_iInter fun x => (h.concave_fst x).convex_domConcave

/-- `dom₂` of a concave-convex function is convex. -/
theorem ConcaveConvexFn.convex_dom₂ (h : ConcaveConvexFn K) : Convex ℝ (dom₂ K) := by
  rw [dom₂_eq_iInter]
  exact convex_iInter fun u => (h.convex_snd u).convex_dom

end SaddleDefs

/-! ### Partial conjugacy -/

section PartialConj

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The conjugate of `f` **in the second variable only**. -/
noncomputable def partialConj₂ (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (f : U × X → EReal) : U × Y → EReal :=
  fun p => conj Bx (fun x => f (p.1, x)) p.2

theorem partialConj₂_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (f : U × X → EReal) (p : U × Y) :
    partialConj₂ Bx f p = conj Bx (fun x => f (p.1, x)) p.2 := rfl

end PartialConj

/-! ### Partial closures -/

section PartialCl

variable {U X : Type*}

/-- Rockafellar's `cl₂`: close in the second variable, **convexly**. -/
noncomputable def partialCl₂ [TopologicalSpace X] (K : U × X → EReal) : U × X → EReal :=
  fun p => clFn (fun x => K (p.1, x)) p.2

/-- Rockafellar's `cl₁`: close in the first variable, **concavely**. -/
noncomputable def partialCl₁ [TopologicalSpace U] (K : U × X → EReal) : U × X → EReal :=
  fun p => clConcave (fun u => K (u, p.2)) p.1

theorem partialCl₂_apply [TopologicalSpace X] (K : U × X → EReal) (p : U × X) :
    partialCl₂ K p = clFn (fun x => K (p.1, x)) p.2 := rfl

theorem partialCl₁_apply [TopologicalSpace U] (K : U × X → EReal) (p : U × X) :
    partialCl₁ K p = clConcave (fun u => K (u, p.2)) p.1 := rfl

/-- The second-variable slice of `cl₂ K` is the closure of the slice of `K`. -/
theorem partialCl₂_slice [TopologicalSpace X] (K : U × X → EReal) (u : U) :
    (fun x => partialCl₂ K (u, x)) = clFn fun x => K (u, x) := rfl

/-- The first-variable slice of `cl₁ K` is the concave closure of the slice of `K`. -/
theorem partialCl₁_slice [TopologicalSpace U] (K : U × X → EReal) (x : X) :
    (fun u => partialCl₁ K (u, x)) = clConcave fun u => K (u, x) := rfl

/-- `cl₂ K ≤ K`: the convex closure only lowers. -/
theorem partialCl₂_le [TopologicalSpace X] (K : U × X → EReal) : partialCl₂ K ≤ K :=
  fun p => clFn_le (fun x => K (p.1, x)) p.2

theorem partialCl₂_mono [TopologicalSpace X] {K L : U × X → EReal} (h : K ≤ L) :
    partialCl₂ K ≤ partialCl₂ L :=
  fun p => clFn_mono (fun x => h (p.1, x)) p.2

/-- `K ≤ cl₁ K`: the concave closure only raises. -/
theorem le_partialCl₁ [TopologicalSpace U] (K : U × X → EReal) : K ≤ partialCl₁ K :=
  fun p => le_clConcave (fun u => K (u, p.2)) p.1

theorem partialCl₁_mono [TopologicalSpace U] {K L : U × X → EReal} (h : K ≤ L) :
    partialCl₁ K ≤ partialCl₁ L :=
  fun p => clConcave_mono (fun u => h (u, p.2)) p.1

/-- `K` is **convex-closed** when it is unchanged by `cl₂`. -/
def ConvexClosedFn [TopologicalSpace X] (K : U × X → EReal) : Prop := partialCl₂ K = K

/-- `K` is **concave-closed** when it is unchanged by `cl₁`. -/
def ConcaveClosedFn [TopologicalSpace U] (K : U × X → EReal) : Prop := partialCl₁ K = K

theorem convexClosedFn_iff [TopologicalSpace X] {K : U × X → EReal} :
    ConvexClosedFn K ↔ ∀ u, ClosedFn fun x => K (u, x) := by
  constructor
  · intro h u
    funext x
    exact congrFun h (u, x)
  · intro h
    funext p
    exact congrFun (h p.1) p.2

theorem concaveClosedFn_iff [TopologicalSpace U] {K : U × X → EReal} :
    ConcaveClosedFn K ↔ ∀ x, ClosedConcaveFn fun u => K (u, x) := by
  constructor
  · intro h x
    funext u
    exact congrFun h (u, x)
  · intro h
    funext p
    exact congrFun (h p.2) p.1

end PartialCl

/-! ### Theorem 33.1: the bracket of a convex bifunction -/

section Bracket

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- Rockafellar's **bracket** `⟨Fu, y⟩ = (F u)*(y)`, read as a function of `(u, y)`. -/
noncomputable def bracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) : U → Y → EReal :=
  fun u y => conj Bx (F u) y

theorem bracket_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (u : U) (y : Y) :
    bracket Bx F u y = ⨆ x, ((Bx x y : ℝ) : EReal) - F u x := rfl

theorem bracket_eq_conj (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (u : U) :
    bracket Bx F u = conj Bx (F u) := rfl

/-- The bracket **is** the partial conjugate of the graph function. -/
theorem partialConj₂_graphFn (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (p : U × Y) :
    partialConj₂ Bx (graphFn F) p = bracket Bx F p.1 p.2 := rfl

/-- **Rockafellar, Theorem 33.1**: `⟨Fu, ·⟩` is convex, with no hypothesis on `F`. -/
theorem convexFn_bracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (u : U) :
    ConvexFn (bracket Bx F u) :=
  convexFn_conj Bx (F u)

end Bracket

section BracketClosed

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing Bx.flip] {F : Bifun U X}

/-- **Rockafellar, Theorem 33.1**: `⟨Fu, ·⟩` is closed as well as convex. -/
theorem closedFn_bracket (u : U) : ClosedFn (bracket Bx F u) := closedFn_conj

end BracketClosed

/-! ### Theorem 33.1: the clauses that use convexity of the bifunction -/

section BracketConvex

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] {F : Bifun U X}

/-- **Rockafellar, Theorem 33.1**, the clause with content: `⟨F·, y⟩` is *concave* in `u` whenever
`F` is a convex bifunction. This is Theorem 5.7 applied to the projection `(u, x) ↦ u`. -/
theorem concaveFn_bracket (hF : ConvexBifun F) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (y : Y) :
    ConcaveFn fun u => bracket Bx F u y := by
  rw [concaveFn_iff_convexFn_neg]
  have hconv : ConvexFn (fun p : U × X => graphFn F p + ((-(Bx p.2 y) : ℝ) : EReal)) := by
    refine convexFn_add_coe hF ?_
    intro p q a b hab
    simp only [Prod.smul_snd, Prod.snd_add, map_add, map_smul, smul_eq_mul, LinearMap.add_apply,
      LinearMap.smul_apply]
    ring
  have hrw : (fun u => -(bracket Bx F u y))
      = fun u => ⨅ x, (graphFn F (u, x) + ((-(Bx x y) : ℝ) : EReal)) := by
    funext u
    rw [bracket_apply, Tdaf.EReal.neg_iSup]
    refine iInf_congr fun x => ?_
    rw [neg_coe_sub']
    exact add_comm _ _
  rw [hrw]
  exact convexFn_iInf_right hconv

/-- The bracket of a convex bifunction is concave-convex. -/
theorem concaveConvexFn_bracket (hF : ConvexBifun F) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    ConcaveConvexFn fun p : U × Y => bracket Bx F p.1 p.2 :=
  ⟨fun y => concaveFn_bracket hF Bx y, fun u => convexFn_bracket Bx F u⟩

end BracketConvex

section BracketInversion

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F : Bifun U X}

/-- **Rockafellar, Theorem 33.1**, the inversion formula: `cl (F u)` is recovered from the bracket
by conjugating back. This is Fenchel–Moreau, uniformly in `u`. -/
theorem clFn_eq_conj_bracket (hF : ConvexBifun F) (u : U) :
    clFn (F u) = conj Bx.flip (bracket Bx F u) :=
  (biconj_eq_clFn (B := Bx) (hF.convexFn_apply u)).symm

end BracketInversion

/-! ### Theorem 33.1, converse direction -/

section OfSaddleDefs

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The convex bifunction attached to a saddle-function: `F u = K (u, ·)*`, the conjugate taken
over the flipped pairing. -/
noncomputable def bifunOfSaddle (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) : Bifun U X :=
  fun u x => conj Bx.flip (fun y => K (u, y)) x

theorem bifunOfSaddle_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) (u : U) (x : X) :
    bifunOfSaddle Bx K u x = ⨆ y, ((Bx x y : ℝ) : EReal) - K (u, y) := rfl

end OfSaddleDefs

section OfSaddle

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] {K : U × Y → EReal}

/-- **Rockafellar, Theorem 33.1**, converse: the bifunction attached to a concave-convex `K` is
convex. Its graph function is a pointwise supremum of jointly convex functions. -/
theorem convexBifun_bifunOfSaddle (hK : ConcaveConvexFn K) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    ConvexBifun (bifunOfSaddle Bx K) := by
  have hconv : ∀ y : Y,
      ConvexFn (fun p : U × X => -(K (p.1, y)) + ((Bx p.2 y : ℝ) : EReal)) := by
    intro y
    refine convexFn_add_coe (f := fun p : U × X => -(K (p.1, y))) ?_ ?_
    · exact convexFn_compLin (LinearMap.fst ℝ U X) ((hK.concave_fst y).convexFn_neg)
    · intro p q a b hab
      simp only [Prod.smul_snd, Prod.snd_add, map_add, map_smul, smul_eq_mul, LinearMap.add_apply,
        LinearMap.smul_apply]
  have hsup : ConvexFn (fun p : U × X => ⨆ y : Y, (-(K (p.1, y)) + ((Bx p.2 y : ℝ) : EReal))) :=
    convexFn_iSup
      (f := fun (y : Y) (p : U × X) => -(K (p.1, y)) + ((Bx p.2 y : ℝ) : EReal)) hconv
  have hrw : graphFn (bifunOfSaddle Bx K)
      = fun p : U × X => ⨆ y : Y, (-(K (p.1, y)) + ((Bx p.2 y : ℝ) : EReal)) := by
    funext p
    rw [graphFn_apply, bifunOfSaddle_apply]
    exact iSup_congr fun y => coe_sub_eq_neg_add
  rw [convexBifun_iff, hrw]
  exact hsup

end OfSaddle

section OfSaddleBracket

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx.flip] {K : U × Y → EReal}

/-- **Rockafellar, Theorem 33.1**, converse: the bracket of that bifunction is `cl₂ K`. -/
theorem bracket_bifunOfSaddle (hK : ConcaveConvexFn K) (p : U × Y) :
    bracket Bx (bifunOfSaddle Bx K) p.1 p.2 = partialCl₂ K p :=
  congrFun (biconj_eq_clFn (B := Bx.flip) (hK.convex_snd p.1)) p.2

end OfSaddleBracket

/-! ### Corollary 33.1.1 -/

section CorClosed

variable {U X : Type*}

/-- **Rockafellar, Corollary 33.1.1** for `cl₂`: the result is convex-closed. -/
theorem convexClosedFn_partialCl₂ [TopologicalSpace X] [AddCommGroup X]
    [IsTopologicalAddGroup X] (K : U × X → EReal) : ConvexClosedFn (partialCl₂ K) :=
  convexClosedFn_iff.2 fun u => closedFn_clFn fun x => K (u, x)

/-- **Rockafellar, Corollary 33.1.1** for `cl₁`: the result is concave-closed. -/
theorem concaveClosedFn_partialCl₁ [TopologicalSpace U] [AddCommGroup U]
    [IsTopologicalAddGroup U] (K : U × X → EReal) : ConcaveClosedFn (partialCl₁ K) :=
  concaveClosedFn_iff.2 fun x => closedConcaveFn_clConcave fun u => K (u, x)

end CorClosed

section Cor

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {K : U × X → EReal}

/-- **Rockafellar, Corollary 33.1.1** for `cl₂`: closing convexly in the second variable preserves
convexity there. -/
theorem convexFn_partialCl₂ [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (hK : ConcaveConvexFn K) (u : U) : ConvexFn fun x => partialCl₂ K (u, x) := by
  rw [partialCl₂_slice]
  exact convexFn_clFn (hK.convex_snd u)

/-- **Rockafellar, Corollary 33.1.1** for `cl₁`: closing concavely in the first variable preserves
concavity there. -/
theorem concaveFn_partialCl₁ [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
    (hK : ConcaveConvexFn K) (x : X) : ConcaveFn fun u => partialCl₁ K (u, x) := by
  rw [partialCl₁_slice]
  exact concaveFn_clConcave (hK.concave_fst x)

end Cor

/-! ### The bridge to §30 -/

/-! ### The concave bracket -/

section ConcaveBracket

variable {U V Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- Rockafellar's bracket for a *concave* bifunction, read as a function of `(u, y)`. Where
`bracket` conjugates convexly in the second variable, this one conjugates concavely in the
first. -/
noncomputable def concaveBracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Bifun Y V) : U → Y → EReal :=
  fun u y => concaveConj Bu.flip (G y) u

theorem concaveBracket_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Bifun Y V) (u : U) (y : Y) :
    concaveBracket Bu G u y = ⨅ v, ((Bu u v : ℝ) : EReal) - G y v := rfl

theorem concaveBracket_eq_concaveConj (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Bifun Y V) (y : Y) :
    (fun u => concaveBracket Bu G u y) = concaveConj Bu.flip (G y) := rfl

end ConcaveBracket

section ConcaveBracketAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **The concave adjoint is the conjugate of the concave bracket** — the mirror of
`adjointBifun_eq_concaveConj_bracket`, with the two conjugations in the opposite order. -/
theorem concaveAdjointBifun_eq_conj_concaveBracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (G : Bifun Y V) (u : U) (x : X) :
    concaveAdjointBifun Bu Bx G u x = conj Bx.flip (fun y => concaveBracket Bu G u y) x := by
  rw [concaveAdjointBifun_apply, conj_apply, iSup_prod]
  refine iSup_congr fun y => ?_
  have hflip : (Bx.flip y x : ℝ) = Bx x y := rfl
  rw [hflip, concaveBracket_apply, coe_sub_eq_neg_add, Tdaf.EReal.neg_iInf,
    Tdaf.EReal.iSup_add_coe]
  refine iSup_congr fun v => ?_
  rw [neg_coe_sub', add_comm (((-(Bu u v) : ℝ) : EReal)) (G y v), add_assoc,
    ← _root_.EReal.coe_add]
  congr 2
  ring

end ConcaveBracketAdjoint

section ConcaveBracketConvex

variable {U V Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup Y] [Module ℝ Y] {G : Bifun Y V}

omit [AddCommGroup Y] [Module ℝ Y] in
/-- **Rockafellar, Theorem 33.1** for a concave bifunction: the concave bracket is *concave* in
the first variable — it is a concave conjugate. -/
theorem concaveFn_concaveBracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Bifun Y V) (y : Y) :
    ConcaveFn fun u => concaveBracket Bu G u y :=
  concaveFn_concaveConj Bu.flip (G y)

/-- **Rockafellar, Theorem 33.1** for a concave bifunction: `⟨u, G ·⟩` is *convex* in the second
variable. This is the mirror of `concaveFn_bracket`, and again Theorem 5.7 at a
projection. -/
theorem convexFn_concaveBracket (hG : ConcaveBifun G) (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u : U) :
    ConvexFn fun y => concaveBracket Bu G u y := by
  have hconv : ConvexFn (fun q : Y × V => -(graphFn G q) + ((Bu u q.2 : ℝ) : EReal)) := by
    refine convexFn_add_coe (concaveBifun_iff.1 hG).convexFn_neg ?_
    intro q r a b hab
    simp only [Prod.smul_snd, Prod.snd_add, map_add, map_smul, smul_eq_mul]
  have hrw : (fun y => concaveBracket Bu G u y)
      = fun y => ⨅ v, (-(graphFn G (y, v)) + ((Bu u v : ℝ) : EReal)) := by
    funext y
    rw [concaveBracket_apply]
    exact iInf_congr fun v => coe_sub_eq_neg_add
  rw [hrw]
  exact convexFn_iInf_right hconv

/-- The concave bracket of a concave bifunction is concave-convex. -/
theorem concaveConvexFn_concaveBracket (hG : ConcaveBifun G) (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ConcaveConvexFn fun p : U × Y => concaveBracket Bu G p.1 p.2 :=
  ⟨fun y => concaveFn_concaveBracket Bu G y, fun u => convexFn_concaveBracket hG Bu u⟩

end ConcaveBracketConvex

section Adjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **The adjoint is the concave conjugate of the bracket.** Rockafellar's `⟨Fu, y⟩` and `F*` are
the two halves of one conjugation of the graph function: first convexly in `x`, then concavely in
`u`. This is the identity that turns Theorem 33.2 into `⟨u, F* y⟩ = cl₁ ⟨Fu, y⟩`. -/
theorem adjointBifun_eq_concaveConj_bracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) (v : V) :
    adjointBifun Bu Bx F y v = concaveConj Bu (fun u => bracket Bx F u y) v := by
  rw [adjointBifun_apply, concaveConj_apply, iInf_prod]
  refine iInf_congr fun u => ?_
  have hneg : ((Bu u v : ℝ) : EReal) - bracket Bx F u y
      = ⨅ x, ((((-(Bx x y) : ℝ) : EReal) + F u x) + ((Bu u v : ℝ) : EReal)) := by
    rw [bracket_apply, coe_sub_eq_neg_add, Tdaf.EReal.neg_iSup, Tdaf.EReal.iInf_add_coe]
    exact iInf_congr fun x => by rw [neg_coe_sub']
  rw [hneg]
  refine iInf_congr fun x => ?_
  rw [add_comm (((-(Bx x y) : ℝ) : EReal)) (F u x), add_assoc, ← _root_.EReal.coe_add]
  congr 2
  ring

end Adjoint

/-! ### Theorem 33.2 -/

section Thm332

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- **Rockafellar, Theorem 33.2**, first equation: `⟨u, F* y⟩ = cl₁ ⟨Fu, y⟩`.

The bracket of the *concave* bifunction `F*` — the concave conjugate of `F* y` — is the concave
closure, in `u`, of the bracket of `F`. Once `adjointBifun_eq_concaveConj_bracket` has identified
`F* y` as `concaveConj Bu (⟨F·, y⟩)`, this is concave Fenchel–Moreau
(`biconcaveConj_eq_clConcave`) applied to the concave function supplied by Theorem 33.1. -/
theorem concaveConj_adjointBifun_eq_partialCl₁ (hF : ConvexBifun F) (y : Y) :
    concaveConj Bu.flip (fun v => adjointBifun Bu Bx F y v)
      = fun u => partialCl₁ (fun p : U × Y => bracket Bx F p.1 p.2) (u, y) := by
  have hbr : (fun v => adjointBifun Bu Bx F y v)
      = concaveConj Bu (fun u => bracket Bx F u y) :=
    funext fun v => adjointBifun_eq_concaveConj_bracket Bu Bx F y v
  rw [hbr]
  exact biconcaveConj_eq_clConcave (concaveFn_bracket hF Bx y)

/-- **Rockafellar, Theorem 33.2**, first equation, in bracket notation. -/
theorem concaveBracket_adjointBifun_eq_partialCl₁ (hF : ConvexBifun F) (y : Y) :
    (fun u => concaveBracket Bu (adjointBifun Bu Bx F) u y)
      = fun u => partialCl₁ (fun p : U × Y => bracket Bx F p.1 p.2) (u, y) :=
  concaveConj_adjointBifun_eq_partialCl₁ hF y

end Thm332

section Thm332Concave

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx.flip]
  {G : Bifun Y V}

/-- **Rockafellar, Theorem 33.2**, second equation, in the form in which it is proved: for a
concave bifunction `G`, the bracket of the adjoint `G*` is the closure, in the second variable, of
the concave bracket of `G`. This is Fenchel–Moreau on `Y`, uniformly in `u`. -/
theorem bracket_concaveAdjointBifun_eq_partialCl₂ (hG : ConcaveBifun G) (u : U) :
    bracket Bx (concaveAdjointBifun Bu Bx G) u
      = fun y => partialCl₂ (fun p : U × Y => concaveBracket Bu G p.1 p.2) (u, y) := by
  have hconj : concaveAdjointBifun Bu Bx G u
      = conj Bx.flip (fun y => concaveBracket Bu G u y) :=
    funext fun x => concaveAdjointBifun_eq_conj_concaveBracket Bu Bx G u x
  rw [bracket_eq_conj, hconj, partialCl₂_slice]
  exact biconj_eq_clFn (B := Bx.flip) (convexFn_concaveBracket hG Bu u)

end Thm332Concave

section Thm332Full

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- **Rockafellar, Theorem 33.2**, second equation: `cl₂ ⟨u, F* y⟩ = ⟨(cl F) u, y⟩`. The adjoint of
`F` is concave with no hypothesis on `F`, so this is the concave form of the equation applied to
`F*`, followed by Theorem 30.1's `F** = cl F`. -/
theorem partialCl₂_concaveBracket_adjointBifun (hF : ConvexBifun F) (u : U) :
    (fun y => partialCl₂
        (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2) (u, y))
      = bracket Bx (clBifun F) u := by
  rw [← concaveAdjointBifun_adjointBifun_eq_clBifun (Bu := Bu) (Bx := Bx) hF]
  exact (bracket_concaveAdjointBifun_eq_partialCl₂ (concaveBifun_adjointBifun Bu Bx F) u).symm

end Thm332Full

/-! ### Corollary 33.1.1, the clauses that need the correspondence -/

section CorFull

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] {K : U × Y → EReal}

omit [AddCommGroup V] [Module ℝ V] in
/-- **Rockafellar, Corollary 33.1.1**, the clause that is not pointwise: `cl₂ K` is again
concave-convex, and in particular concave in the *first* variable. It is a bracket, and brackets
are concave-convex (Theorem 33.1). -/
theorem concaveConvexFn_partialCl₂ (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx.flip]
    (hK : ConcaveConvexFn K) : ConcaveConvexFn (partialCl₂ K) := by
  have h : (fun p : U × Y => bracket Bx (bifunOfSaddle Bx K) p.1 p.2) = partialCl₂ K :=
    funext fun p => bracket_bifunOfSaddle hK p
  rw [← h]
  exact concaveConvexFn_bracket (convexBifun_bifunOfSaddle hK Bx) Bx

end CorFull

end Tdaf.ConvexAnalysis
