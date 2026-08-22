/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Concave
import Tdaf.Analysis.Convex.Duality.Conjugate
import Tdaf.Analysis.Convex.Operations.Image

/-!
# Conjugates of concave functions

Rockafellar mirrors the whole of §12 for concave functions: `g*(y) = inf_x {⟨x, y⟩ - g(x)}`, with
`inf`, `≥` and `-∞` everywhere in place of `sup`, `≤` and `+∞`. Parts VI–VIII mix the two theories
constantly — §30's dual objective is the *concave* conjugate of `-inf F`, and §31's Fenchel duality
theorem pairs a convex `f` against a concave `g` — so the concave conjugate needs a name of its own
rather than being spelled through `-g` at every use.

**The sign trap.** `g* ≠ -(-g)*`. What is true is `g*(y) = -(-g)*(-y)`: there is a reflection on
the *dual* side as well. Rockafellar flags this explicitly, and it is the single most likely error
in Parts VI–VIII. `neg_concaveConj` is the dictionary, and every result below is derived
through it.

## Main definitions

* `concaveConj B g` — the **concave conjugate** `g*(y) = inf_x {⟨x, y⟩ - g x}`.
* `biconcaveConj B g` — the concave biconjugate `g**`, back on `E`.

## Main results

* `neg_concaveConj`, `concaveConj_eq_neg_conj_neg`, `conj_eq_neg_concaveConj_neg` — the sign
  dictionary, in both directions. These carry no side condition: negation, unlike addition, is an
  order-reversing involution of `EReal` with no exceptional values.
* `concaveConj_le_sub`, `add_concaveConj_le` — **Fenchel's inequality**, in both its `∞ - ∞`-free
  form and its named form `g x + g*(y) ≤ ⟨x, y⟩`. Both are unconditional, unlike the convex
  `le_add_conj`; see the design note below.
* `coe_le_concaveConj_iff`, `le_concaveConj_iff` — `c ≤ g*(y)` says exactly that the affine
  function `x ↦ ⟨x, y⟩ - c` lies *above* `g`; and `concaveConj B` is adjoint to
  `concaveConj B.flip`, the mirror of `conj_le_iff`.
* `concaveFn_concaveConj` — the concave conjugate of an arbitrary function is concave.
* `biconcaveConj_eq_neg_biconj_neg` — the double reflection cancels: `g** = -(-g)**`, with **no**
  sign on the argument. This is pure algebra and holds in any paired spaces.
* `biconcaveConj_eq_neg_clFn_neg` — **Fenchel–Moreau for concave functions**: `g**` is the
  *concave closure* of `g`, in the form `-(cl (-g))`.

## Design notes

**Everything is derived through the dictionary.** Concavity is defined geometrically in
`Concave.lean` and `-g` appears only in transfer lemmas; the same discipline is followed here.
The transfers are one or two lines each and are written by hand: `NOTES.md` gotcha 9 records that a
`simp` set normalising through `EReal` negation loops.

**The mirror is not perfectly symmetric, and `add_concaveConj_le` is where it shows.** Rockafellar's
convex Fenchel inequality `⟨x, y⟩ ≤ f x + f* y` needs `Proper f`, because at improper `f` the
right-hand side collapses to `⊤ + ⊥ = ⊥`. Its concave mirror `g x + g* y ≤ ⟨x, y⟩` puts the same
collapsing sum on the *small* side, where `⊥` is harmless, so it holds for every `g`. Sign transfer
on `EReal` reverses the order but not the arithmetic, and `⊤ + ⊥ = ⊥` is not self-dual.

**The concave closure is not yet a definition.** Rockafellar's `cl g` for concave `g` is the upper
semicontinuous hull, which is `-(cl (-g))`; the concave mirror of `Closure.lean` is not needed
until §34, so `biconcaveConj_eq_neg_clFn_neg` is stated through `clFn (-g)`. When `clConcave`
arrives it should be *defined* as `-(cl (-g))` and this theorem restated against it.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §12 and the concave
  conventions of §30; §31 (Fenchel's duality theorem).
-/

namespace Tdaf.ConvexAnalysis

/-! ### The concave conjugate -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **concave conjugate** of `g` with respect to the pairing `B`:
`g*(y) = inf_x (⟨x, y⟩ - g x)`.

Note that this is *not* `-(conj B (-g))`: Rockafellar's warning that `g* ≠ -(-g)*` is exactly the
point, and the correct dictionary `g*(y) = -(-g)*(-y)` is `concaveConj_eq_neg_conj_neg`. -/
noncomputable def concaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) : F → EReal :=
  fun y => ⨅ x : E, ((B x y : ℝ) : EReal) - g x

/-- The concave **biconjugate**, back on `E`. -/
noncomputable abbrev biconcaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) : E → EReal :=
  concaveConj B.flip (concaveConj B g)

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {g : E → EReal} {x : E} {y : F} {c : ℝ}

theorem concaveConj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (y : F) :
    concaveConj B g y = ⨅ x : E, ((B x y : ℝ) : EReal) - g x := rfl

theorem biconcaveConj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) :
    biconcaveConj B g x = ⨅ y : F, ((B x y : ℝ) : EReal) - concaveConj B g y := rfl

/-- **Fenchel's inequality for concave functions, `∞ - ∞`-free.** This is the defining property of
the infimum, and it holds for every `g`, `x` and `y`. -/
theorem concaveConj_le_sub (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) (y : F) :
    concaveConj B g y ≤ ((B x y : ℝ) : EReal) - g x :=
  iInf_le _ x

/-! ### The sign dictionary -/

/-- **The dictionary between the two conjugates**, and the guard against Rockafellar's sign trap:
`-g*(y) = (-g)*(-y)`. Both the values and the arguments are reflected; only one of the two
reflections is visible in the informal statement `g*(y) = -(-g)*(-y)`. -/
theorem neg_concaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (y : F) :
    -(concaveConj B g y) = conj B (fun x => -(g x)) (-y) := by
  rw [concaveConj_apply, Tdaf.EReal.neg_iInf, conj_apply]
  refine iSup_congr fun x => ?_
  have hB : ((B x (-y) : ℝ) : EReal) = -((B x y : ℝ) : EReal) := by
    rw [map_neg, _root_.EReal.coe_neg]
  rw [hB]
  simp only [sub_eq_add_neg]
  rw [_root_.EReal.neg_add (.inl (_root_.EReal.coe_ne_bot _)) (.inl (_root_.EReal.coe_ne_top _))]
  rfl

/-- The dictionary, solved for the concave conjugate: `g*(y) = -(-g)*(-y)`. -/
theorem concaveConj_eq_neg_conj_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (y : F) :
    concaveConj B g y = -(conj B (fun x => -(g x)) (-y)) := by
  rw [← neg_concaveConj, neg_neg]

/-- The dictionary in the other direction: `f*(y) = -(-f)*(-y)`, where the starred operation on the
right is the *concave* conjugate. The two statements are mirror images, exactly as Rockafellar's
`§30` summary promises. -/
theorem conj_eq_neg_concaveConj_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    conj B f y = -(concaveConj B (fun x => -(f x)) (-y)) := by
  rw [neg_concaveConj, neg_neg]
  simp only [neg_neg]

/-! ### Order-theoretic API -/

/-- `c ≤ g*(y)` says exactly that the affine function `x ↦ ⟨x, y⟩ - c` lies *above* `g`. This is
the mirror of `conj_le_coe_iff`, and, like it, has no side condition: it rests on
`Tdaf.EReal.le_coe_sub_comm`. -/
theorem coe_le_concaveConj_iff : (c : EReal) ≤ concaveConj B g y ↔ g ≤ affineFn B y c := by
  rw [concaveConj_apply, le_iInf_iff]
  exact forall_congr' fun x => Tdaf.EReal.le_coe_sub_comm

/-- **Concave conjugacy reverses inequalities.** -/
theorem concaveConj_antitone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Antitone (concaveConj B) := fun _ _ hgh _ =>
  le_iInf fun x => (iInf_le _ x).trans (_root_.EReal.sub_le_sub le_rfl (hgh x))

/-- **The adjunction.** `h ≤ g*` and `g ≤ h*` say the same thing, namely that
`g x + h y ≤ ⟨x, y⟩` for all `x` and `y` in the `∞ - ∞`-free reading. -/
theorem le_concaveConj_iff {h : F → EReal} :
    h ≤ concaveConj B g ↔ g ≤ concaveConj B.flip h := by
  simp only [Pi.le_def, concaveConj_apply, le_iInf_iff, LinearMap.flip_apply]
  rw [forall_comm]
  exact forall₂_congr fun _ _ => Tdaf.EReal.le_coe_sub_comm

/-- The biconjugate is always a majorant: `g ≤ g**`, with no hypothesis on `g`. -/
theorem le_biconcaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) : g ≤ biconcaveConj B g :=
  le_concaveConj_iff.1 le_rfl

/-! ### The improper cases -/

/-- The concave conjugate takes the value `⊤` at a point exactly when `g` is identically `-∞` — a
condition that does not depend on the point. -/
theorem concaveConj_eq_top_iff : concaveConj B g y = ⊤ ↔ ∀ x, g x = ⊥ := by
  rw [concaveConj_eq_neg_conj_neg, _root_.EReal.neg_eq_top_iff, conj_eq_bot_iff]
  exact forall_congr' fun _ => _root_.EReal.neg_eq_top_iff

/-- **If `g` takes the value `+∞` anywhere, its concave conjugate is identically `-∞`.** -/
theorem concaveConj_of_eq_top {x₀ : E} (hx : g x₀ = ⊤) : concaveConj B g = fun _ => ⊥ := by
  funext y
  rw [concaveConj_eq_neg_conj_neg, conj_of_eq_bot (x₀ := x₀) (by rw [hx, _root_.EReal.neg_top]),
    _root_.EReal.neg_top]

/-- **The concave conjugate of `-∞` is `+∞`.** -/
theorem concaveConj_bot (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    concaveConj B (fun _ => ⊥) = fun _ => (⊤ : EReal) :=
  funext fun _ => concaveConj_eq_top_iff.2 fun _ => rfl

/-- **The concave conjugate of `+∞` is `-∞`.** -/
theorem concaveConj_top (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    concaveConj B (fun _ => ⊤) = fun _ => (⊥ : EReal) :=
  concaveConj_of_eq_top (x₀ := (0 : E)) rfl

/-- The concave conjugate of a function with nonempty effective domain never takes the value
`⊤`. -/
theorem concaveConj_ne_top (hd : (domConcave g).Nonempty) (y : F) : concaveConj B g y ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hd
  exact fun hc => absurd (concaveConj_eq_top_iff.1 hc x) hx.ne'

/-- **Fenchel's inequality for concave functions** (Rockafellar §30): `g x + g*(y) ≤ ⟨x, y⟩`.

**It needs no properness hypothesis**, unlike its convex mirror `le_add_conj`, and the asymmetry is
real rather than an oversight. The convex inequality `⟨x, y⟩ ≤ f x + f* y` fails at improper `f`
because the right-hand side collapses to `⊤ + ⊥ = ⊥`; here the same collapse happens on the
*smaller* side of the inequality, where `⊥` is harmless. So both `concaveConj_le_sub` and the named
inequality are unconditional on the concave side. -/
theorem add_concaveConj_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) (y : F) :
    g x + concaveConj B g y ≤ ((B x y : ℝ) : EReal) := by
  rw [add_comm]
  exact (_root_.EReal.le_sub_iff_add_le (.inr (_root_.EReal.coe_ne_bot _))
    (.inr (_root_.EReal.coe_ne_top _))).1 (concaveConj_le_sub B g x y)

/-! ### Concavity of the concave conjugate -/

/-- **The concave conjugate of an arbitrary function is concave.** No hypothesis on `g`: this is
the mirror of `convexFn_conj`, and it is what makes the concave conjugate an operation on
concave functions rather than merely a formula. -/
theorem concaveFn_concaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) :
    ConcaveFn (concaveConj B g) := by
  rw [concaveFn_iff_convexFn_neg]
  have hrw : (fun y => -(concaveConj B g y)) = compLin (conj B fun x => -(g x)) (-LinearMap.id) :=
    funext fun y => neg_concaveConj B g y
  rw [hrw]
  exact convexFn_compLin _ (convexFn_conj B _)

/-! ### The biconjugate -/

/-- **The double reflection cancels.** `g** = -(-g)**`, with no sign on the argument: the
reflection introduced on the dual side by the first conjugation is undone by the second. This is
pure algebra — no topology, no pairing hypothesis — and it is what makes concave Fenchel–Moreau a
corollary of the convex one. -/
theorem biconcaveConj_eq_neg_biconj_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) :
    biconcaveConj B g x = -(biconj B (fun x' => -(g x')) x) := by
  have key : ∀ y : F, ((B x (-y) : ℝ) : EReal) - concaveConj B g (-y)
      = -(((B x y : ℝ) : EReal) - conj B (fun x' => -(g x')) y) := fun y => by
    rw [concaveConj_eq_neg_conj_neg, neg_neg, map_neg, _root_.EReal.coe_neg]
    simp only [sub_eq_add_neg]
    rw [_root_.EReal.neg_add (.inl (_root_.EReal.coe_ne_bot _))
      (.inl (_root_.EReal.coe_ne_top _))]
    rfl
  rw [biconcaveConj_apply, biconj_apply, Tdaf.EReal.neg_iSup]
  refine le_antisymm (le_iInf fun y => ?_) (le_iInf fun y => ?_)
  · exact (iInf_le _ (-y)).trans (key y).le
  · refine (iInf_le _ (-y)).trans (le_of_eq ?_)
    have hy := key (-y)
    rw [neg_neg] at hy
    exact hy.symm

end Defs

/-! ### Fenchel–Moreau for concave functions -/

section FenchelMoreau

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {g : E → EReal}

/-- **Rockafellar's Theorem 12.2 for concave functions.** The concave biconjugate of a concave
function is its *concave closure*, the upper semicontinuous hull — which, until `Concave.lean`
grows a closure of its own, is spelled `-(cl (-g))`.

By `biconcaveConj_eq_neg_biconj_neg` this is the convex Fenchel–Moreau theorem read through the
sign dictionary, and needs no separate argument. -/
theorem biconcaveConj_eq_neg_clFn_neg (hg : ConcaveFn g) :
    biconcaveConj B g = fun x => -(clFn (fun x' => -(g x')) x) := by
  funext x
  rw [biconcaveConj_eq_neg_biconj_neg, biconj_eq_clFn hg.convexFn_neg]

/-- A closed concave function — one whose negative is a closed convex function — is its own concave
biconjugate. This is the concave half of Rockafellar's Corollary 12.2.1. -/
theorem biconcaveConj_eq_self (hg : ConcaveFn g) (hc : ClosedFn fun x => -(g x)) :
    biconcaveConj B g = g := by
  rw [biconcaveConj_eq_neg_clFn_neg hg, hc]
  exact funext fun x => neg_neg (g x)

end FenchelMoreau

end Tdaf.ConvexAnalysis
