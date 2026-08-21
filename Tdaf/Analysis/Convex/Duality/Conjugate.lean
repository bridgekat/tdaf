/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Pairing
import Tdaf.Analysis.Convex.Operations.Basic

/-!
# Conjugates of convex functions

Rockafellar's §12, over a dual pair `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`. This is the keystone of the library:
every duality result in Parts III, V, VI, VII and VIII of the book reduces to Fenchel–Moreau,
`f** = cl f`, which is proved here.

## Main definitions

* `Tdaf.conj B f` — the conjugate `f*(y) = sup_x (⟨x, y⟩ - f x)`.
* `Tdaf.biconj B f` — the biconjugate `f**`, back on `E`.
* `Tdaf.conjClosure B` — conjugacy packaged as a `ClosureOperator` on `(E → EReal)ᵒᵈ`, whose
  closed elements are (Fenchel–Moreau) exactly the closed convex functions.
* `Tdaf.conjEquiv` — the involution of **Corollary 12.2.1** on closed proper convex functions.

## Main results

* `Tdaf.le_add_conj` — **Fenchel's inequality** `⟨x, y⟩ ≤ f x + f* y`. See the design note below:
  as an inequality in `EReal` it needs `Tdaf.Proper f`, and the hypothesis is not removable.
* `Tdaf.sub_le_conj`, `Tdaf.conj_le_coe_iff`, `Tdaf.conj_le_iff` — the hypothesis-free forms of the
  same fact. The last says that `conj B` and `conj B.flip` are an *antitone Galois connection*.
* `Tdaf.convexFn_conj`, `Tdaf.closedFn_conj`, `Tdaf.conj_antitone` — the conjugate of an arbitrary
  function is a closed convex function, and conjugacy reverses the order.
* `Tdaf.conj_of_eq_bot`, `Tdaf.conj_top`, `Tdaf.conj_eq_bot_iff` — the improper cases.
* `Tdaf.conj_clFn` — **Theorem 12.2**, first half: `(cl f)* = f*`.
* `Tdaf.exists_affineFn_le_of_lt`, `Tdaf.eq_biSup_affineFn` — **Theorem 12.1**: a closed convex
  function is the pointwise supremum of the affine functions below it.
* `Tdaf.biconj_eq_clFn` — **Theorem 12.2**, Fenchel–Moreau: `f** = cl f` for convex `f`.
* `Tdaf.proper_conj_iff` — **Theorem 12.2**, properness half.
* `Tdaf.biconj_eq_clFn_weak`, `Tdaf.biconj_eq_clFn_topDual`, `Tdaf.biconj_eq_clFn_inner` —
  Fenchel–Moreau with every hypothesis discharged, for the three canonical pairings: `WeakBilin B`,
  a locally convex space against `topDualPairing`, and a real Hilbert space against its own inner
  product.
* `Tdaf.gc_conj_conj`, `Tdaf.conjClosure` — conjugacy as an antitone Galois connection and the
  closure operator it induces, mirroring `Tdaf.gc_ofEpi_epi` and `Tdaf.epiClosure`.

## Design notes

**The topology is a hypothesis, not a type synonym.** Fenchel–Moreau needs `E` to carry a topology
that is *compatible* with the pairing, meaning that the continuous linear functionals on `E` are
exactly the `⟨·, y⟩`. Rather than fix the weak topology `σ(E, F)` — that is, work in the type
synonym `WeakBilin B` — the theorems below carry the two halves of compatibility as explicit
hypotheses,

* `hBc : ∀ y, Continuous fun x => B x y` — the topology is at least as fine as `σ(E, F)`;
* `hBs : ∀ g : E →L[ℝ] ℝ, ∃ y, ∀ x, g x = B x y` — and no finer, as far as functionals go.

This costs nothing (in `WeakBilin B` both are Mathlib theorems, recorded as
`Tdaf.continuous_weakPairing` and `Tdaf.exists_weakPairing_eq`, and the `WeakBilin` corollaries at
the end of this file are one-liners) and it means that a normed space with its norm topology, a
Hilbert space, and `ℝⁿ` are all covered directly, without any transport. It is *not* a substitute
for `Duality/Compatible.lean`, whose job is the different and harder statement that the *closure*
of a convex set does not depend on which compatible topology is chosen.

**Fenchel's inequality is not hypothesis-free.** `⟨x, y⟩ ≤ f x + f* y` is *false* in `EReal` when
`f ≡ +∞`: then `f* ≡ -∞` and the right-hand side is `⊤ + ⊥ = ⊥`. It is false again when `f` takes
`-∞`: then `f* ≡ +∞` and the right-hand side is `⊥ + ⊤ = ⊥`. Rockafellar states the inequality
"for any proper convex function `f` and its conjugate", and `Tdaf.Proper f` is exactly what is
needed. The `∞ - ∞`-free form `⟨x, y⟩ - f x ≤ f* y` (`Tdaf.sub_le_conj`) is unconditional, and it
is the form every proof below actually uses.

**`Tdaf.EReal.coe_sub_le_comm` does the work.** Because `⟨x, y⟩` is always a *real* number,
`⟨x, y⟩ - z ≤ w ↔ ⟨x, y⟩ - w ≤ z` holds with no side condition whatsoever. That single symmetry is
what makes `Tdaf.conj_le_iff` — and hence the Galois connection, `Tdaf.biconj_le`, and half of
Fenchel–Moreau — unconditional, improper functions included.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §12 (Theorem 12.1,
  Theorem 12.2, Corollary 12.1.1, Corollary 12.1.2, Corollary 12.2.1).
-/

open Set OrderDual

namespace Tdaf

/-! ### The conjugate -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **convex conjugate** of `f` with respect to the pairing `B`:
`f*(y) = sup_x (⟨x, y⟩ - f x)`.

Rockafellar §12: `epi f*` is the set of pairs `(y, c)` for which the affine function
`x ↦ ⟨x, y⟩ - c` is majorized by `f`, so `f*` is exactly a description of the affine minorants of
`f`. No hypothesis at all is placed on `f`; the conjugate of an arbitrary function is the conjugate
of its closed convex hull. -/
noncomputable def conj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : F → EReal :=
  fun y => ⨆ x : E, ((B x y : ℝ) : EReal) - f x

/-- The **biconjugate**, back on `E`. Using `B.flip` rather than a second copy of `B` makes the
correspondence symmetric with no reflexivity assumption; note that `B.flip.flip = B` holds by
`rfl`. -/
noncomputable abbrev biconj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : E → EReal :=
  conj B.flip (conj B f)

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal} {x : E} {y : F} {c : ℝ}

theorem conj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    conj B f y = ⨆ x : E, ((B x y : ℝ) : EReal) - f x := rfl

theorem biconj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) :
    biconj B f x = ⨆ y : F, ((B x y : ℝ) : EReal) - conj B f y := rfl

/-- **Fenchel's inequality, `∞ - ∞`-free.** This is the defining property of the supremum, and it
holds for every `f`, `x` and `y`. Every proof in this file goes through it rather than through the
additive form `Tdaf.le_add_conj`. -/
theorem sub_le_conj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) (y : F) :
    ((B x y : ℝ) : EReal) - f x ≤ conj B f y :=
  le_iSup (fun x : E => ((B x y : ℝ) : EReal) - f x) x

/-- `f*(y) ≤ c` says exactly that the affine function `x ↦ ⟨x, y⟩ - c` lies below `f`. This is the
translation, promised in Rockafellar's §12, of "`epi f*` describes the affine minorants of `f`". -/
theorem conj_le_coe_iff : conj B f y ≤ (c : EReal) ↔ affineFn B y c ≤ f := by
  rw [conj_apply, iSup_le_iff, affineFn_le_iff]

/-- **Conjugacy reverses inequalities** (Rockafellar §12). -/
theorem conj_antitone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Antitone (conj B) := fun _ _ h _ =>
  iSup_mono fun x => _root_.EReal.sub_le_sub le_rfl (h x)

/-- **The adjunction.** `f* ≤ g` and `g* ≤ f` say the same thing — namely that
`⟨x, y⟩ ≤ f x + g y` for all `x` and `y`, in the `∞ - ∞`-free reading. Rockafellar's discussion of
the "best inequalities of the type `⟨x, y⟩ ≤ f x + g y`" is exactly this statement. -/
theorem conj_le_iff {g : F → EReal} : conj B f ≤ g ↔ conj B.flip g ≤ f := by
  simp only [Pi.le_def, conj_apply, iSup_le_iff, LinearMap.flip_apply]
  rw [forall_comm]
  exact forall₂_congr fun _ _ => EReal.coe_sub_le_comm

/-- The biconjugate is always a minorant: `f** ≤ f`, with no hypothesis on `f`. -/
theorem biconj_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : biconj B f ≤ f :=
  conj_le_iff.1 le_rfl

/-! ### The improper cases -/

/-- The conjugate takes the value `⊥` at a point exactly when `f` is identically `⊤` — a condition
that does not depend on the point. So `conj B f` is either the constant `⊥` or never `⊥`, which is
why it is always a *closed* convex function. -/
theorem conj_eq_bot_iff : conj B f y = ⊥ ↔ ∀ x, f x = ⊤ := by
  rw [conj_apply, iSup_eq_bot]
  exact forall_congr' fun _ => EReal.coe_sub_eq_bot_iff

/-- **If `f` takes the value `⊥` anywhere, its conjugate is identically `⊤`.** -/
theorem conj_of_eq_bot {x₀ : E} (h : f x₀ = ⊥) : conj B f = fun _ => ⊤ := by
  funext y
  refine top_le_iff.1 (le_trans ?_ (sub_le_conj B f x₀ y))
  rw [h, _root_.EReal.coe_sub_bot]

/-- **The conjugate of `+∞` is `-∞`.** -/
theorem conj_top (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : conj B (fun _ => ⊤) = fun _ => (⊥ : EReal) :=
  funext fun _ => conj_eq_bot_iff.2 fun _ => rfl

/-- **The conjugate of `-∞` is `+∞`.** -/
theorem conj_bot (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : conj B (fun _ => ⊥) = fun _ => (⊤ : EReal) :=
  conj_of_eq_bot (x₀ := (0 : E)) rfl

/-- The conjugate of a function with nonempty effective domain never takes the value `⊥`. -/
theorem conj_ne_bot (h : (dom f).Nonempty) (y : F) : conj B f y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := h
  exact fun hc => absurd (conj_eq_bot_iff.1 hc x) hx.ne

/-- **Fenchel's inequality** (Rockafellar §12): `⟨x, y⟩ ≤ f x + f*(y)` for a proper `f`.

The properness hypothesis is not decorative. If `f ≡ +∞` then `f* ≡ -∞` and the right-hand side is
`⊤ + ⊥ = ⊥`; if `f` takes `-∞` then `f* ≡ +∞` and the right-hand side is `⊥ + ⊤ = ⊥`. In both cases
the inequality fails. Use `Tdaf.sub_le_conj` when no properness is available. -/
theorem le_add_conj (hb : f x ≠ ⊥) (hd : (dom f).Nonempty) (y : F) :
    ((B x y : ℝ) : EReal) ≤ f x + conj B f y := by
  rw [add_comm]
  exact (_root_.EReal.sub_le_iff_le_add (.inl hb) (.inr (conj_ne_bot hd y))).1 (sub_le_conj B f x y)

/-- Fenchel's inequality, packaged against `Tdaf.Proper`. -/
theorem Proper.le_add_conj (hp : Proper f) (x : E) (y : F) :
    ((B x y : ℝ) : EReal) ≤ f x + conj B f y :=
  _root_.Tdaf.le_add_conj (hp.ne_bot x) hp.dom_nonempty y

/-- If the conjugate is proper then so is the original function; no hypothesis is needed for this
direction. The converse is `Tdaf.proper_conj`, and needs closedness. -/
theorem proper_of_proper_conj (h : Proper (conj B f)) : Proper f := by
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := h.dom_nonempty
    by_contra hd
    rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hd
    exact absurd (conj_eq_bot_iff.2 fun x => top_le_iff.1 (not_lt.1 (hd x))) (h.ne_bot y)
  · obtain ⟨y, hy⟩ := h.dom_nonempty
    rw [conj_of_eq_bot hx] at hy
    exact absurd hy (by simp)

/-! ### Convexity of the conjugate -/

/-- The `x`-th term of the supremum defining `conj B f` is, as a function of `y`, either constant
or one of the affine functions of the flipped pairing. This trichotomy is the whole proof that the
conjugate is convex and closed, and it is where the three possible values of `f x` are consumed. -/
theorem conj_term_eq (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) :
    (fun y => ((B x y : ℝ) : EReal) - f x) = (fun _ => (⊥ : EReal)) ∨
      (fun y => ((B x y : ℝ) : EReal) - f x) = (fun _ => (⊤ : EReal)) ∨
      ∃ t : ℝ, (fun y => ((B x y : ℝ) : EReal) - f x) = affineFn B.flip x t := by
  rcases eq_or_ne (f x) ⊤ with h | h
  · exact Or.inl (funext fun y => by rw [h, _root_.EReal.sub_top])
  rcases eq_or_ne (f x) ⊥ with h' | h'
  · exact Or.inr (Or.inl (funext fun y => by rw [h', _root_.EReal.coe_sub_bot]))
  · obtain ⟨t, ht⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top h' (lt_top_iff_ne_top.2 h)
    exact Or.inr (Or.inr ⟨t, funext fun y => by rw [ht, affineFn_apply, LinearMap.flip_apply]⟩)

/-- **The conjugate of an arbitrary function is convex** (Rockafellar §12): it is a pointwise
supremum of affine functions and constants. -/
theorem convexFn_conj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : ConvexFn (conj B f) := by
  refine convexFn_iSup fun x => ?_
  rcases conj_term_eq B f x with h | h | ⟨t, h⟩ <;> rw [h]
  · exact convexFn_const ⊥
  · exact convexFn_const ⊤
  · exact convexFn_affineFn x t

end Defs

/-! ### Why Fenchel's inequality needs properness

The two `example`s below are the reason `Tdaf.le_add_conj` carries hypotheses, and they are why
`Tdaf.sub_le_conj` rather than `Tdaf.le_add_conj` is what the proofs in this file use. In `EReal`
the value `⊥` is absorbing for addition, so `⊤ + ⊥ = ⊥ + ⊤ = ⊥`, and the additive form of Fenchel's
inequality collapses at each of the two improper functions. Rockafellar states the inequality only
"for any proper convex function `f` and its conjugate". -/

example : ¬ (((innerₗ ℝ) (0 : ℝ) (0 : ℝ) : ℝ) : EReal)
    ≤ (fun _ : ℝ => (⊤ : EReal)) 0 + conj (innerₗ ℝ) (fun _ : ℝ => (⊤ : EReal)) 0 := by
  rw [conj_top]
  simp

example : ¬ (((innerₗ ℝ) (0 : ℝ) (0 : ℝ) : ℝ) : EReal)
    ≤ (fun _ : ℝ => (⊥ : EReal)) 0 + conj (innerₗ ℝ) (fun _ : ℝ => (⊥ : EReal)) 0 := by
  rw [conj_bot]
  simp

/-! ### Closedness of the conjugate

The conjugate is closed in *any* topology on `F` for which the pairing is continuous — in
particular in `σ(F, E)`, and hence also in the norm topology of a normed space paired with its
dual. -/

section ConjClosed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- The conjugate is lower semicontinuous whenever the pairing is continuous in its second
variable. -/
theorem lowerSemicontinuous_conj (hB : ∀ x : E, Continuous fun y : F => B x y) :
    LowerSemicontinuous (conj B f) := by
  refine lowerSemicontinuous_iSup fun x => ?_
  rcases conj_term_eq B f x with h | h | ⟨t, h⟩ <;> rw [h]
  · exact lowerSemicontinuous_const
  · exact lowerSemicontinuous_const
  · exact lowerSemicontinuous_affineFn (hB x)

variable [IsTopologicalAddGroup F]

/-- **The conjugate is a closed convex function** (Rockafellar §12), with no hypothesis on `f`.

The two branches of `Tdaf.closedFn_iff` correspond exactly to the two possibilities for `f`: if
`f ≡ +∞` the conjugate is the constant `⊥`, and otherwise it is lower semicontinuous and never
takes `⊥`. -/
theorem closedFn_conj (hB : ∀ x : E, Continuous fun y : F => B x y) : ClosedFn (conj B f) := by
  rw [closedFn_iff]
  by_cases h : ∀ x, f x = ⊤
  · exact Or.inl (funext fun _ => conj_eq_bot_iff.2 h)
  · exact Or.inr ⟨lowerSemicontinuous_conj hB, fun _ hy => h (conj_eq_bot_iff.1 hy)⟩

end ConjClosed

/-! ### The conjugate sees only the closure -/

section ConjClosure

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **Rockafellar, Theorem 12.2** (first half): `(cl f)* = f*`.

The affine functions below `f` and the affine functions below `cl f` are the same, because an
affine function of a continuous pairing is itself closed; and `f*` is nothing but a description of
that collection. -/
theorem conj_clFn (hBc : ∀ y : F, Continuous fun x : E => B x y) (f : E → EReal) :
    conj B (clFn f) = conj B f := by
  funext y
  refine Tdaf.EReal.eq_of_forall_le_coe_iff fun c => ?_
  rw [conj_le_coe_iff, conj_le_coe_iff]
  exact ⟨fun h => h.trans (clFn_le f), fun h => le_clFn_of_le (closedFn_affineFn (hBc y)) h⟩

/-- The biconjugate is a closed convex minorant of `f`, hence a minorant of `cl f`. This is the
easy half of Fenchel–Moreau, and it needs no convexity. -/
theorem biconj_le_clFn (hBc : ∀ y : F, Continuous fun x : E => B x y) (f : E → EReal) :
    biconj B f ≤ clFn f :=
  le_clFn_of_le (closedFn_conj (B := B.flip) hBc) (biconj_le B f)

end ConjClosure

/-! ### Theorem 12.1 -/

section Theorem121

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **Rockafellar, Theorem 12.1**, in its working form: below any value strictly under a closed
convex function there is an affine minorant of the pairing.

The proof is Rockafellar's. `epi f` is a closed convex set not containing `(x₀, α)`, so a
continuous linear functional on `E × ℝ` separates them; splitting it with
`Tdaf.exists_unique_dual_prod` into a horizontal part `g` and a vertical coefficient `c₀`, upward
closedness of `epi f` forces `c₀ ≤ 0` — no *lower* half-space can contain an epigraph. If `c₀ < 0`
the functional is *upper* and rescaling by `-c₀` gives the affine minorant directly. If `c₀ = 0`
the functional is *vertical*, and the last paragraph of Rockafellar's proof applies: `g - u` is
`≤ 0` on `dom f` and `> 0` at `x₀`, so adding a large multiple of it to the affine minorant
supplied by `Tdaf.exists_affine_le_of_closed_proper` produces a non-vertical one. -/
theorem exists_affineFn_le_of_lt (hBs : ∀ g : E →L[ℝ] ℝ, ∃ y : F, ∀ x, g x = B x y)
    (hf : ConvexFn f) (hc : ClosedFn f) {x₀ : E} {α : ℝ} (h : (α : EReal) < f x₀) :
    ∃ (y : F) (c : ℝ), affineFn B y c ≤ f ∧ (α : EReal) < affineFn B y c x₀ := by
  by_cases hp : Proper f
  case neg =>
    -- A closed improper function is constant; `f ≡ -∞` contradicts `α < f x₀`, and every affine
    -- function lies below `f ≡ +∞`.
    rcases eq_const_of_closedFn_of_not_proper hc hp with hbot | htop
    · rw [hbot] at h; exact absurd h (by simp)
    · refine ⟨0, -(α + 1), htop ▸ fun _ => le_top, ?_⟩
      rw [affineFn_eq_coe, map_zero, _root_.EReal.coe_lt_coe_iff]
      linarith
  case pos =>
  -- A point of the epigraph over any point of the effective domain.
  have hmem : ∀ x, f x < ⊤ → ∃ μ : ℝ, (x, μ) ∈ epi f := by
    intro x hx
    obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
    exact ⟨r, by rw [mk_mem_epi, hr]⟩
  have hnot : ((x₀, α) : E × ℝ) ∉ epi f := fun hcon => absurd (mk_mem_epi.1 hcon) (not_le.2 h)
  have hclosed : IsClosed (epi f) :=
    lowerSemicontinuous_iff_isClosed_epi.1 hc.lowerSemicontinuous
  obtain ⟨L, u, hLs, hLx⟩ := geometric_hahn_banach_closed_point hf.convex_epi hclosed hnot
  set g : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E ℝ) with hg
  set c₀ : ℝ := L (0, 1) with hc₀def
  have hL : ∀ (x : E) (μ : ℝ), L (x, μ) = g x + c₀ * μ := dual_prod_apply L
  -- The separating functional cannot be a *lower* half-space: `epi f` is unbounded above.
  obtain ⟨x₁, hx₁⟩ := hp.dom_nonempty
  obtain ⟨μ₁, hμ₁⟩ := hmem x₁ hx₁
  have hc₀ : c₀ ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    set t : ℝ := max 0 ((u - g x₁ - c₀ * μ₁) / c₀) with ht
    have ht0 : 0 ≤ t := le_max_left _ _
    have htle : (u - g x₁ - c₀ * μ₁) / c₀ ≤ t := le_max_right _ _
    have hin : ((x₁, μ₁ + t) : E × ℝ) ∈ epi f :=
      mk_mem_epi.2 ((mk_mem_epi.1 hμ₁).trans
        (by exact_mod_cast (by linarith : μ₁ ≤ μ₁ + t)))
    have hbnd := hLs _ hin
    rw [hL] at hbnd
    have := (div_le_iff₀ hpos).1 htle
    nlinarith
  obtain ⟨y₁, hy₁⟩ := hBs g
  rcases lt_or_eq_of_le hc₀ with hneg | hzero
  · -- Upper half-space: rescale by `-c₀ > 0`.
    have hd : 0 < -c₀ := by linarith
    have hy : ∀ x, B x ((-c₀)⁻¹ • y₁) = (-c₀)⁻¹ * g x := fun x => by
      rw [map_smul, smul_eq_mul, hy₁ x]
    refine ⟨(-c₀)⁻¹ • y₁, u / (-c₀), fun x => ?_, ?_⟩
    · rw [affineFn_eq_coe, hy]
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨μ, hfμ, hμ⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hcon
      have hin : ((x, μ) : E × ℝ) ∈ epi f := mk_mem_epi.2 hfμ.le
      have hbnd := hLs _ hin
      rw [hL] at hbnd
      have hμ' : μ < (-c₀)⁻¹ * g x - u / (-c₀) := by exact_mod_cast hμ
      rw [inv_mul_eq_div, div_sub_div_same, lt_div_iff₀ hd] at hμ'
      nlinarith
    · rw [affineFn_eq_coe, hy, _root_.EReal.coe_lt_coe_iff, inv_mul_eq_div, div_sub_div_same,
        lt_div_iff₀ hd]
      rw [hL] at hLx
      nlinarith
  · -- Vertical half-space: absorb it into a known affine minorant.
    obtain ⟨w, c₂, hw⟩ := exists_affine_le_of_closed_proper hf hc hp
    obtain ⟨y₂, hy₂⟩ := hBs w
    have hdom : ∀ x, f x < ⊤ → g x < u := by
      intro x hx
      obtain ⟨μ, hμ⟩ := hmem x hx
      have hbnd := hLs _ hμ
      rw [hL, hzero] at hbnd
      simpa using hbnd
    have hgx₀ : u < g x₀ := by rw [hL, hzero] at hLx; simpa using hLx
    set d : ℝ := g x₀ - u with hdd
    have hdpos : 0 < d := by rw [hdd]; linarith
    set m : ℝ := B x₀ y₂ - c₂ with hm
    set lam : ℝ := max 0 ((α + 1 - m) / d) with hlam
    have hlam0 : 0 ≤ lam := le_max_left _ _
    have hlamle : (α + 1 - m) / d ≤ lam := le_max_right _ _
    refine ⟨lam • y₁ + y₂, lam * u + c₂, fun x => ?_, ?_⟩
    · rw [affineFn_smul_add]
      rcases lt_or_ge (f x) ⊤ with hx | hx
      · have h1 : lam * (B x y₁ - u) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hlam0 (by rw [← hy₁ x]; linarith [hdom x hx])
        refine le_trans ?_ (hy₂ x ▸ hw x)
        rw [← _root_.EReal.coe_sub, _root_.EReal.coe_le_coe_iff]
        linarith
      · rw [top_le_iff.1 hx]; exact le_top
    · rw [affineFn_smul_add, _root_.EReal.coe_lt_coe_iff, ← hy₁ x₀, ← hm]
      have := (div_le_iff₀ hdpos).1 hlamle
      nlinarith

/-- **Rockafellar, Theorem 12.1.** A closed convex function is the pointwise supremum of the
collection of all affine functions of the pairing that lie below it. -/
theorem eq_biSup_affineFn (hBs : ∀ g : E →L[ℝ] ℝ, ∃ y : F, ∀ x, g x = B x y)
    (hf : ConvexFn f) (hc : ClosedFn f) :
    f = fun x => ⨆ p ∈ {p : F × ℝ | affineFn B p.1 p.2 ≤ f}, affineFn B p.1 p.2 x := by
  funext x
  refine le_antisymm ?_ (iSup₂_le fun p hp => hp x)
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨α, hα₁, hα₂⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hcon
  obtain ⟨y, c, hle, hlt⟩ := exists_affineFn_le_of_lt hBs hf hc hα₂
  exact absurd (lt_of_lt_of_le hlt (le_iSup₂ (f := fun p (_ : p ∈ _) => affineFn B p.1 p.2 x)
    ((y, c) : F × ℝ) hle)) (not_lt.2 hα₁.le)

end Theorem121

/-! ### Theorem 12.2: Fenchel–Moreau -/

section FenchelMoreau

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **Rockafellar, Theorem 12.2 — the Fenchel–Moreau theorem.** For a convex function,
`f** = cl f`.

The improper cases come first and are the reason `Tdaf.clFn` is defined by branching on
`Tdaf.lscHull f` rather than on `f`: if `f` takes `-∞` anywhere then `f* ≡ +∞` and `f** ≡ -∞`,
which is `cl f` only under that branching; and if `f ≡ +∞` then `f* ≡ -∞` and `f** ≡ +∞ = cl f`.

In the proper case, `f** ≤ cl f` is `Tdaf.biconj_le_clFn`, needing no convexity. The converse is
Theorem 12.1 applied to `cl f`: an affine minorant of `cl f` strictly above a given value at `x₀`
is an affine minorant of `f`, so it is recorded in `f*` and hence in `f**`. -/
theorem biconj_eq_clFn (hBc : ∀ y : F, Continuous fun x : E => B x y)
    (hBs : ∀ g : E →L[ℝ] ℝ, ∃ y : F, ∀ x, g x = B x y) (hf : ConvexFn f) :
    biconj B f = clFn f := by
  by_cases hb : ∃ x, f x = ⊥
  · obtain ⟨x₀, hx₀⟩ := hb
    have hbot : lscHull f x₀ = ⊥ := le_bot_iff.1 (hx₀ ▸ lscHull_le f x₀)
    rw [clFn_of_exists_eq_bot ⟨x₀, hbot⟩]
    change conj B.flip (conj B f) = _
    rw [conj_of_eq_bot hx₀, conj_top]
  push Not at hb
  by_cases ht : ∀ x, f x = ⊤
  · have hfeq : f = fun _ => (⊤ : EReal) := funext ht
    rw [hfeq]
    change conj B.flip (conj B (fun _ => (⊤ : EReal))) = _
    rw [conj_top, conj_bot]
    exact closedFn_const_top.symm
  refine le_antisymm (biconj_le_clFn hBc f) fun x₀ => ?_
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨α, hα₁, hα₂⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hcon
  obtain ⟨y, c, hle, hlt⟩ :=
    exists_affineFn_le_of_lt hBs (convexFn_clFn hf) (closedFn_clFn f) hα₂
  have hcy : conj B f y ≤ (c : EReal) := conj_le_coe_iff.2 (hle.trans (clFn_le f))
  refine absurd (lt_of_lt_of_le hlt ?_) (not_lt.2 hα₁.le)
  refine le_trans ?_ (sub_le_conj B.flip (conj B f) y x₀)
  rw [affineFn_apply, LinearMap.flip_apply]
  exact _root_.EReal.sub_le_sub le_rfl hcy

/-- **Rockafellar, Theorem 12.2** (properness half): the conjugate of a closed proper convex
function is proper. Together with `Tdaf.proper_of_proper_conj` this is "`f*` is proper if and only
if `f` is". -/
theorem proper_conj (hBs : ∀ g : E →L[ℝ] ℝ, ∃ y : F, ∀ x, g x = B x y)
    (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) : Proper (conj B f) := by
  obtain ⟨w, c, hw⟩ := exists_affine_le_of_closed_proper hf hc hp
  obtain ⟨y, hy⟩ := hBs w
  refine ⟨⟨y, lt_of_le_of_lt (conj_le_coe_iff.2 fun x => ?_) (_root_.EReal.coe_lt_top c)⟩,
    conj_ne_bot hp.dom_nonempty⟩
  rw [affineFn_apply, ← hy x]
  exact hw x

/-- **Rockafellar, Theorem 12.2**, properness in full. -/
theorem proper_conj_iff (hBs : ∀ g : E →L[ℝ] ℝ, ∃ y : F, ∀ x, g x = B x y)
    (hf : ConvexFn f) (hc : ClosedFn f) : Proper (conj B f) ↔ Proper f :=
  ⟨proper_of_proper_conj, proper_conj hBs hf hc⟩

/-- A closed convex function is its own biconjugate. -/
theorem biconj_eq_self (hBc : ∀ y : F, Continuous fun x : E => B x y)
    (hBs : ∀ g : E →L[ℝ] ℝ, ∃ y : F, ∀ x, g x = B x y) (hf : ConvexFn f) (hc : ClosedFn f) :
    biconj B f = f := (biconj_eq_clFn hBc hBs hf).trans hc

end FenchelMoreau

/-! ### Conjugacy as a Galois connection

`Tdaf.conj_le_iff` says that `conj B` and `conj B.flip` are adjoint, antitonely, exactly as
`Tdaf.subset_epi_iff_le_ofEpi` does for `ofEpi` and `epi`. Recording it makes the whole
`ClosureOperator` API available, and Fenchel–Moreau then identifies the closed elements of that
operator with the closed convex functions. As with `Tdaf.gc_ofEpi_epi`, the `OrderDual` on the
domain is what makes the antitone adjunction fit Mathlib's monotone `GaloisConnection`. -/

section Galois

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Conjugacy is an antitone Galois connection between `E → EReal` and `F → EReal`. -/
theorem gc_conj_conj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    GaloisConnection (fun f : (E → EReal)ᵒᵈ => conj B (ofDual f))
      (fun g : F → EReal => toDual (conj B.flip g)) := fun _ _ => conj_le_iff

/-- The closure operator `f ↦ f**` induced by the adjunction. Its closed elements are the functions
equal to their own biconjugate, which by Fenchel–Moreau (`Tdaf.isClosed_conjClosure_iff`) are
exactly the closed convex functions. -/
noncomputable def conjClosure (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : ClosureOperator (E → EReal)ᵒᵈ :=
  (gc_conj_conj B).closureOperator

@[simp] theorem conjClosure_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    conjClosure B (toDual f) = toDual (biconj B f) := rfl

/-- Closedness for `Tdaf.conjClosure` is the fixed-point equation `f** = f`. -/
theorem isClosed_conjClosure_iff {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} :
    (conjClosure B).IsClosed (toDual f) ↔ biconj B f = f :=
  ⟨fun h => congrArg ofDual h, fun h => congrArg toDual h⟩

/-- Conjugating three times is the same as conjugating once — the triangle identity, which for
conjugacy is the statement that `f*` is unchanged by closure (Rockafellar's Theorem 12.2 for the
conjugate function). -/
theorem conj_biconj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : conj B (biconj B f) = conj B f :=
  le_antisymm (conj_le_iff.2 (le_refl (biconj B f))) (conj_antitone B (biconj_le B f))

end Galois

/-! ### Corollary 12.2.1: the involution on closed proper convex functions

Here both spaces carry topologies compatible with the pairing. Everything is symmetric under
`B ↦ B.flip`, and `B.flip.flip = B` holds by `rfl`, so the two directions of the equivalence are
the same argument run twice. -/

section Involution

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)

/-- **Rockafellar, Corollary 12.2.1.** The conjugacy operation induces a symmetric one-to-one
correspondence between the closed proper convex functions on `E` and those on `F`. -/
noncomputable def conjEquiv (hBc : ∀ y : F, Continuous fun x : E => B x y)
    (hBs : ∀ g : E →L[ℝ] ℝ, ∃ y : F, ∀ x, g x = B x y)
    (hBc' : ∀ x : E, Continuous fun y : F => B x y)
    (hBs' : ∀ g : F →L[ℝ] ℝ, ∃ x : E, ∀ y, g y = B x y) :
    {f : E → EReal // ConvexFn f ∧ ClosedFn f ∧ Proper f} ≃
      {g : F → EReal // ConvexFn g ∧ ClosedFn g ∧ Proper g} where
  toFun f := ⟨conj B f.1, convexFn_conj B f.1, closedFn_conj hBc',
    proper_conj hBs f.2.1 f.2.2.1 f.2.2.2⟩
  invFun g := ⟨conj B.flip g.1, convexFn_conj B.flip g.1, closedFn_conj hBc,
    proper_conj hBs' g.2.1 g.2.2.1 g.2.2.2⟩
  left_inv f := Subtype.ext (biconj_eq_self hBc hBs f.2.1 f.2.2.1)
  right_inv g := Subtype.ext (biconj_eq_self (B := B.flip) hBc' hBs' g.2.1 g.2.2.1)

@[simp] theorem conjEquiv_apply (hBc : ∀ y : F, Continuous fun x : E => B x y)
    (hBs : ∀ g : E →L[ℝ] ℝ, ∃ y : F, ∀ x, g x = B x y)
    (hBc' : ∀ x : E, Continuous fun y : F => B x y)
    (hBs' : ∀ g : F →L[ℝ] ℝ, ∃ x : E, ∀ y, g y = B x y)
    (f : {f : E → EReal // ConvexFn f ∧ ClosedFn f ∧ Proper f}) :
    (conjEquiv B hBc hBs hBc' hBs' f : F → EReal) = conj B f := rfl

end Involution

/-! ### Canonical instantiations

Three pairings: the weak topology `σ(E, F)` of an arbitrary pairing, a locally convex space paired
with its own topological dual, and a real Hilbert space paired with itself — Rockafellar's `Rⁿ`. In
each case both compatibility hypotheses are discharged outright, so Fenchel–Moreau holds with no
side condition beyond convexity. -/

section Weak

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)

/-- The conjugate is insensitive to the transport into `WeakBilin B`. -/
@[simp] theorem conj_toWeakFn (f : E → EReal) : conj (weakPairing B) (toWeakFn B f) = conj B f :=
  rfl

/-- **Fenchel–Moreau in the weak topology `σ(E, F)`.** -/
theorem biconj_eq_clFn_weak {f : WeakBilin B → EReal} (hf : ConvexFn f) :
    biconj (weakPairing B) f = clFn f :=
  biconj_eq_clFn (continuous_weakPairing B) (exists_weakPairing_eq B) hf

/-- **Theorem 12.1 in the weak topology `σ(E, F)`.** -/
theorem eq_biSup_affineFn_weak {f : WeakBilin B → EReal} (hf : ConvexFn f) (hc : ClosedFn f) :
    f = fun x => ⨆ p ∈ {p : F × ℝ | affineFn (weakPairing B) p.1 p.2 ≤ f},
      affineFn (weakPairing B) p.1 p.2 x :=
  eq_biSup_affineFn (exists_weakPairing_eq B) hf hc

/-- **Corollary 12.2.1 in the weak topologies `σ(E, F)` and `σ(F, E)`.** -/
noncomputable def conjEquivWeak :
    {f : WeakBilin B → EReal // ConvexFn f ∧ ClosedFn f ∧ Proper f} ≃
      {g : WeakBilin B.flip → EReal // ConvexFn g ∧ ClosedFn g ∧ Proper g} :=
  conjEquiv (weakPairing B) (continuous_weakPairing B) (exists_weakPairing_eq B)
    (continuous_weakPairing B.flip) (exists_weakPairing_eq B.flip)

end Weak

section TopDual

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- **Fenchel–Moreau for a locally convex space paired with its own topological dual**, in the
original topology of `E` and with no hypothesis beyond convexity.

Both halves of compatibility are trivial for `topDualPairing`: a continuous linear functional is
continuous, and it represents itself. -/
theorem biconj_eq_clFn_topDual {f : E → EReal} (hf : ConvexFn f) :
    biconj (topDualPairing ℝ E).flip f = clFn f :=
  biconj_eq_clFn (fun y => y.continuous) (fun g => ⟨g, fun _ => rfl⟩) hf

/-- **Theorem 12.1 for a locally convex space paired with its own topological dual.** -/
theorem eq_biSup_affineFn_topDual {f : E → EReal} (hf : ConvexFn f) (hc : ClosedFn f) :
    f = fun x => ⨆ p ∈ {p : (E →L[ℝ] ℝ) × ℝ | affineFn (topDualPairing ℝ E).flip p.1 p.2 ≤ f},
      affineFn (topDualPairing ℝ E).flip p.1 p.2 x :=
  eq_biSup_affineFn (fun g => ⟨g, fun _ => rfl⟩) hf hc

end TopDual

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Fenchel–Moreau for a real Hilbert space paired with itself by the inner product** — the
setting of Rockafellar's `Rⁿ`, in the norm topology.

Compatibility is the Fréchet–Riesz representation theorem, `InnerProductSpace.toDual`. -/
theorem biconj_eq_clFn_inner {f : E → EReal} (hf : ConvexFn f) :
    biconj (innerₗ E) f = clFn f := by
  refine biconj_eq_clFn (fun y => by simpa using (continuous_id.inner continuous_const : _))
    (fun g => ⟨(InnerProductSpace.toDual ℝ E).symm g, fun x => ?_⟩) hf
  rw [innerₗ_apply_apply, real_inner_comm, InnerProductSpace.toDual_symm_apply]

/-- **Theorem 12.1 for a real Hilbert space paired with itself.** -/
theorem eq_biSup_affineFn_inner {f : E → EReal} (hf : ConvexFn f) (hc : ClosedFn f) :
    f = fun x => ⨆ p ∈ {p : E × ℝ | affineFn (innerₗ E) p.1 p.2 ≤ f},
      affineFn (innerₗ E) p.1 p.2 x := by
  refine eq_biSup_affineFn (fun g => ⟨(InnerProductSpace.toDual ℝ E).symm g, fun x => ?_⟩) hf hc
  rw [innerₗ_apply_apply, real_inner_comm, InnerProductSpace.toDual_symm_apply]

end Hilbert

end Tdaf
