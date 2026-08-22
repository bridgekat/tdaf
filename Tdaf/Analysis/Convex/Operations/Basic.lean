/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Indicator

/-!
# Operations that preserve convexity: the epigraph-only ones

This file collects the operations of Rockafellar, *Convex Analysis*, §5 whose convexity proof needs
nothing beyond the epigraph API of `Tdaf/Analysis/Convex/Epigraph.lean`: pointwise suprema, sums,
multiplication by a nonnegative scalar, composition with a nondecreasing convex function of one
variable, and restriction to a convex set. The operations built from a convex set in `E × ℝ` by
Theorem 5.3 (`ofEpi`, infimal convolution, convex hulls of families, images under linear maps) live
elsewhere.

## Main results

* `convexFn_iSup` — **Theorem 5.5**, the pointwise supremum of convex functions is convex.
  The proof is the set identity `epi_iSup`, `epi (⨆ i, f i) = ⋂ i, epi (f i)`, which is reused
  for support functions.
* `ConvexFn.add` — **Theorem 5.2**, together with `dom_add` and `ConvexFn.sum`.
* `ConvexFn.smul` — multiplication by a nonnegative real (§5).
* `ConvexFn.comp` — **Theorem 5.1**, composition with a nondecreasing convex function.
* `ConvexFn.restrict` — restricting to a convex set preserves convexity, and
  `ConvexFn.add_indicatorFn` says the same thing in the form "adding an indicator function to
  `f` restricts the effective domain" (Rockafellar's remark after Theorem 5.2).

## Design notes

**Why `∀ x, f x ≠ ⊥` and not `Proper f`.** Rockafellar states Theorem 5.2 for *proper* convex
functions, remarking that "the properness in the hypothesis of Theorem 5.2 is for the sake of
avoiding `∞ - ∞`". Only half of properness does that work: the `dom_nonempty` half is irrelevant
(if `f ≡ ⊤` then `f + g ≡ ⊤`, which is convex), while the `ne_bot` half is genuinely needed. Take
`E = ℝ`, `f x = ⊥` for `x > 0` and `⊤` otherwise, `g x = ⊥` for `x < 0` and `⊤` otherwise: their
epigraphs are the convex sets `Ioi 0 ×ˢ univ` and `Iio 0 ×ˢ univ`, so both are convex, but
`(f + g) x = ⊥` for `x ≠ 0` and `⊤` at `x = 0`, whose epigraph `(ℝ \ {0}) ×ˢ univ` is not convex.
So the hypothesis carried here is exactly `∀ x, _ x ≠ ⊥`, written inline rather than bundled.

**How Theorem 5.1 is stated.** Rockafellar takes `φ : ℝ → (-∞, +∞]` convex and nondecreasing and
extends it to `+∞` by `φ (+∞) = +∞`. Since `EReal` is not an `ℝ`-module, `ConvexFn φ` cannot be
stated for `φ : EReal → EReal`; but the *only* thing the proof asks of `φ` off the reals is
monotonicity and the value at `⊤`. `ConvexFn.comp` therefore takes `φ : EReal → EReal` with
three separate hypotheses — `ConvexFn fun r : ℝ => φ r` (convexity, stated where it is statable),
`Monotone φ`, and `φ ⊤ = ⊤` — which is both faithful and directly usable when `φ` is naturally
given on all of `EReal`. `extendTop` performs the book's extension for a `φ` given on `ℝ`, and
`ConvexFn.comp_extendTop` is Theorem 5.1 verbatim in those terms. The hypothesis `φ ⊤ = ⊤` is
not decoration: a monotone convex `φ : ℝ → EReal` bounded above is constant, and gluing a strictly
larger finite value at `⊤` breaks convexity of `φ ∘ f` as soon as `dom f` has nonconvex complement.
Note that `φ` is *not* required to avoid `⊥`, which the book's `(-∞, +∞]` does require; the proof
never needs it.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §5 (Theorems 5.1, 5.2,
  5.5).
-/

open Set

namespace Tdaf.ConvexAnalysis

/-! ### Epigraphs of suprema, sums and restrictions

None of these identities involves the linear structure of `E`. -/

section Basic

variable {E : Type*}

/-- **Rockafellar, Theorem 5.5** (the set-theoretic content). The epigraph of a pointwise supremum
is the intersection of the epigraphs.

This identity, not the convexity statement it proves, is what later files need: the support function
of a set is a pointwise supremum of affine functions, and its epigraph is computed this way. -/
theorem epi_iSup {ι : Sort*} (f : ι → E → EReal) : epi (fun x => ⨆ i, f i x) = ⋂ i, epi (f i) := by
  ext p
  simp [epi, iSup_le_iff]

/-- The `Set`-indexed form of `epi_iSup`. -/
theorem epi_biSup {ι : Type*} (s : Set ι) (f : ι → E → EReal) :
    epi (fun x => ⨆ i ∈ s, f i x) = ⋂ i ∈ s, epi (f i) := by
  ext p
  simp [epi, iSup_le_iff]

/-- The binary case of `epi_iSup`. -/
theorem epi_sup (f g : E → EReal) : epi (f ⊔ g) = epi f ∩ epi g := by
  ext p
  simp [epi, sup_le_iff]

/-- **Rockafellar, Theorem 5.2** (the remark following it). The effective domain of a sum is the
intersection of the effective domains.

Both `≠ ⊥` hypotheses are needed: for `f x = ⊥` and `g x = ⊤` one has `(f + g) x = ⊥ < ⊤`, so `x`
lies in `dom (f + g)` but not in `dom g`. -/
theorem dom_add {f g : E → EReal} (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) :
    dom (f + g) = dom f ∩ dom g := by
  ext x
  simp only [mem_dom, Pi.add_apply, Set.mem_inter_iff, lt_top_iff_ne_top]
  exact _root_.EReal.add_ne_top_iff_ne_top₂ (hf x) (hg x)

/-- The epigraph of a restriction is the epigraph cut down to a vertical slab.

This generalises `epi_restrict_coe` to `EReal`-valued `f`. -/
theorem epi_restrict (s : Set E) (f : E → EReal) : epi (restrict s f) = epi f ∩ s ×ˢ univ := by
  ext p
  by_cases hp : p.1 ∈ s <;> simp [epi, hp]

end Basic

/-! ### Convexity of the operations -/

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A constant function is convex. -/
theorem convexFn_const (c : EReal) : ConvexFn (fun _ : E => c) := by
  refine convexFn_of_epi_combo (fun x y μ ν hx hy a b ha hb hab => ?_)
  have hx' : c ≤ (μ : EReal) := hx
  have hy' : c ≤ (ν : EReal) := hy
  rcases eq_or_ne c ⊥ with rfl | hc
  · exact bot_le
  obtain ⟨r, rfl⟩ :=
    Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top hc (hx'.trans_lt (_root_.EReal.coe_lt_top μ))
  have h1 : r ≤ μ := by exact_mod_cast hx'
  have h2 : r ≤ ν := by exact_mod_cast hy'
  have h3 : a * r + b * r = r := by linear_combination r * hab
  have h4 : a * r ≤ a * μ := mul_le_mul_of_nonneg_left h1 ha
  have h5 : b * r ≤ b * ν := mul_le_mul_of_nonneg_left h2 hb
  exact_mod_cast (by linarith : r ≤ a * μ + b * ν)

/-! #### Theorem 5.5: pointwise suprema -/

/-- **Rockafellar, Theorem 5.5.** The pointwise supremum of an arbitrary collection of convex
functions is convex.

The index is a `Sort*`, so the empty family is allowed: `⨆ i : Empty, f i x` is `⊥`, whose epigraph
is all of `E × ℝ`. -/
theorem convexFn_iSup {ι : Sort*} {f : ι → E → EReal} (h : ∀ i, ConvexFn (f i)) :
    ConvexFn (fun x => ⨆ i, f i x) := by
  refine ⟨?_⟩
  rw [epi_iSup]
  exact convex_iInter fun i => (h i).convex_epi

/-- **Rockafellar, Theorem 5.5**, for a family indexed by a set. -/
theorem convexFn_biSup {ι : Type*} {s : Set ι} {f : ι → E → EReal}
    (h : ∀ i ∈ s, ConvexFn (f i)) : ConvexFn (fun x => ⨆ i ∈ s, f i x) := by
  refine ⟨?_⟩
  rw [epi_biSup]
  exact convex_iInter₂ fun i hi => (h i hi).convex_epi

/-- **Rockafellar, Theorem 5.5**, binary case: the pointwise maximum of two convex functions is
convex. -/
theorem ConvexFn.sup {f g : E → EReal} (hf : ConvexFn f) (hg : ConvexFn g) : ConvexFn (f ⊔ g) := by
  refine ⟨?_⟩
  rw [epi_sup]
  exact hf.convex_epi.inter hg.convex_epi

/-! #### Theorem 5.2: sums -/

/-- **Rockafellar, Theorem 5.2.** The sum of two convex functions neither of which takes the value
`⊥` is convex.

`∀ x, f x ≠ ⊥` is the half of Rockafellar's properness hypothesis that does the work — it is what
prevents `∞ - ∞` — and it cannot be dropped; see the module docstring for a counterexample. -/
theorem ConvexFn.add {f g : E → EReal} (hf : ConvexFn f) (hg : ConvexFn g)
    (hf' : ∀ x, f x ≠ ⊥) (hg' : ∀ x, g x ≠ ⊥) : ConvexFn (f + g) := by
  refine convexFn_of_epi_combo (fun x y μ ν hx hy a b ha hb hab => ?_)
  have hx' : f x + g x ≤ (μ : EReal) := hx
  have hy' : f y + g y ≤ (ν : EReal) := hy
  -- neither summand can be `⊤`, so all four values are real
  have hxt : f x ≠ ⊤ ∧ g x ≠ ⊤ :=
    (_root_.EReal.add_ne_top_iff_ne_top₂ (hf' x) (hg' x)).1
      (hx'.trans_lt (_root_.EReal.coe_lt_top μ)).ne
  have hyt : f y ≠ ⊤ ∧ g y ≠ ⊤ :=
    (_root_.EReal.add_ne_top_iff_ne_top₂ (hf' y) (hg' y)).1
      (hy'.trans_lt (_root_.EReal.coe_lt_top ν)).ne
  obtain ⟨p₁, hp₁⟩ :=
    Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf' x) (lt_top_iff_ne_top.2 hxt.1)
  obtain ⟨p₂, hp₂⟩ :=
    Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hg' x) (lt_top_iff_ne_top.2 hxt.2)
  obtain ⟨q₁, hq₁⟩ :=
    Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf' y) (lt_top_iff_ne_top.2 hyt.1)
  obtain ⟨q₂, hq₂⟩ :=
    Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hg' y) (lt_top_iff_ne_top.2 hyt.2)
  rw [hp₁, hp₂, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at hx'
  rw [hq₁, hq₂, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at hy'
  have hfc := hf.epi_combo hp₁.le hq₁.le ha hb hab
  have hgc := hg.epi_combo hp₂.le hq₂.le ha hb hab
  have hsum := add_le_add hfc hgc
  rw [← _root_.EReal.coe_add] at hsum
  refine hsum.trans ?_
  have h1 : a * (p₁ + p₂) ≤ a * μ := mul_le_mul_of_nonneg_left hx' ha
  have h2 : b * (q₁ + q₂) ≤ b * ν := mul_le_mul_of_nonneg_left hy' hb
  have h3 : a * p₁ + b * q₁ + (a * p₂ + b * q₂) = a * (p₁ + p₂) + b * (q₁ + q₂) := by ring
  exact_mod_cast (by linarith : a * p₁ + b * q₁ + (a * p₂ + b * q₂) ≤ a * μ + b * ν)

/-- **Rockafellar, Theorem 5.2**, for a finite sum: "a linear combination
`λ₁ f₁ + ⋯ + λₘ fₘ` of proper convex functions with non-negative coefficients is convex". -/
theorem ConvexFn.sum {ι : Type*} {s : Finset ι} {f : ι → E → EReal}
    (hf : ∀ i ∈ s, ConvexFn (f i)) (hf' : ∀ i ∈ s, ∀ x, f i x ≠ ⊥) :
    ConvexFn (fun x => ∑ i ∈ s, f i x) := by
  induction s using Finset.cons_induction with
  | empty => simpa using convexFn_const (E := E) 0
  | cons i t hi ih =>
    have key : ConvexFn (f i + fun x => ∑ j ∈ t, f j x) :=
      (hf i (by simp)).add
        (ih (fun j hj => hf j (by simp [hj])) (fun j hj => hf' j (by simp [hj])))
        (hf' i (by simp))
        (fun x => Tdaf.EReal.sum_ne_bot fun j hj => hf' j (by simp [hj]) x)
    have hfun : (fun x => ∑ j ∈ Finset.cons i t hi, f j x) = (f i + fun x => ∑ j ∈ t, f j x) := by
      funext x; simp [Finset.sum_cons]
    rw [hfun]
    exact key

/-! #### Multiplication by a nonnegative scalar -/

/-- Multiplying a convex function by a nonnegative real preserves convexity (Rockafellar §5).

The case `a = 0` is not vacuous but is still true: `EReal` obeys Rockafellar's convention
`0 · ∞ = 0`, so `(0 : EReal) * f` is the zero function, which is convex. -/
theorem ConvexFn.smul {f : E → EReal} (a : ℝ) (ha : 0 ≤ a) (hf : ConvexFn f) :
    ConvexFn (fun x => (a : EReal) * f x) := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simpa using convexFn_const (E := E) 0
  refine convexFn_of_epi_combo (fun x y μ ν hx hy c d hc hd hcd => ?_)
  have hx' : f x ≤ ((μ / a : ℝ) : EReal) := (Tdaf.EReal.coe_mul_le_coe_iff ha').1 hx
  have hy' : f y ≤ ((ν / a : ℝ) : EReal) := (Tdaf.EReal.coe_mul_le_coe_iff ha').1 hy
  refine (Tdaf.EReal.coe_mul_le_coe_iff ha').2 ?_
  have hcombo := hf.epi_combo hx' hy' hc hd hcd
  have harith : c * (μ / a) + d * (ν / a) = (c * μ + d * ν) / a := by ring
  rwa [harith] at hcombo

/-! #### Theorem 5.1: composition with a nondecreasing convex function -/

/-- `φ : ℝ → EReal` extended to `EReal → EReal` by Rockafellar's convention `φ (+∞) = +∞`, and by
`φ (-∞) = -∞`, which is the choice that keeps the extension monotone.

Theorem 5.1 applies `φ` only to the values of a function into `(-∞, +∞]`, so the value at `⊥` is
immaterial to it. -/
noncomputable def extendTop (φ : ℝ → EReal) : EReal → EReal :=
  _root_.EReal.rec ⊥ φ ⊤

/-- On the reals, `extendTop φ` is `φ`. -/
@[simp] theorem extendTop_coe (φ : ℝ → EReal) (r : ℝ) : extendTop φ (r : EReal) = φ r := rfl

/-- Rockafellar's convention `φ (+∞) = +∞`. -/
@[simp] theorem extendTop_top (φ : ℝ → EReal) : extendTop φ ⊤ = ⊤ := rfl

/-- The value at `⊥`, chosen to keep the extension monotone; Theorem 5.1 never sees it. -/
@[simp] theorem extendTop_bot (φ : ℝ → EReal) : extendTop φ ⊥ = ⊥ := rfl

/-- The extension of a monotone `φ : ℝ → EReal` is monotone. -/
theorem monotone_extendTop {φ : ℝ → EReal} (h : Monotone φ) : Monotone (extendTop φ) := by
  intro z w hzw
  induction z with
  | bot => simp
  | top =>
    obtain rfl := top_le_iff.1 hzw
    exact le_rfl
  | coe r =>
    induction w with
    | bot => exact absurd hzw (by simp)
    | top => simp
    | coe s => exact h (by exact_mod_cast hzw)

/-- **Rockafellar, Theorem 5.1.** If `f : E → EReal` is convex and never `⊥` — that is, `f` maps
into `(-∞, +∞]` — and `φ : EReal → EReal` is monotone, convex on `ℝ`, and satisfies `φ ⊤ = ⊤`, then
`x ↦ φ (f x)` is convex.

See the module docstring for why these three hypotheses on `φ` replace "convex nondecreasing
`φ : ℝ → (-∞, +∞]`, extended by `φ (+∞) = +∞`", and why `φ ⊤ = ⊤` cannot be dropped. -/
theorem ConvexFn.comp {f : E → EReal} {φ : EReal → EReal} (hf : ConvexFn f)
    (hf' : ∀ x, f x ≠ ⊥) (hφ : ConvexFn fun r : ℝ => φ (r : EReal)) (hmono : Monotone φ)
    (htop : φ ⊤ = ⊤) : ConvexFn (fun x => φ (f x)) := by
  refine convexFn_of_epi_combo (fun x y μ ν hx hy a b ha hb hab => ?_)
  have hx' : φ (f x) ≤ (μ : EReal) := hx
  have hy' : φ (f y) ≤ (ν : EReal) := hy
  -- `f` cannot be `⊤` where `φ ∘ f` is bounded above by a real, because `φ ⊤ = ⊤`
  have hfx : f x < ⊤ := by
    rcases eq_top_or_lt_top (f x) with h | h
    · rw [h, htop] at hx'
      exact absurd hx' (not_le.2 (_root_.EReal.coe_lt_top μ))
    · exact h
  have hfy : f y < ⊤ := by
    rcases eq_top_or_lt_top (f y) with h | h
    · rw [h, htop] at hy'
      exact absurd hy' (not_le.2 (_root_.EReal.coe_lt_top ν))
    · exact h
  obtain ⟨p, hp⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf' x) hfx
  obtain ⟨q, hq⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf' y) hfy
  rw [hp] at hx'
  rw [hq] at hy'
  have hcombo : f (a • x + b • y) ≤ ((a * p + b * q : ℝ) : EReal) :=
    hf.epi_combo hp.le hq.le ha hb hab
  refine (hmono hcombo).trans ?_
  simpa [smul_eq_mul] using hφ.epi_combo hx' hy' ha hb hab

/-- **Rockafellar, Theorem 5.1**, in the book's own shape: `φ` is a nondecreasing convex function
of one real variable, and `h x = φ (f x)` with the convention `φ (+∞) = +∞`. -/
theorem ConvexFn.comp_extendTop {f : E → EReal} {φ : ℝ → EReal} (hf : ConvexFn f)
    (hf' : ∀ x, f x ≠ ⊥) (hφ : ConvexFn φ) (hmono : Monotone φ) :
    ConvexFn (fun x => extendTop φ (f x)) :=
  hf.comp hf' hφ (monotone_extendTop hmono) (extendTop_top φ)

/-! #### Restriction to a convex set -/

/-- Restricting a convex function to a convex set gives a convex function (Rockafellar §5). -/
theorem ConvexFn.restrict {f : E → EReal} {s : Set E} (hf : ConvexFn f) (hs : Convex ℝ s) :
    ConvexFn (Tdaf.ConvexAnalysis.restrict s f) := by
  refine ⟨?_⟩
  rw [epi_restrict]
  exact hf.convex_epi.inter (hs.prod convex_univ)

/-- Rockafellar's remark after Theorem 5.2: "adding an indicator function to `f` amounts to
restricting the effective domain of `f`". Combined with `restrict_eq_add_indicatorFn`, this is
`ConvexFn.restrict` read as an instance of `ConvexFn.add`. -/
theorem ConvexFn.add_indicatorFn {f : E → EReal} {s : Set E} (hf : ConvexFn f)
    (hf' : ∀ x, f x ≠ ⊥) (hs : Convex ℝ s) : ConvexFn (f + indicatorFn s) := by
  rw [← restrict_eq_add_indicatorFn hf']
  exact hf.restrict hs

end Module

end Tdaf.ConvexAnalysis
