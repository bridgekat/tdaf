/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.Convex.Function
import Tdaf.Order.EReal

/-!
# Extended-real-valued convex functions

This file introduces the basic theory of convex functions `f : E → EReal` on a real vector space,
following Rockafellar, *Convex Analysis*, §4.

## Main definitions

* `Tdaf.epi f` — the epigraph of `f`, a subset of `E × ℝ`.
* `Tdaf.dom f` — the effective domain of `f`, where `f < ⊤`.
* `Tdaf.NeBotFn f` — `f` never takes the value `⊥`.
* `Tdaf.Proper f` — `f` is finite somewhere and never `⊥`.
* `Tdaf.restrict s f` — `f` restricted to `s`, extended by `⊤`.
* `Tdaf.ConvexFn f` — `f` is convex, meaning that `epi f` is a convex set.

## Main results

* `Tdaf.convexFn_iff_forall_lt` — Rockafellar's Theorem 4.2, the characterisation of convexity by
  strict inequalities. This is the form that avoids `∞ - ∞` entirely.
* `Tdaf.convexFn_iff_le` — Rockafellar's Theorem 4.1, the familiar inequality, valid when `f` never
  takes the value `⊥`.
* `Tdaf.ConvexFn.convex_lt`, `Tdaf.ConvexFn.convex_le`, `Tdaf.ConvexFn.convex_dom` — Theorem 4.6.
* `Tdaf.convexOn_iff_convexFn` — the bridge to Mathlib's `ConvexOn`.

## Design notes

Following Rockafellar, convexity is *defined* geometrically, as convexity of the epigraph, rather
than by the inequality `f (a • x + b • y) ≤ a * f x + b * f y`. The inequality is problematic as a
definition because `a * f x + b * f y` can be the undefined `∞ - ∞` when `f` takes both infinite
values, and Rockafellar admits such improper functions throughout: they arise naturally from proper
ones, and Part VII of the book depends on them.

Note also that the epigraph lives in `E × ℝ`, not `E × EReal`: the second coordinate ranges over
the *reals*. This differs from Mathlib's `ConvexOn.convex_epigraph`, which uses the codomain of the
function for the second coordinate. For `EReal`-valued functions the two are genuinely different
sets, so `Tdaf.epi` is a new definition rather than a specialisation.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §4.
-/

open Set

namespace Tdaf

/-! ### Epigraphs, domains, properness -/

section Basic

variable {E : Type*}

/-- The epigraph of `f : E → EReal`, as a subset of `E × ℝ`.

Rockafellar §4: `epi f = {(x, μ) | x ∈ E, μ ∈ ℝ, μ ≥ f x}`. The second coordinate ranges over the
*reals*, not over `EReal`. -/
def epi (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

@[simp]
theorem mem_epi {f : E → EReal} {p : E × ℝ} : p ∈ epi f ↔ f p.1 ≤ (p.2 : EReal) := Iff.rfl

theorem mk_mem_epi {f : E → EReal} {x : E} {μ : ℝ} : (x, μ) ∈ epi f ↔ f x ≤ (μ : EReal) := Iff.rfl

theorem epi_mono {f g : E → EReal} (h : f ≤ g) : epi g ⊆ epi f := fun _ hp => (h _).trans hp

/-- The epigraph determines the function: `f ≤ g` exactly when `epi g ⊆ epi f`. -/
theorem le_iff_epi_subset {f g : E → EReal} : f ≤ g ↔ epi g ⊆ epi f := by
  refine ⟨epi_mono, fun h x => ?_⟩
  by_contra hx
  obtain ⟨q, hgq, hqf⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hx)
  exact absurd (h (show (x, q) ∈ epi g from hgq.le)) (not_le.2 hqf)

/-- The effective domain of `f`: the set where `f < ⊤`.

Rockafellar §4: `dom f` is the projection of `epi f` on `E`. -/
def dom (f : E → EReal) : Set E := {x | f x < ⊤}

@[simp] theorem mem_dom {f : E → EReal} {x : E} : x ∈ dom f ↔ f x < ⊤ := Iff.rfl

/-- `f` never takes the value `⊥`, i.e. `f` maps into `(-∞, +∞]`.

This is the standing hypothesis under which Rockafellar's arithmetic of convex functions is
unambiguous: it is exactly what rules out the forbidden `∞ - ∞`. It is bundled as a named
predicate rather than spelled out as `∀ x, f x ≠ ⊥` at every use site. -/
structure NeBotFn (f : E → EReal) : Prop where
  /-- `f` never takes the value `⊥`. -/
  ne_bot : ∀ x, f x ≠ ⊥

theorem NeBotFn.bot_lt {f : E → EReal} (hf : NeBotFn f) (x : E) : ⊥ < f x :=
  bot_lt_iff_ne_bot.2 (hf.ne_bot x)

theorem NeBotFn.mono {f g : E → EReal} (hf : NeBotFn f) (h : f ≤ g) : NeBotFn g :=
  ⟨fun x => bot_lt_iff_ne_bot.1 ((hf.bot_lt x).trans_le (h x))⟩

/-- `f` is *proper* when it is finite somewhere and never takes the value `⊥`.

Rockafellar §4: equivalently, `epi f` is nonempty and contains no vertical lines. -/
structure Proper (f : E → EReal) : Prop extends NeBotFn f where
  /-- `f` is not identically `⊤`. -/
  dom_nonempty : (dom f).Nonempty

/-- `f` restricted to `s` and extended by `⊤` off `s`.

This encoding of "a convex function given on a convex set" recurs constantly; Rockafellar adopts it
as the standing convention in §4. The `⨅` formulation avoids a decidability hypothesis; see
`Tdaf.restrict_of_mem` and `Tdaf.restrict_of_notMem` for the defining equations. -/
noncomputable def restrict (s : Set E) (f : E → EReal) : E → EReal := fun x => ⨅ _ : x ∈ s, f x

@[simp] theorem restrict_of_mem {s : Set E} {f : E → EReal} {x : E} (hx : x ∈ s) :
    restrict s f x = f x := iInf_pos hx

@[simp] theorem restrict_of_notMem {s : Set E} {f : E → EReal} {x : E} (hx : x ∉ s) :
    restrict s f x = ⊤ := iInf_neg hx

end Basic

/-! ### Convex functions -/

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A function `f : E → EReal` is convex when its epigraph is a convex subset of `E × ℝ`.

This is Rockafellar's definition (§4). See `Tdaf.convexFn_iff_forall_lt` (Theorem 4.2) and
`Tdaf.convexFn_iff_le` (Theorem 4.1) for the analytic characterisations. -/
structure ConvexFn (f : E → EReal) : Prop where
  /-- The epigraph of a convex function is convex. -/
  convex_epi : Convex ℝ (epi f)

@[simp] theorem convexFn_iff_convex_epi {f : E → EReal} : ConvexFn f ↔ Convex ℝ (epi f) :=
  ⟨fun h => h.convex_epi, fun h => ⟨h⟩⟩

/-- A convex-combination goal in which one coefficient may vanish reduces to the case where both
coefficients are positive. -/
theorem combo_of_pos {P : E → Prop} {x y : E} {a b : ℝ} (hx : P x) (hy : P y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (h : 0 < a → 0 < b → P (a • x + b • y)) :
    P (a • x + b • y) := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; simpa using hy
  rcases eq_or_lt_of_le hb with rfl | hb'
  · have ha1 : a = 1 := by linarith
    subst ha1; simpa using hx
  exact h ha' hb'

/-- The defining property of convexity, in the form in which it is used: a convex combination of
two points of the epigraph lies in the epigraph. -/
theorem ConvexFn.epi_combo {f : E → EReal} (hf : ConvexFn f) {x y : E} {μ ν : ℝ}
    (hx : f x ≤ (μ : EReal)) (hy : f y ≤ (ν : EReal)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : f (a • x + b • y) ≤ ((a * μ + b * ν : ℝ) : EReal) :=
  hf.convex_epi (show (x, μ) ∈ epi f from hx) (show (y, ν) ∈ epi f from hy) ha hb hab

/-- Conversely, the combination property characterises convexity. -/
theorem convexFn_of_epi_combo {f : E → EReal}
    (h : ∀ (x y : E) (μ ν : ℝ), f x ≤ (μ : EReal) → f y ≤ (ν : EReal) →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ ((a * μ + b * ν : ℝ) : EReal)) :
    ConvexFn f := by
  refine ⟨?_⟩
  rintro ⟨x, μ⟩ hx ⟨y, ν⟩ hy a b ha hb hab
  exact h x y μ ν hx hy a b ha hb hab

/-! ### Theorem 4.2 -/

/-- **Rockafellar, Theorem 4.2.** A function `f : E → EReal` is convex if and only if
`f ((1 - λ) x + λ y) < (1 - λ) α + λ β` whenever `f x < α` and `f y < β` and `0 < λ < 1`.

This characterisation is stated with strict inequalities precisely so that the forbidden expression
`∞ - ∞` never arises: `α` and `β` range over the reals. -/
theorem convexFn_iff_forall_lt (f : E → EReal) :
    ConvexFn f ↔ ∀ (x y : E) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      ∀ α β : ℝ, f x < (α : EReal) → f y < (β : EReal) →
        f (a • x + b • y) < ((a * α + b * β : ℝ) : EReal) := by
  constructor
  · intro hf x y a b ha hb hab α β hx hy
    obtain ⟨α', hxα', hα'⟩ := Tdaf.EReal.exists_real_btwn_of_lt_coe hx
    obtain ⟨β', hyβ', hβ'⟩ := Tdaf.EReal.exists_real_btwn_of_lt_coe hy
    refine lt_of_le_of_lt (hf.epi_combo hxα'.le hyβ'.le ha.le hb.le hab) ?_
    exact_mod_cast add_lt_add (by nlinarith) (by nlinarith)
  · intro h
    refine convexFn_of_epi_combo (fun x y μ ν hx hy a b ha hb hab => ?_)
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy
    rcases eq_or_lt_of_le hb with rfl | hb'
    · have ha1 : a = 1 := by linarith
      subst ha1; simpa using hx
    · refine Tdaf.EReal.le_coe_of_forall_lt (fun q hq => ?_)
      have hx' : f x < ((μ + (q - (a * μ + b * ν)) : ℝ) : EReal) :=
        lt_of_le_of_lt hx (by exact_mod_cast (by linarith : μ < μ + (q - (a * μ + b * ν))))
      have hy' : f y < ((ν + (q - (a * μ + b * ν)) : ℝ) : EReal) :=
        lt_of_le_of_lt hy (by exact_mod_cast (by linarith : ν < ν + (q - (a * μ + b * ν))))
      have key := h x y a b ha' hb' hab _ _ hx' hy'
      have harith : a * (μ + (q - (a * μ + b * ν))) + b * (ν + (q - (a * μ + b * ν))) = q := by
        linear_combination (q - (a * μ + b * ν)) * hab
      rwa [harith] at key

/-! ### Theorem 4.1 -/

/-- **Rockafellar, Theorem 4.1.** For a function `f` that never takes the value `⊥` — equivalently,
a function into `(-∞, +∞]` — convexity is the familiar inequality. -/
theorem convexFn_iff_le {f : E → EReal} (hf : NeBotFn f) :
    ConvexFn f ↔ ∀ (x y : E) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y := by
  rw [convexFn_iff_forall_lt]
  have hacoe : ∀ {c : ℝ}, 0 < c → (0 : EReal) < (c : EReal) := fun hc => by exact_mod_cast hc
  constructor
  · intro h x y a b ha hb hab
    rcases eq_top_or_lt_top (f x) with hx | hx
    · rw [hx, EReal.mul_top_of_pos (hacoe ha)]
      rcases eq_top_or_lt_top (f y) with hy | hy
      · rw [hy, EReal.mul_top_of_pos (hacoe hb), EReal.top_add_top]; exact le_top
      · obtain ⟨q, hq⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.ne_bot y) hy
        rw [hq, Tdaf.EReal.coe_mul_coe, EReal.top_add_coe]; exact le_top
    obtain ⟨p, hp⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.ne_bot x) hx
    rcases eq_top_or_lt_top (f y) with hy | hy
    · rw [hy, EReal.mul_top_of_pos (hacoe hb), hp, Tdaf.EReal.coe_mul_coe, EReal.coe_add_top]
      exact le_top
    obtain ⟨q, hq⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.ne_bot y) hy
    rw [hp, hq, Tdaf.EReal.coe_mul_coe, Tdaf.EReal.coe_mul_coe, ← EReal.coe_add]
    refine Tdaf.EReal.le_coe_of_forall_lt (fun r hr => ?_)
    have hx' : f x < ((p + (r - (a * p + b * q)) : ℝ) : EReal) := by
      rw [hp]; exact_mod_cast (by linarith : p < p + (r - (a * p + b * q)))
    have hy' : f y < ((q + (r - (a * p + b * q)) : ℝ) : EReal) := by
      rw [hq]; exact_mod_cast (by linarith : q < q + (r - (a * p + b * q)))
    have key := h x y a b ha hb hab _ _ hx' hy'
    have harith : a * (p + (r - (a * p + b * q))) + b * (q + (r - (a * p + b * q))) = r := by
      linear_combination (r - (a * p + b * q)) * hab
    rwa [harith] at key
  · intro h x y a b ha hb hab α β hx hy
    obtain ⟨p, hp⟩ :=
      Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.ne_bot x) (hx.trans (EReal.coe_lt_top α))
    obtain ⟨q, hq⟩ :=
      Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.ne_bot y) (hy.trans (EReal.coe_lt_top β))
    refine lt_of_le_of_lt (h x y a b ha hb hab) ?_
    rw [hp, hq, Tdaf.EReal.coe_mul_coe, Tdaf.EReal.coe_mul_coe, ← EReal.coe_add]
    rw [hp] at hx; rw [hq] at hy
    have hpα : p < α := by exact_mod_cast hx
    have hqβ : q < β := by exact_mod_cast hy
    exact_mod_cast (by nlinarith : a * p + b * q < a * α + b * β)

/-! ### Level sets and the effective domain: Theorem 4.6 -/

/-- **Rockafellar, Theorem 4.6** (strict form). Strict sublevel sets of a convex function are
convex. -/
theorem ConvexFn.convex_lt {f : E → EReal} (hf : ConvexFn f) (α : EReal) :
    Convex ℝ {x | f x < α} := by
  intro x hx y hy a b ha hb hab
  refine combo_of_pos (P := fun z => z ∈ {x | f x < α}) hx hy ha hb hab (fun ha' hb' => ?_)
  have hx' : f x < α := hx
  have hy' : f y < α := hy
  change f (a • x + b • y) < α
  obtain ⟨p, hxp, hpα⟩ := EReal.lt_iff_exists_real_btwn.1 hx'
  obtain ⟨q, hyq, hqα⟩ := EReal.lt_iff_exists_real_btwn.1 hy'
  refine lt_of_le_of_lt (hf.epi_combo hxp.le hyq.le ha'.le hb'.le hab) ?_
  induction α with
  | bot => exact absurd hpα (by simp)
  | top => exact EReal.coe_lt_top _
  | coe r =>
    have hp : p < r := by exact_mod_cast hpα
    have hq : q < r := by exact_mod_cast hqα
    have h1 : a * p < a * r := mul_lt_mul_of_pos_left hp ha'
    have h2 : b * q < b * r := mul_lt_mul_of_pos_left hq hb'
    have h3 : a * r + b * r = r := by linear_combination r * hab
    exact_mod_cast (by linarith : a * p + b * q < r)

/-- **Rockafellar, Theorem 4.6** (non-strict form). Sublevel sets of a convex function are
convex. -/
theorem ConvexFn.convex_le {f : E → EReal} (hf : ConvexFn f) (α : EReal) :
    Convex ℝ {x | f x ≤ α} := by
  intro x hx y hy a b ha hb hab
  refine combo_of_pos (P := fun z => z ∈ {x | f x ≤ α}) hx hy ha hb hab (fun ha' hb' => ?_)
  have hx' : f x ≤ α := hx
  have hy' : f y ≤ α := hy
  change f (a • x + b • y) ≤ α
  induction α with
  | bot =>
    refine le_of_eq (Tdaf.EReal.eq_bot_of_forall_le_coe (fun r => ?_))
    have := hf.epi_combo (μ := r) (ν := r) (hx'.trans bot_le) (hy'.trans bot_le) ha'.le hb'.le hab
    refine this.trans (le_of_eq ?_)
    exact_mod_cast (by linear_combination r * hab : a * r + b * r = r)
  | top => exact le_top
  | coe r =>
    have := hf.epi_combo hx' hy' ha'.le hb'.le hab
    refine this.trans (le_of_eq ?_)
    exact_mod_cast (by linear_combination r * hab : a * r + b * r = r)

/-- The effective domain of a convex function is convex (Rockafellar §4). -/
theorem ConvexFn.convex_dom {f : E → EReal} (hf : ConvexFn f) : Convex ℝ (dom f) :=
  hf.convex_lt ⊤

/-! ### The bridge to Mathlib's `ConvexOn` -/

omit [AddCommGroup E] [Module ℝ E] in
theorem epi_restrict_coe (s : Set E) (g : E → ℝ) :
    epi (restrict s fun x => (g x : EReal)) = {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} := by
  ext p
  by_cases hp : p.1 ∈ s <;> simp [epi, hp]

/-- Mathlib's `ConvexOn` for a real-valued function on a set agrees with `ConvexFn` for its
extension by `⊤`. This is the interface through which the surface layer reuses Mathlib. -/
theorem convexOn_iff_convexFn (s : Set E) (g : E → ℝ) :
    ConvexOn ℝ s g ↔ ConvexFn (restrict s fun x => (g x : EReal)) := by
  rw [convexFn_iff_convex_epi, epi_restrict_coe]
  exact ⟨fun h => h.convex_epigraph, fun h => convexOn_of_convex_epigraph h⟩

end Module

end Tdaf
