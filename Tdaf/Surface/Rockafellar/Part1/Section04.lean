/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Convex.Deriv
import Tdaf.Analysis.Convex.Homogeneous
import Tdaf.Analysis.Convex.Saddle.Differential
import Tdaf.Analysis.Convex.Subgradient.Gradient
import Tdaf.Surface.Common.Euclidean

/-!
# Rockafellar, *Convex Analysis*, §4: Convex Functions

The eleven numbered results of §4 (book lines 1039–1438, pp. 23–31), stated in the book's own
terms over `Rn n = ℝⁿ` and closed by the backbone.

Rockafellar's "convex function" is a function `Rn n → EReal` defined on **all** of `ℝⁿ`, convex by
definition when its epigraph is convex. That is `Tdaf.ConvexAnalysis.ConvexFn` exactly. Only
Theorems 4.4 and 4.5 are about finite functions, because only they are about `C²` functions on an
interval and on an open convex set; everywhere else a hypothesis `f : Rn n → ℝ` would be a
mistranslation. Properness is imposed only where the book imposes it: Corollaries 4.7.1 and 4.7.2
and Theorem 4.8.

## Main results

* `theorem_4_1` — convexity is the secant inequality, for `f` with values in `(-∞, +∞]`.
* `theorem_4_2` — convexity by strict inequalities; the form valid for **all** `EReal` values.
* `theorem_4_3` — **Jensen's inequality**: convexity is the finite-convex-combination inequality.
* `theorem_4_4` — a `C²` function on an open interval is convex iff `f'' ≥ 0`.
* `theorem_4_5` — a `C²` function on an open convex `C ⊆ ℝⁿ` is convex iff its Hessian is
  positive semi-definite at every point of `C`.
* `theorem_4_6` — the level sets `{x | f x < α}` and `{x | f x ≤ α}` of a convex function are
  convex.
* `corollary_4_6_1` — a system of convex inequalities has a convex solution set.
* `theorem_4_7` — a positively homogeneous function is convex iff it is subadditive.
* `corollary_4_7_1`, `corollary_4_7_2` — subadditivity for positive combinations, and
  `f (-x) ≥ -f x`.
* `theorem_4_8` — a positively homogeneous proper convex `f` is linear on a subspace `L` iff
  `f (-x) = -f x` on `L`; `theorem_4_8_basis` is the book's final sentence, that checking a
  spanning set suffices.

## The extended arithmetic of §4

The conventions Rockafellar lays down on pp. 24–25 are the content of this section, not
boilerplate. How each is realised here:

* **`0 · ∞ = 0`.** Mathlib's `EReal` multiplication satisfies `zero_mul`, so this holds on the
  nose. `theorem_4_3` **depends on it**: the book's right-hand side `λ₁ f x₁ + ⋯ + λₘ f xₘ` is
  well defined at an index with `λᵢ = 0` and `f xᵢ = +∞` only because that term is `0`. The proof
  discards exactly those indices, and the discarded terms must vanish for the two sides to match.
* **`inf ∅ = +∞`.** This is what `Tdaf.ConvexAnalysis.restrict`, `⨅ _ : x ∈ s, f x`, computes off
  `s`: an infimum over an empty `Prop` is `⊤`. `theorem_4_1` is stated through `restrict`, which
  is the book's own device for "a convex function given on a convex set `C`" extended by `+∞`.
* **`∞ − ∞` deliberately undefined.** Mathlib's `EReal` *totalises* it: `x + ⊥ = ⊥` and
  `⊥ + x = ⊥`, so `(+∞) + (−∞) = −∞` there, which is **not** Rockafellar's convention. Nothing
  below relies on that totalisation. Every statement whose right-hand side could produce the
  combination carries the book's own hypothesis `∀ x, f x ≠ ⊥` — that is, `f` has values in
  `(-∞, +∞]` — so the value of `⊤ + ⊥` is never consulted: `theorem_4_1`, `theorem_4_3`,
  `theorem_4_7`, `corollary_4_7_1`, `corollary_4_7_2`, `theorem_4_8`. `theorem_4_2` is the one
  characterisation stated for the full range `[-∞, +∞]`, and it is stated with strict inequalities
  between *reals* precisely so that no infinite sum ever appears. `theorem_4_6` and
  `corollary_4_6_1` need no such hypothesis: they are about level sets, where no sum occurs.

## What is not here

* **The unnumbered claims of §4** are already in the backbone under descriptive names and are not
  restated: `ConvexFn.convex_dom` (`dom f` is convex, book line 1051), `convexFn_indicatorFn`
  (`C` is convex iff `δ(·|C)` is convex, 1300), `epi_indicatorFn` (the epigraph of an indicator is
  a half-cylinder, 1300), and `posHomogeneous_iff_isCone_epi` (positive homogeneity is the
  epigraph being a cone, 1391). Restating them here would duplicate a one-line alias and risk
  name collisions with the sibling section modules.
* **The worked examples of book lines 1211–1290** — `e^{αx}`, `xᵖ`, `−log x`, `(α² − x²)^{-1/2}`,
  the negative geometric mean, the Euclidean norm — are *deferred by scope*. `part1.md` schedules
  the whole §4–§5 example corpus as a separate harvest by line range, since none of it is
  numbered.
* **The support function `δ*(·|C)`, the gauge `γ(·|C)` and the distance `d(·, C)`** are *defined*
  in §4 (lines 1310–1318) but the book explicitly postpones their convexity to §5, so they are
  deferred to `Section05`.
* **Theorem 4.5's Hessian as a matrix.** The book names the matrix `Q_x = (q_ij x)` with
  `q_ij = ∂²f/∂ξᵢ∂ξⱼ` and then defines positive semi-definiteness as `⟨z, Q_x z⟩ ≥ 0` for every
  `z`. `theorem_4_5` states that condition in the coordinate-free form
  `0 ≤ fderiv ℝ (fderiv ℝ f) x z z`, which is the same quadratic form. The bridge to the matrix of
  second partial derivatives in the standard basis of `Rn n` is *omitted*: it is pure coordinate
  bookkeeping, not §4's content.

## Backbone gaps patched locally

The `private` lemmas in the `Lines` section are **not** surface material. They are the missing
convex half of the reduction to lines (remediation item 4.9 — the concave half already exists as
`Tdaf.ConvexAnalysis.concaveOn_comp_line`, and the convex forward half as `convexOn_comp_line`),
together with the second-derivative-along-a-line computation that Rockafellar's proof of
Theorem 4.5 calls "a straightforward calculation". Both belong in the backbone. They are `private`
so that no surface statement outside this file can come to depend on them.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §4.
-/

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

/-! ### Theorem 4.1 -/

/-- **Rockafellar, Theorem 4.1.** Let `f` be a function from `C` to `(-∞, +∞]`, where `C` is a
convex set (for example `C = ℝⁿ`). Then `f` is convex on `C` if and only if

`f ((1 − λ) x + λ y) ≤ (1 − λ) f x + λ f y`,  `0 < λ < 1`,

for every `x` and `y` in `C`.

"`f` is convex on `C`" is `ConvexFn (restrict C f)`: the book's own convention (line 1047) is that
a convex function given on `C` is extended to all of `ℝⁿ` by `+∞`, and `restrict` is that
extension. The hypothesis `∀ x, f x ≠ ⊥` is the book's "values in `(-∞, +∞]`", which is exactly
what keeps the right-hand side from being the forbidden `∞ − ∞`.

Specialises `convexFn_iff_le`, whose statement is the `C = ℝⁿ` case; the passage between the two
is the only content added here. -/
theorem theorem_4_1 {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) {f : Rn n → EReal}
    (hbot : ∀ x, f x ≠ ⊥) :
    ConvexFn (restrict C f) ↔ ∀ x ∈ C, ∀ y ∈ C, ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y := by
  have hrb : ∀ x, restrict C f x ≠ ⊥ := by
    intro x
    by_cases hx : x ∈ C <;> simp [hx, hbot x]
  rw [convexFn_iff_le hrb]
  constructor
  · intro h x hx y hy a b ha hb hab
    have hmem : a • x + b • y ∈ C := hC hx hy ha.le hb.le hab
    have hkey := h x y a b ha hb hab
    rwa [restrict_of_mem hx, restrict_of_mem hy, restrict_of_mem hmem] at hkey
  · intro h x y a b ha hb hab
    by_cases hx : x ∈ C
    · by_cases hy : y ∈ C
      · have hmem : a • x + b • y ∈ C := hC hx hy ha.le hb.le hab
        rw [restrict_of_mem hx, restrict_of_mem hy, restrict_of_mem hmem]
        exact h x hx y hy a b ha hb hab
      · rw [restrict_of_notMem hy, EReal.coe_mul_top_of_pos hb,
          EReal.add_top_of_ne_bot (Tdaf.EReal.coe_mul_ne_bot ha.le (hrb x))]
        exact le_top
    · rw [restrict_of_notMem hx, EReal.coe_mul_top_of_pos ha,
        EReal.top_add_of_ne_bot (Tdaf.EReal.coe_mul_ne_bot hb.le (hrb y))]
      exact le_top

/-! ### Theorem 4.2 -/

/-- **Rockafellar, Theorem 4.2.** Let `f` be a function from `ℝⁿ` to `[-∞, +∞]`. Then `f` is
convex if and only if

`f ((1 − λ) x + λ y) < (1 − λ) α + λ β`,  `0 < λ < 1`,

whenever `f x < α` and `f y < β`.

This is the characterisation that survives for functions taking **both** infinite values, which is
why Rockafellar remarks (line 1155) that it, and not Theorem 4.1's inequality, could serve as the
definition in general. `α` and `β` are reals, so no infinite sum is formed.

Specialises `convexFn_iff_forall_lt`. -/
theorem theorem_4_2 {n : ℕ} (f : Rn n → EReal) :
    ConvexFn f ↔ ∀ (x y : Rn n) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      ∀ α β : ℝ, f x < (α : EReal) → f y < (β : EReal) →
        f (a • x + b • y) < ((a * α + b * β : ℝ) : EReal) :=
  convexFn_iff_forall_lt f

/-! ### Theorem 4.3 -/

/-- **Rockafellar, Theorem 4.3 (Jensen's Inequality).** Let `f` be a function from `ℝⁿ` to
`(-∞, +∞]`. Then `f` is convex if and only if

`f (λ₁ x₁ + ⋯ + λₘ xₘ) ≤ λ₁ f x₁ + ⋯ + λₘ f xₘ`

whenever `λ₁ ≥ 0, …, λₘ ≥ 0` and `λ₁ + ⋯ + λₘ = 1`.

The book's proof is "An elementary exercise."

The right-hand side is an `EReal` sum, and it is well formed only under the convention `0 · ∞ = 0`
(book line 1075): an index with `λᵢ = 0` and `f xᵢ = +∞` contributes `0`, not `∞`. Accordingly the
proof restricts to the indices with `λᵢ ≠ 0`, and it is `zero_mul` on `EReal` that makes the
restricted sum equal the whole one.

Specialises `ConvexFn.sum_le` — aliased in the backbone as `jensen` — in one direction and
`convexFn_iff_le` in the other. `ConvexFn.sum_le` bounds the combination by a combination of
*real* upper bounds `mᵢ ≥ f xᵢ`; producing the book's `EReal` right-hand side from it is the work
below. -/
theorem theorem_4_3 {n : ℕ} {f : Rn n → EReal} (hbot : ∀ x, f x ≠ ⊥) :
    ConvexFn f ↔ ∀ (m : ℕ) (l : Fin m → ℝ) (x : Fin m → Rn n), (∀ i, 0 ≤ l i) →
      ∑ i, l i = 1 → f (∑ i, l i • x i) ≤ ∑ i, (l i : EReal) * f (x i) := by
  classical
  constructor
  · intro hconv m l x hl hl1
    set t : Finset (Fin m) := Finset.univ.filter fun i => l i ≠ 0 with ht
    have hzero : ∀ i ∈ (Finset.univ : Finset (Fin m)), i ∉ t → l i = 0 := by
      intro i _ hi
      simpa [ht] using hi
    have hsub : t ⊆ (Finset.univ : Finset (Fin m)) := Finset.filter_subset _ _
    have hsx : ∑ i ∈ t, l i • x i = ∑ i, l i • x i :=
      Finset.sum_subset hsub fun i hi hi' => by rw [hzero i hi hi', zero_smul]
    have hsf : ∑ i ∈ t, (l i : EReal) * f (x i) = ∑ i, (l i : EReal) * f (x i) :=
      Finset.sum_subset hsub fun i hi hi' => by
        rw [hzero i hi hi', EReal.coe_zero, zero_mul]
    have hs1 : ∑ i ∈ t, l i = 1 :=
      (Finset.sum_subset hsub fun i hi hi' => hzero i hi hi').trans hl1
    rw [← hsx, ← hsf]
    by_cases htop : ∑ i ∈ t, (l i : EReal) * f (x i) = ⊤
    · rw [htop]; exact le_top
    have hnb : ∀ i ∈ t, (l i : EReal) * f (x i) ≠ ⊥ :=
      fun i _ => Tdaf.EReal.coe_mul_ne_bot (hl i) (hbot (x i))
    have hnt := Tdaf.EReal.forall_ne_top_of_sum_ne_top t _ hnb htop
    have hfin : ∀ i ∈ t, f (x i) = ((f (x i)).toReal : EReal) := by
      intro i hi
      have hli : 0 < l i := lt_of_le_of_ne (hl i) (Ne.symm (by simpa [ht] using hi))
      refine (EReal.coe_toReal ?_ (hbot (x i))).symm
      intro hc
      exact hnt i hi (by rw [hc, EReal.coe_mul_top_of_pos hli])
    have key := hconv.sum_le t x (fun i => (f (x i)).toReal) l
      (fun i hi => le_of_eq (hfin i hi)) (fun i _ => hl i) hs1
    refine key.trans (le_of_eq ?_)
    rw [Tdaf.EReal.coe_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Tdaf.EReal.coe_mul_coe, ← hfin i hi]
  · intro h
    rw [convexFn_iff_le hbot]
    intro x y a b ha hb hab
    have key := h 2 ![a, b] ![x, y] (fun i => by fin_cases i <;> simp [ha.le, hb.le])
      (by simpa [Fin.sum_univ_two] using hab)
    simpa [Fin.sum_univ_two] using key

/-! ### Theorem 4.4 -/

/-- **Rockafellar, Theorem 4.4.** Let `f` be a twice continuously differentiable real-valued
function on an open interval `(α, β)`. Then `f` is convex if and only if its second derivative
`f''` is non-negative throughout `(α, β)`.

This is one of the two results of §4 that really is about a *finite* function, so `f : ℝ → ℝ` is
correct here and not a mistranslation. "Twice continuously differentiable on `(α, β)`" is
`ContDiffOn ℝ 2 f (Set.Ioo α β)`; since `Ioo α β` is open, `deriv` and `derivWithin` agree on it,
and the book's `f''` is `deriv (deriv f)`.

Mathlib supplies both halves: `convexOn_of_deriv2_nonneg'` is the book's integral argument, and
`ConvexOn.monotoneOn_deriv` with `MonotoneOn.derivWithin_nonneg` replaces the book's converse
("by continuity `f''` would be negative on a subinterval"), which is a contrapositive of the same
monotonicity fact. -/
theorem theorem_4_4 {α β : ℝ} {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo α β)) :
    ConvexOn ℝ (Set.Ioo α β) f ↔ ∀ x ∈ Set.Ioo α β, 0 ≤ deriv (deriv f) x := by
  have hd1 : DifferentiableOn ℝ f (Set.Ioo α β) := hf.differentiableOn (by norm_num)
  have hd2 : DifferentiableOn ℝ (deriv f) (Set.Ioo α β) :=
    (hf.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).differentiableOn (by norm_num)
  constructor
  · intro hconv x hx
    have hmono : MonotoneOn (deriv f) (Set.Ioo α β) :=
      hconv.monotoneOn_deriv fun y hy => (hd1 y hy).differentiableAt (isOpen_Ioo.mem_nhds hy)
    have h := hmono.derivWithin_nonneg (x := x)
    rwa [derivWithin_of_isOpen isOpen_Ioo hx] at h
  · intro h
    exact convexOn_of_deriv2_nonneg' (convex_Ioo α β) hd1 hd2 h

/-! ### Theorem 4.5

The `private` lemmas below are backbone gaps patched locally; see the module docstring. -/

section Lines

variable {n : ℕ}

/-- **Backbone gap (remediation 4.9).** The set of steps `t` with `y + t • z ∈ C` is convex when
`C` is. Needed for the converse half of the reduction to lines, which the backbone lacks. -/
private theorem convex_line_steps {C : Set (Rn n)} (hC : Convex ℝ C) (y z : Rn n) :
    Convex ℝ {t : ℝ | y + t • z ∈ C} := by
  intro t₁ h₁ t₂ h₂ a b ha hb hab
  have key : y + (a • t₁ + b • t₂) • z = a • (y + t₁ • z) + b • (y + t₂ • z) := by
    have hb' : a = 1 - b := by linarith
    subst hb'
    module
  change y + (a • t₁ + b • t₂) • z ∈ C
  rw [key]
  exact hC h₁ h₂ ha hb hab

/-- **Backbone gap (remediation 4.9).** Convexity of `f` on `C` is equivalent to convexity of the
restriction of `f` to each line, which is the first sentence of Rockafellar's proof of Theorem 4.5.
The forward half is the backbone's `convexOn_comp_line`; the converse is the missing half. -/
private theorem convexOn_iff_lines {C : Set (Rn n)} (hC : Convex ℝ C) (f : Rn n → ℝ) :
    ConvexOn ℝ C f ↔
      ∀ y ∈ C, ∀ z : Rn n, ConvexOn ℝ {t : ℝ | y + t • z ∈ C} fun t => f (y + t • z) := by
  refine ⟨fun h y _ z => convexOn_comp_line h y z, fun h => ⟨hC, ?_⟩⟩
  intro x hx y hy a b ha hb hab
  have h0 : (0 : ℝ) ∈ {t : ℝ | x + t • (y - x) ∈ C} := by simpa using hx
  have h1 : (1 : ℝ) ∈ {t : ℝ | x + t • (y - x) ∈ C} := by
    change x + (1 : ℝ) • (y - x) ∈ C
    simpa using hy
  have key : f (x + (a • (0 : ℝ) + b • (1 : ℝ)) • (y - x))
      ≤ a • f (x + (0 : ℝ) • (y - x)) + b • f (x + (1 : ℝ) • (y - x)) :=
    (h x hx (y - x)).2 h0 h1 ha hb hab
  have harith : x + (a • (0 : ℝ) + b • (1 : ℝ)) • (y - x) = a • x + b • y := by
    have hb' : a = 1 - b := by linarith
    subst hb'
    module
  rw [harith] at key
  simpa using key

variable {C : Set (Rn n)} {f : Rn n → ℝ} {y z : Rn n}

/-- **Backbone gap.** The steps that stay in an open `C` form an open set. -/
private theorem isOpen_line_steps (hCopen : IsOpen C) (y z : Rn n) :
    IsOpen {t : ℝ | y + t • z ∈ C} :=
  hCopen.preimage (continuous_const.add (continuous_id.smul continuous_const))

/-- **Backbone gap.** The line `t ↦ y + t • z` has derivative `z`. -/
private theorem hasDerivAt_line (y z : Rn n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => y + s • z) z t := by
  simpa using ((hasDerivAt_id t).smul_const z).const_add y

/-- **Backbone gap.** A `C²` function on an open set has an honest Fréchet derivative there. -/
private theorem hasFDerivAt_of_contDiffOn (hCopen : IsOpen C) (hf : ContDiffOn ℝ 2 f C) {u : Rn n}
    (hu : u ∈ C) : HasFDerivAt f (fderiv ℝ f u) u :=
  (((hf.differentiableOn (by norm_num)) u hu).differentiableAt
    (hCopen.mem_nhds hu)).hasFDerivAt

/-- **Backbone gap.** The derivative of a `C²` function is itself differentiable on the open
set. -/
private theorem hasFDerivAt_fderiv_of_contDiffOn (hCopen : IsOpen C) (hf : ContDiffOn ℝ 2 f C)
    {u : Rn n} (hu : u ∈ C) : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) u) u :=
  ((((hf.fderiv_of_isOpen (m := 1) hCopen (by norm_num)).differentiableOn
    (by norm_num)) u hu).differentiableAt (hCopen.mem_nhds hu)).hasFDerivAt

/-- **Backbone gap.** `g t = f (y + t • z)` has derivative `⟨∇f (y + t • z), z⟩`. -/
private theorem hasDerivAt_comp_line (hCopen : IsOpen C) (hf : ContDiffOn ℝ 2 f C) {t : ℝ}
    (ht : y + t • z ∈ C) :
    HasDerivAt (fun s : ℝ => f (y + s • z)) (fderiv ℝ f (y + t • z) z) t :=
  (hasFDerivAt_of_contDiffOn hCopen hf ht).comp_hasDerivAt t (hasDerivAt_line y z t)

/-- **Backbone gap.** Near a step that stays in `C`, `deriv g` is given by the formula above. -/
private theorem deriv_comp_line_eventuallyEq (hCopen : IsOpen C) (hf : ContDiffOn ℝ 2 f C) {t : ℝ}
    (ht : y + t • z ∈ C) :
    (deriv fun s : ℝ => f (y + s • z)) =ᶠ[nhds t] fun s : ℝ => fderiv ℝ f (y + s • z) z := by
  have hopen := isOpen_line_steps hCopen y z
  filter_upwards [hopen.mem_nhds (show t ∈ {t : ℝ | y + t • z ∈ C} from ht)] with s hs
  exact (hasDerivAt_comp_line hCopen hf hs).deriv

/-- **Backbone gap.** Rockafellar's "straightforward calculation": for `g t = f (y + t • z)`,
`g'' t = ⟨z, Q_x z⟩` with `x = y + t • z`, where `Q_x` is the second Fréchet derivative. -/
private theorem hasDerivAt_deriv_comp_line (hCopen : IsOpen C) (hf : ContDiffOn ℝ 2 f C) {t : ℝ}
    (ht : y + t • z ∈ C) :
    HasDerivAt (deriv fun s : ℝ => f (y + s • z))
      (fderiv ℝ (fderiv ℝ f) (y + t • z) z z) t := by
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ f (y + s • z))
      (fderiv ℝ (fderiv ℝ f) (y + t • z) z) t :=
    (hasFDerivAt_fderiv_of_contDiffOn hCopen hf ht).comp_hasDerivAt t (hasDerivAt_line y z t)
  have h2 : HasDerivAt (fun s : ℝ => (fderiv ℝ f (y + s • z)) z)
      (fderiv ℝ (fderiv ℝ f) (y + t • z) z z) t :=
    (ContinuousLinearMap.apply ℝ ℝ z).hasFDerivAt.comp_hasDerivAt t h1
  exact h2.congr_of_eventuallyEq (deriv_comp_line_eventuallyEq hCopen hf ht)

end Lines

/-- **Rockafellar, Theorem 4.5.** Let `f` be a twice continuously differentiable real-valued
function on an open convex set `C` in `ℝⁿ`. Then `f` is convex on `C` if and only if its Hessian
matrix `Q_x = (q_ij x)`, `q_ij = ∂²f/∂ξᵢ∂ξⱼ`, is positive semi-definite for every `x ∈ C`.

Positive semi-definiteness of `Q_x` is, by the book's own definition two paragraphs earlier
(line 1236), the condition `⟨z, Q_x z⟩ ≥ 0` for every `z ∈ ℝⁿ`. That quadratic form is
`fderiv ℝ (fderiv ℝ f) x z z` — the second Fréchet derivative evaluated at `(z, z)` — and that is
how the condition is stated here. The passage to the matrix of second partial derivatives in the
standard basis of `Rn n` is coordinate bookkeeping and is not stated; see the module docstring.

The proof is Rockafellar's: reduce to lines, use `g'' λ = ⟨z, Q_x z⟩`, apply Theorem 4.4. Both
steps are `private` lemmas above and both are backbone gaps — the backbone has only the forward
half of the reduction (`convexOn_comp_line`) and none of the derivative computation. -/
theorem theorem_4_5 {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) (hCopen : IsOpen C)
    {f : Rn n → ℝ} (hf : ContDiffOn ℝ 2 f C) :
    ConvexOn ℝ C f ↔ ∀ x ∈ C, ∀ z : Rn n, 0 ≤ fderiv ℝ (fderiv ℝ f) x z z := by
  rw [convexOn_iff_lines hC f]
  constructor
  · intro h x hx z
    have h0 : x + (0 : ℝ) • z ∈ C := by simpa using hx
    have hmono : MonotoneOn (deriv fun s : ℝ => f (x + s • z)) {t : ℝ | x + t • z ∈ C} :=
      (h x hx z).monotoneOn_deriv fun s hs => (hasDerivAt_comp_line hCopen hf hs).differentiableAt
    have hnn := hmono.derivWithin_nonneg (x := (0 : ℝ))
    rw [derivWithin_of_isOpen (isOpen_line_steps hCopen x z) h0,
      (hasDerivAt_deriv_comp_line hCopen hf h0).deriv] at hnn
    simpa using hnn
  · intro h y hy z
    refine convexOn_of_deriv2_nonneg' (convex_line_steps hC y z)
      (fun s hs => (hasDerivAt_comp_line hCopen hf hs).differentiableAt.differentiableWithinAt)
      (fun s hs =>
        (hasDerivAt_deriv_comp_line hCopen hf hs).differentiableAt.differentiableWithinAt)
      fun s hs => ?_
    change (0 : ℝ) ≤ deriv (deriv fun s : ℝ => f (y + s • z)) s
    rw [(hasDerivAt_deriv_comp_line hCopen hf hs).deriv]
    exact h _ hs z

/-! ### Theorem 4.6 and Corollary 4.6.1 -/

/-- **Rockafellar, Theorem 4.6.** For any convex function `f` and any `α ∈ [-∞, +∞]`, the level
sets `{x | f x < α}` and `{x | f x ≤ α}` are convex.

The book prints this as a single sentence about two sets, with no clause labels, so it is one
declaration. `α` genuinely ranges over `EReal`, including `±∞`; no properness or finiteness
hypothesis appears, and none is needed.

Specialises `ConvexFn.convex_lt` and `ConvexFn.convex_le`. -/
theorem theorem_4_6 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (α : EReal) :
    Convex ℝ {x | f x < α} ∧ Convex ℝ {x | f x ≤ α} :=
  ⟨hf.convex_lt α, hf.convex_le α⟩

/-- **Rockafellar, Corollary 4.6.1.** Let `fᵢ` be a convex function on `ℝⁿ` and `αᵢ` a real number
for each `i ∈ I`, where `I` is an arbitrary index set. Then

`C = {x | fᵢ x ≤ αᵢ, ∀ i ∈ I}`

is a convex set.

The book's proof is "Like Corollary 2.1.1", i.e. an arbitrary intersection of convex sets is
convex. Specialises `ConvexFn.convex_le` through `convex_iInter`. -/
theorem corollary_4_6_1 {n : ℕ} {I : Type*} {f : I → Rn n → EReal} (hf : ∀ i, ConvexFn (f i))
    (α : I → ℝ) : Convex ℝ {x : Rn n | ∀ i, f i x ≤ ((α i : ℝ) : EReal)} := by
  have hEq : {x : Rn n | ∀ i, f i x ≤ ((α i : ℝ) : EReal)}
      = ⋂ i, {x : Rn n | f i x ≤ ((α i : ℝ) : EReal)} := by
    ext x; simp
  rw [hEq]
  exact convex_iInter fun i => (hf i).convex_le _

/-! ### Theorem 4.7 and its corollaries -/

/-- **Rockafellar, Theorem 4.7.** A positively homogeneous function `f` from `ℝⁿ` to `(-∞, +∞]` is
convex if and only if `f (x + y) ≤ f x + f y` for every `x, y ∈ ℝⁿ`.

The book's proof is Theorem 2.6 applied to `epi f`: subadditivity is exactly closure of the cone
`epi f` under addition.

Specialises `PosHomogeneous.convexFn_iff_subadditive`, which the backbone cites by this number. -/
theorem theorem_4_7 {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hbot : ∀ x, f x ≠ ⊥) :
    ConvexFn f ↔ ∀ x y : Rn n, f (x + y) ≤ f x + f y :=
  hf.convexFn_iff_subadditive hbot

/-- **Rockafellar, Corollary 4.7.1.** If `f` is a positively homogeneous proper convex function,
then

`f (λ₁ x₁ + ⋯ + λₘ xₘ) ≤ λ₁ f x₁ + ⋯ + λₘ f xₘ`

whenever `λ₁ > 0, …, λₘ > 0`.

The book prints no proof. The index range must be nonempty (`0 < m`), which the book's
`λ₁, …, λₘ` implies: the empty sum would assert `f 0 ≤ 0`, and a positively homogeneous proper
convex function may have `f 0 = +∞` — `δ(·|C)` for a convex cone `C` missing the origin.

Specialises `PosHomogeneous.sum_le`. -/
theorem corollary_4_7_1 {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hproper : Proper f) {m : ℕ} (hm : 0 < m) {l : Fin m → ℝ} (hl : ∀ i, 0 < l i)
    (x : Fin m → Rn n) : f (∑ i, l i • x i) ≤ ∑ i, (l i : EReal) * f (x i) :=
  hf.sum_le hconv hproper.ne_bot ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i _ => hl i) x

/-- **Rockafellar, Corollary 4.7.2.** If `f` is a positively homogeneous proper convex function,
then `f (-x) ≥ -f x` for every `x`.

The book's proof: `f x + f (-x) ≥ f (x − x) = f 0 ≥ 0`.

Specialises `PosHomogeneous.neg_le`. -/
theorem corollary_4_7_2 {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hproper : Proper f) (x : Rn n) : -(f x) ≤ f (-x) :=
  hf.neg_le hconv hproper.ne_bot x

/-! ### Theorem 4.8 -/

/-- **Rockafellar, Theorem 4.8.** A positively homogeneous proper convex function `f` is linear on
a subspace `L` if and only if `f (-x) = -f x` for every `x ∈ L`.

"Linear on `L`" is rendered as the existence of a genuine linear functional `L →ₗ[ℝ] ℝ` agreeing
with `f` on `L`; that such a functional can be extracted at all is part of the content, since a
function odd at `x` is automatically finite there.

Specialises `PosHomogeneous.exists_linearMap_iff`. The unbundled form — additivity and
homogeneity as two separate statements about `f` — is `PosHomogeneous.isLinearOn_iff`. -/
theorem theorem_4_8 {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hproper : Proper f) (L : Submodule ℝ (Rn n)) :
    (∃ g : L →ₗ[ℝ] ℝ, ∀ x : L, f x = ((g x : ℝ) : EReal)) ↔ ∀ x ∈ L, f (-x) = -(f x) :=
  hf.exists_linearMap_iff hconv hproper.ne_bot L

/-- **Rockafellar, Theorem 4.8**, final sentence: "This is true if merely `f (-bᵢ) = -f bᵢ` for all
the vectors in some basis `b₁, …, bₘ` for `L`."

Stated for an arbitrary nonempty spanning set rather than a basis, which is what the book's proof
actually uses and which covers the basis case. Combine with `theorem_4_8` to get linearity on `L`.

The nonemptiness hypothesis is not decoration. Rockafellar's proof writes `f (λᵢ bᵢ) = λᵢ f bᵢ`
"for every `λᵢ ∈ ℝ`, not just for `λᵢ > 0`", which at `λᵢ = 0` silently uses `f 0 = 0`; that is
available only once some vector is known to be odd. For `L = {0}` with an empty basis the
statement fails as printed, since a positively homogeneous proper convex `f` may have `f 0 = +∞`.

Specialises `PosHomogeneous.neg_eq_of_mem_span`. -/
theorem theorem_4_8_basis {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hproper : Proper f) {L : Submodule ℝ (Rn n)} {b : Set (Rn n)} (hb : b.Nonempty)
    (hspan : Submodule.span ℝ b = L) (hodd : ∀ v ∈ b, f (-v) = -(f v)) :
    ∀ x ∈ L, f (-x) = -(f x) := by
  subst hspan
  exact fun x hx => hf.neg_eq_of_mem_span hconv hproper.ne_bot hb hodd hx

end Rockafellar
