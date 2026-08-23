/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Helly
import Tdaf.Analysis.Convex.Optimization.Minimum

/-!
# Ordinary convex programs and Lagrange multipliers

Rockafellar's §28. An *ordinary convex program* is the problem of minimising `f₀` over the set
`C = dom f₀` subject to finitely many convex inequalities `fᵢ x ≤ 0` and finitely many affine
constraints. This file carries the part of §28 that is not about coordinates: the **existence of
Kuhn–Tucker vectors under Slater's condition**, Rockafellar's Theorem 28.2.

## Main results

* `feasibleSet`, `programLagrangian`, `optimalValue`, `IsKuhnTuckerVector` — the vocabulary.
* `exists_isKuhnTuckerVector_of_slater` — **Theorem 28.2**.
* `exists_isKuhnTuckerVector_of_mem_dom` — **Corollary 28.2.1**: for a program whose constraints
  are all of the strict kind, the Slater point may be taken anywhere in `C`, not just in `ri C`.
* `exists_isKuhnTuckerVector_of_affine` — **Corollary 28.2.2**: a program with only affine
  constraints needs only a feasible point in `ri C`.
* `exists_multipliers_of_slater_eq` — Theorem 28.2 for programs with affine *equality* constraints,
  whose multipliers are then of unrestricted sign.

## What is not here

Theorems 28.1, 28.3, 28.4 and Corollary 28.3.1 are the saddle-point and complementary-slackness
descriptions of optimality; they are surface material (Theorem 28.3 additionally needs §36), and
the `(m + 3)`-tuple packaging goes with them.

## Design notes

**Two families of constraints, not one.** Rockafellar's `(m + 3)`-tuple `(C, f₀, …, f_m, r)` is a
surface-level packaging; what the mathematics needs is the split by *role*. The constraints indexed
by `ι` are the ones at which Slater's condition asks for a **strict** inequality — Rockafellar's
set `I` of indices where `fᵢ` is not affine — and they are `EReal`-valued convex functions. The
constraints indexed by `κ` are affine, are asked only for a weak inequality, and are `E →ᵃ[ℝ] ℝ`.
This is exactly the split that Theorem 21.2 (`alternative_of_convex_system_affine`) is stated
against, which is why Theorem 28.2 is a direct application of it, and why Corollary 28.2.2 is the
case `ι = Empty` and needs no separate argument.

**`C` is `dom f₀`.** Rockafellar's assumption (a) at the start of §28 is exactly `dom f₀ = C`, and
his assumption (b) is `dom fᵢ ⊇ C`, here `hsub`. Assumption (b) is not decoration: it is what makes
every `fᵢ` finite on `C`, and hence what makes the multiplier inequality an inequality between
*real numbers*, which can be divided by `λ₀`. Theorem 21.2's own domain hypothesis
`ri C ⊆ dom (f i)` then needs no separate assumption — it follows from `hsub`.

**The objective is shifted by the optimal value, not by an arbitrary constant.** The `Option ι`
index type carries `f₀ - α` in the `none` slot and the strict constraints in the `some` slots;
`l ≠ 0` from Theorem 21.2 plus the Slater point is what forces the multiplier of the `none` slot to
be strictly positive, which is the whole content of the proof.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §28.
-/

namespace Tdaf.ConvexAnalysis

open Set Filter Topology

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The set of **feasible solutions** of the constraint system `fᵢ x ≤ 0`, `bⱼ x ≤ 0`. -/
def feasibleSet (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ) : Set E :=
  {x | (∀ i, f i x ≤ 0) ∧ ∀ j, b j x ≤ 0}

omit [Fintype ι] [Fintype κ] in
@[simp] theorem mem_feasibleSet {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ} {x : E} :
    x ∈ feasibleSet f b ↔ (∀ i, f i x ≤ 0) ∧ ∀ j, b j x ≤ 0 := Iff.rfl

/-- The **Lagrangian** of an ordinary convex program at the multipliers `(l, μ)`, that is
Rockafellar's `f₀ + λ₁f₁ + ⋯ + λ_m f_m`.

The general perturbational Lagrangian of §29 is `lagrangian`, in
`Tdaf/Analysis/Convex/Optimization/Lagrangian.lean`; this is the ordinary program's, written out. -/
noncomputable def programLagrangian (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) : E → EReal :=
  fun x => f₀ x + (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * b j x : ℝ) : EReal)

theorem programLagrangian_apply (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) (x : E) :
    programLagrangian f₀ f b l μ x
      = f₀ x + (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * b j x : ℝ) : EReal) := rfl

/-- The **optimal value** of the program: the infimum of the objective over the feasible set. -/
noncomputable def optimalValue (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ) : EReal :=
  ⨅ x ∈ feasibleSet f b, f₀ x

omit [Fintype ι] [Fintype κ] in
theorem optimalValue_le {f₀ : E → EReal} {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ} {x : E}
    (hx : x ∈ feasibleSet f b) : optimalValue f₀ f b ≤ f₀ x :=
  iInf₂_le x hx

/-- `(l, μ)` is a vector of **Kuhn–Tucker coefficients** for the program: the multipliers are
non-negative, and the infimum of the Lagrangian is finite and equal to the optimal value.

This is Rockafellar's own definition (§28), *not* the perturbational inequality
`p u + ⟨λ, u⟩ ≥ p 0` that it is equivalent to; stating it by the inequality would make the
description of §29 a definitional triviality. -/
structure IsKuhnTuckerVector (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) : Prop where
  /-- The multipliers of the convex constraints are non-negative. -/
  nonneg : ∀ i, 0 ≤ l i
  /-- The multipliers of the affine inequality constraints are non-negative. -/
  nonneg_affine : ∀ j, 0 ≤ μ j
  /-- The infimum of the Lagrangian is not `-∞`. -/
  ne_bot : (⨅ x, programLagrangian f₀ f b l μ x) ≠ ⊥
  /-- The infimum of the Lagrangian is not `+∞`. -/
  ne_top : (⨅ x, programLagrangian f₀ f b l μ x) ≠ ⊤
  /-- The infimum of the Lagrangian is the optimal value in the program. -/
  iInf_eq : (⨅ x, programLagrangian f₀ f b l μ x) = optimalValue f₀ f b

end Defs

section Elementary

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {f₀ : E → EReal} {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ} {l : ι → ℝ} {μ : κ → ℝ}

/-- A non-negative real multiple of a non-positive `EReal` is non-positive. The coefficient `0` is
harmless because `EReal` obeys Rockafellar's convention `0 · ∞ = 0`. -/
theorem coe_mul_nonpos {c : ℝ} (hc : 0 ≤ c) {z : EReal} (hz : z ≤ 0) : (c : EReal) * z ≤ 0 := by
  rcases eq_or_lt_of_le hc with h | h
  · rw [← h]; simp
  · calc (c : EReal) * z ≤ (c : EReal) * 0 := by
          refine mul_le_mul_of_nonneg_left hz ?_
          exact_mod_cast hc
      _ = 0 := by simp

/-- A non-negatively weighted sum of strictly negative values, with at least one non-zero weight,
is strictly negative. This is what rules out a vanishing multiplier on the objective in
Theorem 28.2. -/
theorem sum_coe_mul_neg (hl : ∀ i, 0 ≤ l i) {v : ι → EReal} (hv : ∀ i, v i < 0) {i₀ : ι}
    (hi₀ : l i₀ ≠ 0) : (∑ i, (l i : EReal) * v i) < 0 := by
  classical
  have hpos : 0 < l i₀ := lt_of_le_of_ne (hl i₀) (Ne.symm hi₀)
  have hterm : (l i₀ : EReal) * v i₀ < 0 := by
    have hlt : ¬ ((l i₀ : EReal) * 0 ≤ (l i₀ : EReal) * v i₀) := by
      rw [Tdaf.EReal.coe_mul_le_coe_mul_iff hpos]
      exact not_le.2 (hv i₀)
    simpa using not_le.1 hlt
  have hrest : ∑ i ∈ Finset.univ.erase i₀, (l i : EReal) * v i ≤ 0 :=
    Finset.sum_nonpos fun i _ => coe_mul_nonpos (hl i) (hv i).le
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  calc (l i₀ : EReal) * v i₀ + ∑ i ∈ Finset.univ.erase i₀, (l i : EReal) * v i
      ≤ (l i₀ : EReal) * v i₀ + 0 := add_le_add (le_refl _) hrest
    _ = (l i₀ : EReal) * v i₀ := add_zero _
    _ < 0 := hterm

/-- On the feasible set the Lagrangian never exceeds the objective: every constraint term is
non-positive there. -/
theorem programLagrangian_le_of_mem_feasibleSet (hl : ∀ i, 0 ≤ l i) (hμ : ∀ j, 0 ≤ μ j)
    {x : E} (hx : x ∈ feasibleSet f b) : programLagrangian f₀ f b l μ x ≤ f₀ x := by
  have hsum : (∑ i, (l i : EReal) * f i x) ≤ 0 :=
    Finset.sum_nonpos fun i _ => coe_mul_nonpos (hl i) (hx.1 i)
  have haff : ((∑ j, μ j * b j x : ℝ) : EReal) ≤ 0 := by
    have h : (∑ j, μ j * b j x) ≤ 0 :=
      Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hμ j) (hx.2 j)
    exact_mod_cast h
  calc programLagrangian f₀ f b l μ x
      ≤ f₀ x + (∑ i, (l i : EReal) * f i x) + 0 := add_le_add (le_refl _) haff
    _ = f₀ x + (∑ i, (l i : EReal) * f i x) := add_zero _
    _ ≤ f₀ x + 0 := add_le_add (le_refl _) hsum
    _ = f₀ x := add_zero _

/-- Off the effective domain of the objective the Lagrangian is `+∞`: no constraint term can be
`-∞`, because the constraint functions never take `-∞` and the multipliers are non-negative. -/
theorem programLagrangian_eq_top (hl : ∀ i, 0 ≤ l i) (hbot : ∀ i x, f i x ≠ ⊥) {x : E}
    (hx : f₀ x = ⊤) : programLagrangian f₀ f b l μ x = ⊤ := by
  have hsum : (∑ i, (l i : EReal) * f i x) ≠ ⊥ :=
    Tdaf.EReal.sum_ne_bot fun i _ => Tdaf.EReal.coe_mul_ne_bot (hl i) (hbot i x)
  rw [programLagrangian_apply, hx, _root_.EReal.top_add_of_ne_bot hsum,
    _root_.EReal.top_add_of_ne_bot (_root_.EReal.coe_ne_bot _)]

/-- The Lagrangian at a point where the objective and every constraint is finite, read as a single
real number. -/
theorem programLagrangian_eq_coe {x : E} {r₀ : ℝ} (h₀ : f₀ x = (r₀ : EReal)) {r : ι → ℝ}
    (hr : ∀ i, f i x = (r i : EReal)) :
    programLagrangian f₀ f b l μ x
      = ((r₀ + (∑ i, l i * r i) + ∑ j, μ j * b j x : ℝ) : EReal) := by
  have hterm : ∀ i, (l i : EReal) * f i x = ((l i * r i : ℝ) : EReal) := fun i => by
    rw [hr i, Tdaf.EReal.coe_mul_coe]
  rw [programLagrangian_apply, h₀, Finset.sum_congr rfl (fun i _ => hterm i),
    ← Tdaf.EReal.coe_sum, ← _root_.EReal.coe_add, ← _root_.EReal.coe_add]

end Elementary

section Slater

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {f₀ : E → EReal} {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] [Fintype κ] in
/-- Shifting an `EReal` by a real constant: `u + (-a) < 0` says exactly `u < a`. -/
private theorem add_neg_coe_lt_zero_iff {u : EReal} {a : ℝ} :
    u + ((-a : ℝ) : EReal) < 0 ↔ u < (a : EReal) := by
  induction u with
  | bot => simp
  | top => simp
  | coe r =>
    rw [← _root_.EReal.coe_add, ← _root_.EReal.coe_zero, _root_.EReal.coe_lt_coe_iff,
      _root_.EReal.coe_lt_coe_iff]
    constructor <;> intro h <;> linarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] [Fintype κ] in
/-- Shifting an `EReal` by a real constant does not change its effective domain. -/
private theorem add_neg_coe_lt_top_iff {u : EReal} {a : ℝ} :
    u + ((-a : ℝ) : EReal) < ⊤ ↔ u < ⊤ := by
  induction u with
  | bot => simp
  | top => simp
  | coe r =>
    rw [← _root_.EReal.coe_add]
    exact iff_of_true (_root_.EReal.coe_lt_top _) (_root_.EReal.coe_lt_top _)

/-- **Rockafellar, Theorem 28.2.** Suppose the optimal value of the program is not `-∞`, and that
the program has a feasible solution in `ri C` — `C = dom f₀` — satisfying *strictly* every
constraint of the first family. Then a vector of Kuhn–Tucker coefficients exists.

The first family `f` is Rockafellar's set `I` of indices at which `fᵢ` is not affine; the second
family `b` is affine and is asked only for a weak inequality. -/
theorem exists_isKuhnTuckerVector_of_slater (hf₀ : ConvexFn f₀) (hp₀ : Proper f₀)
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i)) (hsub : ∀ i, dom f₀ ⊆ dom (f i))
    (hbot : optimalValue f₀ f b ≠ ⊥)
    (hslater : ∃ x ∈ ri (dom f₀), (∀ i, f i x < 0) ∧ ∀ j, b j x ≤ 0) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ), IsKuhnTuckerVector f₀ f b l μ := by
  classical
  obtain ⟨z, hzri, hzf, hzb⟩ := hslater
  have hzC : z ∈ dom f₀ := intrinsicInterior_subset hzri
  have hzfeas : z ∈ feasibleSet f b := ⟨fun i => (hzf i).le, hzb⟩
  -- the optimal value is a real number
  have htop : optimalValue f₀ f b < ⊤ :=
    lt_of_le_of_lt (optimalValue_le hzfeas) (mem_dom.1 hzC)
  obtain ⟨α, hα⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top hbot htop
  -- the shifted system, indexed by `Option ι`
  set g : Option ι → E → EReal := fun i' x => i'.elim (f₀ x + ((-α : ℝ) : EReal)) (fun i => f i x)
    with hgdef
  have hgnone : g none = fun x => f₀ x + ((-α : ℝ) : EReal) := rfl
  have hgsome : ∀ i, g (some i) = f i := fun _ => rfl
  have hgconv : ∀ i', ConvexFn (g i') := by
    rintro (_ | i)
    · have : ConvexFn (f₀ + fun _ : E => ((-α : ℝ) : EReal)) :=
        hf₀.add (convexFn_const _) hp₀.ne_bot (fun _ => _root_.EReal.coe_ne_bot _)
      exact this
    · exact hf i
  have hgproper : ∀ i', Proper (g i') := by
    rintro (_ | i)
    · refine ⟨⟨z, ?_⟩, fun x => ?_⟩
      · exact mem_dom.2 (add_neg_coe_lt_top_iff.2 (mem_dom.1 hzC))
      · exact _root_.EReal.add_ne_bot_iff.2 ⟨hp₀.ne_bot x, _root_.EReal.coe_ne_bot _⟩
    · exact hp i
  have hgdom : ∀ i', ri (dom f₀) ⊆ dom (g i') := by
    rintro (_ | i) x hx
    · exact mem_dom.2 (add_neg_coe_lt_top_iff.2 (mem_dom.1 (intrinsicInterior_subset hx)))
    · exact hsub i (intrinsicInterior_subset hx)
  -- the strict system is unsolvable, so Theorem 21.2 produces multipliers
  have hnoalt : ¬ ∃ x ∈ dom f₀, (∀ i', g i' x < 0) ∧ ∀ j, b j x ≤ 0 := by
    rintro ⟨x, _, hxg, hxb⟩
    have hx0 : f₀ x < (α : EReal) := add_neg_coe_lt_zero_iff.1 (hxg none)
    have hxfeas : x ∈ feasibleSet f b := ⟨fun i => (hxg (some i)).le, hxb⟩
    have hle : (α : EReal) ≤ f₀ x := hα ▸ optimalValue_le (f₀ := f₀) hxfeas
    exact absurd (lt_of_le_of_lt hle hx0) (lt_irrefl _)
  obtain ⟨c, μ, hcnonneg, hμnonneg, hcne, hkey⟩ :=
    (alternative_of_convex_system_affine (C := dom f₀) (f := g) (a := b) hf₀.convex_dom hgconv
      hgproper hgdom ⟨z, hzri, hzb⟩).resolve_left hnoalt
  -- the multiplier of the objective is positive
  have hcpos : 0 < c none := by
    rcases eq_or_lt_of_le (hcnonneg none) with h0 | h0
    · exfalso
      obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ι, c (some i₀) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hcne (funext fun i' => by
          cases i' with
          | none => exact h0.symm
          | some i => exact hcon i)
      have hz' := hkey z hzC
      rw [Fintype.sum_option] at hz'
      have hfirst : (c none : EReal) * g none z = 0 := by
        rw [← h0]; simp
      have hsecond : (∑ i, (c (some i) : EReal) * g (some i) z) < 0 := by
        refine sum_coe_mul_neg (l := fun i => c (some i)) (fun i => hcnonneg (some i))
          (v := fun i => g (some i) z) (fun i => ?_) hi₀
        rw [hgsome i]; exact hzf i
      have hthird : ((∑ j, μ j * b j z : ℝ) : EReal) ≤ 0 := by
        have h : (∑ j, μ j * b j z) ≤ 0 :=
          Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hμnonneg j) (hzb j)
        exact_mod_cast h
      rw [hfirst, zero_add] at hz'
      have : (∑ i, (c (some i) : EReal) * g (some i) z) + ((∑ j, μ j * b j z : ℝ) : EReal) < 0 :=
        lt_of_le_of_lt (add_le_add (le_refl _) hthird) (by simpa using hsecond)
      exact absurd hz' (not_le.2 this)
    · exact h0
  -- normalise: divide every multiplier by the one on the objective
  set l : ι → ℝ := fun i => c (some i) / c none with hldef
  set ν : κ → ℝ := fun j => μ j / c none with hνdef
  have hlnonneg : ∀ i, 0 ≤ l i := fun i => div_nonneg (hcnonneg (some i)) hcpos.le
  have hνnonneg : ∀ j, 0 ≤ ν j := fun j => div_nonneg (hμnonneg j) hcpos.le
  have hL : ∀ x, (α : EReal) ≤ programLagrangian f₀ f b l ν x := by
    intro x
    by_cases hxC : x ∈ dom f₀
    · obtain ⟨r₀, hr₀⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp₀.ne_bot x) (mem_dom.1 hxC)
      have hrfin : ∀ i, ∃ r : ℝ, f i x = (r : EReal) := fun i =>
        Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top ((hp i).ne_bot x) (mem_dom.1 (hsub i hxC))
      choose r hr using hrfin
      have hx' := hkey x hxC
      rw [Fintype.sum_option] at hx'
      have hnone : (c none : EReal) * g none x = ((c none * (r₀ + -α) : ℝ) : EReal) := by
        change (c none : EReal) * (f₀ x + ((-α : ℝ) : EReal)) = _
        rw [hr₀, ← _root_.EReal.coe_add, Tdaf.EReal.coe_mul_coe]
      have hsome : ∀ i, (c (some i) : EReal) * g (some i) x = ((c (some i) * r i : ℝ) : EReal) := by
        intro i; rw [hgsome i, hr i, Tdaf.EReal.coe_mul_coe]
      rw [hnone, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hsome i),
        ← Tdaf.EReal.coe_sum, ← _root_.EReal.coe_add, ← _root_.EReal.coe_add,
        ← _root_.EReal.coe_zero, _root_.EReal.coe_le_coe_iff] at hx'
      rw [programLagrangian_eq_coe hr₀ hr, _root_.EReal.coe_le_coe_iff]
      refine le_of_mul_le_mul_left ?_ hcpos
      have hsumfield : c none * (∑ i, l i * r i) = ∑ i, c (some i) * r i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hldef]
        field_simp
      have haffield : c none * (∑ j, ν j * b j x) = ∑ j, μ j * b j x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hνdef]
        field_simp
      have hexp : c none * (r₀ + (∑ i, l i * r i) + ∑ j, ν j * b j x)
          = c none * r₀ + c none * (∑ i, l i * r i) + c none * (∑ j, ν j * b j x) := by ring
      have hshift : c none * (r₀ + -α) = c none * r₀ - c none * α := by ring
      rw [hexp, hsumfield, haffield]
      rw [hshift] at hx'
      linarith
    · have htopx : f₀ x = ⊤ := by
        rcases lt_or_eq_of_le (le_top : f₀ x ≤ ⊤) with h | h
        · exact absurd (mem_dom.2 h) hxC
        · exact h
      rw [programLagrangian_eq_top hlnonneg (fun i y => (hp i).ne_bot y) htopx]
      exact le_top
  have hiInf : (⨅ x, programLagrangian f₀ f b l ν x) = (α : EReal) := by
    refine le_antisymm ?_ (le_iInf hL)
    rw [← hα]
    exact le_iInf₂ fun x hx =>
      (iInf_le _ x).trans (programLagrangian_le_of_mem_feasibleSet hlnonneg hνnonneg hx)
  exact ⟨l, ν, hlnonneg, hνnonneg, by rw [hiInf]; exact _root_.EReal.coe_ne_bot _,
    by rw [hiInf]; exact _root_.EReal.coe_ne_top _, by rw [hiInf, hα]⟩

/-- **Rockafellar, Corollary 28.2.2.** A program whose only constraints are affine needs nothing
more than a feasible solution in `ri C`: it is Theorem 28.2 with an empty family of strict
constraints. -/
theorem exists_isKuhnTuckerVector_of_affine [IsEmpty ι] (hf₀ : ConvexFn f₀) (hp₀ : Proper f₀)
    (hbot : optimalValue f₀ f b ≠ ⊥) (hfeas : ∃ x ∈ ri (dom f₀), ∀ j, b j x ≤ 0) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ), IsKuhnTuckerVector f₀ f b l μ := by
  obtain ⟨x, hx, hxb⟩ := hfeas
  exact exists_isKuhnTuckerVector_of_slater hf₀ hp₀ (fun i => isEmptyElim i)
    (fun i => isEmptyElim i) (fun i => isEmptyElim i) hbot ⟨x, hx, fun i => isEmptyElim i, hxb⟩

omit [FiniteDimensional ℝ E] [Fintype ι] [Fintype κ] in
/-- The point `(1 - a) • y + a • z` of the segment from `y` to `z`, read as an affine map applied
to a line. This is what lets an affine constraint be followed along the prolongation used in
Corollary 28.2.1. -/
theorem affineMap_segment (g : E →ᵃ[ℝ] ℝ) (y z : E) (a : ℝ) :
    g ((1 - a) • y + a • z) = (1 - a) * g y + a * g z := by
  have hseg : (1 - a) • y + a • z = AffineMap.lineMap y z a := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  rw [hseg, AffineMap.apply_lineMap, AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  ring

/-- **Rockafellar, Corollary 28.2.1.** When every constraint is satisfied *strictly* at some point
of `C`, that point need not lie in `ri C`: prolonging it towards a relative interior point produces
a Slater point for Theorem 28.2.

Rockafellar states this for a program with no affine constraints (his `r = m`); the statement here
allows them, at the price of asking for strict inequality there too, which is what survives the
prolongation. `hri` is the other half of Rockafellar's standing assumption (b) at the start of §28,
and is what Theorem 7.5 needs in order to follow `fᵢ` along the segment. -/
theorem exists_isKuhnTuckerVector_of_mem_dom (hf₀ : ConvexFn f₀) (hp₀ : Proper f₀)
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i)) (hsub : ∀ i, dom f₀ ⊆ dom (f i))
    (hri : ∀ i, ri (dom f₀) ⊆ ri (dom (f i))) (hbot : optimalValue f₀ f b ≠ ⊥)
    (hslater : ∃ x ∈ dom f₀, (∀ i, f i x < 0) ∧ ∀ j, b j x < 0) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ), IsKuhnTuckerVector f₀ f b l μ := by
  classical
  obtain ⟨z, hz, hzf, hzb⟩ := hslater
  obtain ⟨y, hy⟩ := Convex.relint_nonempty hf₀.convex_dom ⟨z, hz⟩
  -- along the segment from `y` to `z`, every constraint stays strict near the far end
  have hmem : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), (1 - a) • y + a • z ∈ ri (dom f₀) := by
    filter_upwards [(eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with a ha ha'
    exact Convex.segment_mem_relint hf₀.convex_dom hy (subset_closure hz) ha.le ha'
  have hcon : ∀ i, ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), f i ((1 - a) • y + a • z) < 0 := by
    intro i
    have hlim := (hf i).tendsto_lscHull_along_segment_relint (hri i hy) z
    exact hlim.eventually_lt_const (lt_of_le_of_lt (lscHull_le (f i) z) (hzf i))
  have haff : ∀ j, ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), b j ((1 - a) • y + a • z) < 0 := by
    intro j
    have hlim : Filter.Tendsto (fun a : ℝ => b j ((1 - a) • y + a • z)) (𝓝[<] (1 : ℝ))
        (𝓝 (b j z)) := by
      have : Filter.Tendsto (fun a : ℝ => (1 - a) * b j y + a * b j z) (𝓝 (1 : ℝ))
          (𝓝 ((1 - 1) * b j y + 1 * b j z)) :=
        (((tendsto_const_nhds.sub tendsto_id).mul tendsto_const_nhds).add
          (tendsto_id.mul tendsto_const_nhds))
      simp only [sub_self, zero_mul, one_mul, zero_add] at this
      exact (this.mono_left nhdsWithin_le_nhds).congr fun a => (affineMap_segment (b j) y z a).symm
    exact hlim.eventually_lt_const (hzb j)
  obtain ⟨a, hamem, hafeas⟩ :=
    ((hmem.and ((Filter.eventually_all).2 hcon)).and ((Filter.eventually_all).2 haff)).exists
  exact exists_isKuhnTuckerVector_of_slater hf₀ hp₀ hf hp hsub hbot
    ⟨_, hamem.1, hamem.2, fun j => (hafeas j).le⟩

/-- **Rockafellar, Theorem 28.2** for a program whose affine constraints are *equations*. Their
multipliers are then of unrestricted sign, obtained as `μ' - μ''` from the two inequalities each
equation splits into — Rockafellar's own reduction. -/
theorem exists_multipliers_of_slater_eq {σ : Type*} [Fintype σ] {a : σ → E →ᵃ[ℝ] ℝ}
    (hf₀ : ConvexFn f₀) (hp₀ : Proper f₀) (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i))
    (hsub : ∀ i, dom f₀ ⊆ dom (f i))
    (hbot : optimalValue f₀ f (Sum.elim a fun k => -(a k)) ≠ ⊥)
    (hslater : ∃ x ∈ ri (dom f₀), (∀ i, f i x < 0) ∧ ∀ k, a k x = 0) :
    ∃ (l : ι → ℝ) (ρ : σ → ℝ), (∀ i, 0 ≤ l i) ∧
      (⨅ x, f₀ x + (∑ i, (l i : EReal) * f i x) + ((∑ k, ρ k * a k x : ℝ) : EReal))
        = ⨅ x ∈ {x | (∀ i, f i x ≤ 0) ∧ ∀ k, a k x = 0}, f₀ x := by
  classical
  set b' : σ ⊕ σ → E →ᵃ[ℝ] ℝ := Sum.elim a fun k => -(a k) with hb'
  have hinl : ∀ (k : σ) (x : E), b' (Sum.inl k) x = a k x := fun _ _ => rfl
  have hinr : ∀ (k : σ) (x : E), b' (Sum.inr k) x = -(a k x) := fun _ _ => rfl
  have hsplit : ∀ (x : E), (∀ j, b' j x ≤ 0) ↔ ∀ k, a k x = 0 := by
    intro x
    constructor
    · intro h k
      have h₁ := h (Sum.inl k)
      have h₂ := h (Sum.inr k)
      rw [hinl k x] at h₁
      rw [hinr k x] at h₂
      linarith
    · rintro h (k | k)
      · rw [hinl k x, h k]
      · rw [hinr k x, h k, neg_zero]
  have hfeasEq : feasibleSet f b' = {x | (∀ i, f i x ≤ 0) ∧ ∀ k, a k x = 0} := by
    ext x
    exact and_congr_right fun _ => hsplit x
  obtain ⟨x₀, hx₀, hx₀f, hx₀a⟩ := hslater
  obtain ⟨l, μ, hkt⟩ := exists_isKuhnTuckerVector_of_slater (b := b') hf₀ hp₀ hf hp hsub hbot
    ⟨x₀, hx₀, hx₀f, (hsplit x₀).2 hx₀a⟩
  refine ⟨l, fun k => μ (Sum.inl k) - μ (Sum.inr k), hkt.nonneg, ?_⟩
  have hlag : ∀ x, f₀ x + (∑ i, (l i : EReal) * f i x)
      + ((∑ k, (μ (Sum.inl k) - μ (Sum.inr k)) * a k x : ℝ) : EReal)
      = programLagrangian f₀ f b' l μ x := by
    intro x
    rw [programLagrangian_apply]
    congr 2
    rw [Fintype.sum_sum_type]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hb', Sum.elim_inl, Sum.elim_inr, AffineMap.coe_neg, Pi.neg_apply]
    ring
  rw [iInf_congr hlag, hkt.iInf_eq, optimalValue, hfeasEq]

end Slater

end Tdaf.ConvexAnalysis

