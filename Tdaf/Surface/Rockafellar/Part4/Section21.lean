/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.HellyRefined
import Tdaf.Surface.Common.Euclidean

/-!
# Rockafellar, §21: Helly's Theorem and Systems of Inequalities

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §21, pp. 185–197: existence theorems for
systems of convex inequalities, stated as pairs of mutually exclusive alternatives, and the four
forms of Helly's theorem that come out of them.

## The section's own vocabulary

A **system of convex inequalities** is `fᵢ(x) ≤ αᵢ` for `i ∈ I₁` together with `fᵢ(x) < αᵢ` for
`i ∈ I₂`, where `I₁` and `I₂` are arbitrary index sets, each `fᵢ` is a convex function on all of
`ℝⁿ` and `-∞ ≤ αᵢ ≤ +∞`. `ConvexSystem` is that data, `ConvexSystem.solutions` its solution set and
`ConvexSystem.Consistent` the book's "consistent". The three facts the book states about it in
prose — the solution set is an intersection of level sets, it is convex, and it is closed when
there are no strict inequalities and the `fᵢ` are closed — are `solutions_eq_iInter`,
`convex_solutions` and `isClosed_solutions`.

The numbered theorems below are all stated with right-hand sides `0`, which is what the book does
after observing that `fᵢ(x) ≤ αᵢ` is `gᵢ(x) ≤ 0` for `gᵢ = fᵢ - αᵢ` when `αᵢ` is finite:
`solutions_normalize` is that observation. `pairing_eq_iff` is the other translation device of the
opening pages, the one that writes a linear *equation* as two inequalities.

## The shape of the results

Theorems 21.1, 21.2 and 21.3 are "one and only one of the following alternatives holds". Each is
two declarations: `theorem_21_k` is the disjunction — the half with content — and
`theorem_21_k_exclusive` is the half that says the alternatives cannot both hold.

## Contents

| label | declaration |
|---|---|
| Theorem 21.1 | `theorem_21_1`, `theorem_21_1_exclusive` |
| Theorem 21.2 | `theorem_21_2`, `theorem_21_2_exclusive` |
| Theorem 21.3 | `theorem_21_3`, `theorem_21_3_exclusive` |
| Corollary 21.3.1 | `corollary_21_3_1` |
| Corollary 21.3.2 | `corollary_21_3_2` |
| Theorem 21.4 | `theorem_21_4`, `theorem_21_4_subsystem` |
| Theorem 21.5 | `theorem_21_5` |
| Theorem 21.6 | `theorem_21_6` |
| Corollary 21.6.1 | `corollary_21_6_1` |
| Corollary 21.6.2 | `corollary_21_6_2`, `corollary_21_6_2_affine` |

## Two hypotheses that look like typos and are not

**Theorem 21.1 asks for `dom fᵢ ⊇ ri C`, not `dom fᵢ ⊇ C`.** The weaker hypothesis is deliberate
and is exactly what the proof uses: separation only produces the inequality where every `fᵢ` is
finite, and Corollary 7.3.3 carries it from `ri C` to `cl (ri C) = cl C ⊇ C`. The book gives the
counterexample that shows some such condition is needed — `f₁(x) = -x^(1/2)` for `x ≥ 0` and `+∞`
otherwise, `f₂(x) = x`, `C = R` — where neither alternative holds.

**Alternative (b) is read in `EReal`, where `0 · (+∞) = 0`.** That convention is load-bearing:
without it a vanishing multiplier could not drop a constraint whose `fᵢ` is `+∞` somewhere, and
Corollary 21.6.2 — which extends a short multiplier vector by zeros — would be false as stated.
No `0⁺` bookkeeping appears anywhere in this section.

## What is not here

* **The two hyperbola counterexamples** (book, pp. 190–191) — *omitted with a reason*. On `R²`
  with `f₁(x) = (ξ₁² + 1)^(1/2) - ξ₂` and `f₂(x) = (ξ₂² + 1)^(1/2) - ξ₁`, neither alternative of
  Theorem 21.3 holds, and the derived family `C_{k,ε} = {x | fₖ(x) ≤ ε}` has the
  `(n+1)`-intersection property with empty intersection, so Corollary 21.3.2 fails too. Both are
  unnumbered prose showing that the recession hypothesis cannot be dropped. Transcribing them is
  a one-variable calculus computation about `Real.sqrt (ξ² + 1)`, not convex analysis, and nothing
  later in the book cites them. The same holds for the `-x^(1/2)` example after Theorem 21.1.
* **The exercise at book line 7601** — *deferred by scope*. "The recession hypothesis in Helly's
  Theorem is satisfied if and only if some finite subcollection has a bounded intersection,
  assuming every finite subcollection is non-empty. The proof of this fact is left as an
  exercise." It is unnumbered, the book supplies no proof, and its forward direction needs the
  recession-cone-of-an-intersection theory of §8 in a form the backbone states only for finitely
  many closed convex sets with a common point.

Everything else in the section's range is here.

## A citation the book gets wrong

Rockafellar's Comments and References for Part IV (book line 17309) cite a **"Corollary 21.3.3"**.
No such result exists: §21 has Corollaries 21.3.1 and 21.3.2 and nothing further. The intended
reference is Corollary 21.3.2, Helly's theorem.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §21.
-/

open Set

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

variable {n : ℕ}

/-! ### A system of convex inequalities

The book's opening definition, together with the three facts it states about the solution set and
the two translation devices of the same pages. -/

/-- Rockafellar's **system of convex inequalities** in `ℝⁿ`:

```
fᵢ(x) ≤ αᵢ,  ∀ i ∈ I₁,
fᵢ(x) < αᵢ,  ∀ i ∈ I₂,
```

with `I₁` and `I₂` arbitrary index sets and `-∞ ≤ αᵢ ≤ +∞`. Convexity of the `fᵢ` is *not* a field:
the book's own statements about the solution set carry it as a hypothesis, and the numbered
theorems below quantify over families directly rather than over this structure. -/
structure ConvexSystem (n : ℕ) (ι κ : Type*) where
  /-- The functions of the weak part, `fᵢ(x) ≤ αᵢ` for `i ∈ I₁`. -/
  weakFn : ι → Rn n → EReal
  /-- The right-hand sides `αᵢ` of the weak part, allowed to be `±∞`. -/
  weakBound : ι → EReal
  /-- The functions of the strict part, `fᵢ(x) < αᵢ` for `i ∈ I₂`. -/
  strictFn : κ → Rn n → EReal
  /-- The right-hand sides `αᵢ` of the strict part, allowed to be `±∞`. -/
  strictBound : κ → EReal

namespace ConvexSystem

variable {ι κ : Type*}

/-- The set of solutions `x` of a system of convex inequalities. -/
def solutions (S : ConvexSystem n ι κ) : Set (Rn n) :=
  {x | (∀ i, S.weakFn i x ≤ S.weakBound i) ∧ ∀ j, S.strictFn j x < S.strictBound j}

/-- The book's **consistent**: the system has at least one solution. A system is *inconsistent*
when it is not consistent, i.e. when its solution set is empty. -/
def Consistent (S : ConvexSystem n ι κ) : Prop := S.solutions.Nonempty

/-- **Rockafellar, §21, p. 185.** The solution set is the intersection of the level sets
`{x | fᵢ(x) ≤ αᵢ}`, `i ∈ I₁`, and `{x | fᵢ(x) < αᵢ}`, `i ∈ I₂`. -/
theorem solutions_eq_iInter (S : ConvexSystem n ι κ) :
    S.solutions = (⋂ i, {x | S.weakFn i x ≤ S.weakBound i})
      ∩ ⋂ j, {x | S.strictFn j x < S.strictBound j} := by
  ext x
  simp [solutions]

/-- **Rockafellar, §21, p. 185**: "The set of solutions `x` to such a system is, of course, a
certain convex set in `ℝⁿ`." -/
theorem convex_solutions (S : ConvexSystem n ι κ) (hw : ∀ i, ConvexFn (S.weakFn i))
    (hs : ∀ j, ConvexFn (S.strictFn j)) : Convex ℝ S.solutions := by
  rw [solutions_eq_iInter]
  exact Convex.inter (convex_iInter fun i => (hw i).convex_le _)
    (convex_iInter fun j => (hs j).convex_lt _)

/-- A level set `{x | f x ≤ α}` of a closed function is closed, for an *extended-real* level `α`.
`lowerSemicontinuous_iff_isClosed_le` covers only the finite levels; the two infinite ones are the
two cases of `closedFn_iff`. -/
theorem isClosed_setOf_le {f : Rn n → EReal} (hf : ClosedFn f) (a : EReal) :
    IsClosed {x : Rn n | f x ≤ a} := by
  induction a using EReal.rec with
  | bot =>
    rcases closedFn_iff.1 hf with rfl | ⟨-, hne⟩
    · simp
    · have hempty : {x : Rn n | f x ≤ ⊥} = (∅ : Set (Rn n)) := by
        ext x
        simpa using hne x
      rw [hempty]
      exact isClosed_empty
  | coe r => exact lowerSemicontinuous_iff_isClosed_le.1 hf.lowerSemicontinuous r
  | top => simp

/-- **Rockafellar, §21, p. 185**: "If every `fᵢ` is closed and there are no strict inequalities
(i.e. `I₂ = ∅`), the set of solutions is closed." -/
theorem isClosed_solutions [IsEmpty κ] (S : ConvexSystem n ι κ)
    (hw : ∀ i, ClosedFn (S.weakFn i)) : IsClosed S.solutions := by
  rw [solutions_eq_iInter]
  have hstrict : (⋂ j, {x : Rn n | S.strictFn j x < S.strictBound j}) = (univ : Set (Rn n)) := by
    simp
  rw [hstrict, Set.inter_univ]
  exact isClosed_iInter fun i => isClosed_setOf_le (hw i) _

/-- **Rockafellar, §21, p. 186**: for a *finite* right-hand side `α`, the inequality `f(x) ≤ α` is
the inequality `g(x) ≤ 0` for `g = f - α`, and likewise for the strict form. This is why every
numbered theorem of the section may be stated with all right-hand sides `0`. -/
theorem solutions_normalize (f : Rn n → EReal) (a : ℝ) (x : Rn n) :
    (f x ≤ (a : EReal) ↔ f x - (a : EReal) ≤ 0) ∧ (f x < (a : EReal) ↔ f x - (a : EReal) < 0) := by
  generalize f x = y
  induction y using EReal.rec with
  | bot => simp
  | coe r =>
    rw [← EReal.coe_sub]
    norm_cast
    exact ⟨⟨fun h => by linarith, fun h => by linarith⟩,
      ⟨fun h => by linarith, fun h => by linarith⟩⟩
  | top => simp

end ConvexSystem

/-- **Rockafellar, §21, p. 186**: "Linear equations may be incorporated into a system of convex
inequalities by the device of writing `⟨x, b⟩ = β` as a pair of inequalities: `⟨x, b⟩ ≤ β` and
`⟨x, -b⟩ ≤ -β`." -/
theorem pairing_eq_iff (x b : Rn n) (β : ℝ) :
    pairing n x b = β ↔ pairing n x b ≤ β ∧ pairing n x (-b) ≤ -β := by
  rw [map_neg]
  constructor
  · rintro h
    simp [h]
  · rintro ⟨h₁, h₂⟩
    linarith

/-! ### Theorem 21.1 -/

/-- **Rockafellar, Theorem 21.1.** Let `C` be a convex set, and let `f₁, …, f_m` be proper convex
functions such that `dom fᵢ ⊇ ri C`. Then one and only one of the following alternatives holds:

(a) there exists some `x ∈ C` such that `f₁(x) < 0, …, f_m(x) < 0`;

(b) there exist non-negative real numbers `λ₁, …, λ_m`, not all zero, such that
`λ₁f₁(x) + ⋯ + λ_mf_m(x) ≥ 0` for every `x ∈ C`.

This is the disjunction; `theorem_21_1_exclusive` is the exclusivity. The hypothesis is
`ri C ⊆ dom fᵢ` and not `C ⊆ dom fᵢ` — see the module docstring — and the weighted sum is read in
`EReal`, where `0 · (+∞) = 0`.

Specialises `alternative_of_convex_system`. -/
theorem theorem_21_1 {ι : Type*} [Fintype ι] [Nonempty ι] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i))
    (hdom : ∀ i, ri C ⊆ dom (f i)) :
    (∃ x ∈ C, ∀ i, f i x < 0) ∨
      ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ l ≠ 0 ∧
        ∀ x ∈ C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x :=
  alternative_of_convex_system hC hf hp hdom

/-- **Rockafellar, Theorem 21.1**, the "only one" half: alternatives (a) and (b) cannot both hold.
No hypothesis on the `fᵢ` or on `C` is needed — at a point where every `fᵢ` is negative, every term
`λᵢfᵢ(x)` is non-positive and the terms with `λᵢ ≠ 0` are strictly negative.

Specialises `not_exists_forall_neg_of_forall_zero_le_weighted`. -/
theorem theorem_21_1_exclusive {ι : Type*} [Fintype ι] {C : Set (Rn n)} {f : ι → Rn n → EReal}
    {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i) (hl0 : l ≠ 0)
    (h : ∀ x ∈ C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x) :
    ¬ ∃ x ∈ C, ∀ i, f i x < 0 :=
  not_exists_forall_neg_of_forall_zero_le_weighted hl hl0 h

/-! ### Theorem 21.2 -/

/-- **Rockafellar, Theorem 21.2.** Let `C` be a convex set, let `f₁, …, f_k` be proper convex
functions with `dom fᵢ ⊇ ri C`, and let `f_{k+1}, …, f_m` be affine functions such that the system
`f_{k+1}(x) ≤ 0, …, f_m(x) ≤ 0` has at least one solution in `ri C`. Then one and only one of the
following alternatives holds:

(a) there exists `x ∈ C` with `f₁(x) < 0, …, f_k(x) < 0` and `f_{k+1}(x) ≤ 0, …, f_m(x) ≤ 0`;

(b) there exist non-negative `λ₁, …, λ_m` with at least one of `λ₁, …, λ_k` non-zero and
`λ₁f₁(x) + ⋯ + λ_mf_m(x) ≥ 0` for every `x ∈ C`.

The book cuts the range `1, …, m` at `k`; here the convex constraints are indexed by `ι` and the
affine ones by `κ`, and the affine constraints are `Rn n →ᵃ[ℝ] ℝ` rather than `EReal`-valued, which
is what "affine function" means. Theorem 21.1 is the case `κ = Empty`, but it is not derived from
this one: 21.1 needs only Theorem 11.3, while 21.2 needs the polyhedral separation of Theorem 20.2.

Specialises `alternative_of_convex_system_affine`. -/
theorem theorem_21_2 {ι κ : Type*} [Fintype ι] [Fintype κ] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} {a : κ → (Rn n →ᵃ[ℝ] ℝ)} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hp : ∀ i, Proper (f i)) (hdom : ∀ i, ri C ⊆ dom (f i))
    (hfeas : ∃ x ∈ ri C, ∀ j, a j x ≤ 0) :
    (∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0) ∨
      ∃ (l : ι → ℝ) (μ : κ → ℝ), (∀ i, 0 ≤ l i) ∧ (∀ j, 0 ≤ μ j) ∧ l ≠ 0 ∧
        ∀ x ∈ C, (0 : EReal)
          ≤ (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal) :=
  alternative_of_convex_system_affine hC hf hp hdom hfeas

/-- **Rockafellar, Theorem 21.2**, the "only one" half. At a point of `C` solving the mixed system,
the convex part of the weighted sum is strictly negative — that is Theorem 21.1's exclusivity
applied to the singleton `{x}` — and the affine part is non-positive, so the total is negative. -/
theorem theorem_21_2_exclusive {ι κ : Type*} [Fintype ι] [Fintype κ] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} {a : κ → (Rn n →ᵃ[ℝ] ℝ)} {l : ι → ℝ} {μ : κ → ℝ}
    (hl : ∀ i, 0 ≤ l i) (hμ : ∀ j, 0 ≤ μ j) (hl0 : l ≠ 0)
    (h : ∀ x ∈ C, (0 : EReal)
      ≤ (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal)) :
    ¬ ∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0 := by
  rintro ⟨x, hx, hneg, haff⟩
  have hconv : ¬ (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x := by
    intro hle
    refine not_exists_forall_neg_of_forall_zero_le_weighted (C := ({x} : Set (Rn n))) hl hl0
      (fun y hy => ?_) ⟨x, rfl, hneg⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hle
  have haffsum : (∑ j, μ j * a j x) ≤ 0 := by
    refine Finset.sum_nonpos fun j _ => ?_
    have h₁ := hμ j
    have h₂ := haff j
    nlinarith
  have hlt : (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal) < 0 := by
    calc (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal)
        ≤ (∑ i, (l i : EReal) * f i x) + 0 := by
          have h0 : ((∑ j, μ j * a j x : ℝ) : EReal) ≤ 0 := by exact_mod_cast haffsum
          exact add_le_add le_rfl h0
      _ = ∑ i, (l i : EReal) * f i x := add_zero _
      _ < 0 := not_le.1 hconv
  exact absurd (h x hx) (not_le.2 hlt)

/-! ### Theorem 21.3 and its corollaries -/

/-- **Rockafellar, Theorem 21.3.** Let `{fᵢ | i ∈ I}` be a collection of closed proper convex
functions on `ℝⁿ`, `I` an arbitrary index set, and let `C` be a non-empty closed convex set.
Assume the `fᵢ` have no common direction of recession which is also a direction of recession of
`C`. Then one and only one of the following alternatives holds:

(a) there is a vector `x ∈ C` with `fᵢ(x) ≤ 0` for every `i ∈ I`;

(b) there exist non-negative `λᵢ`, only finitely many non-zero, such that for some `ε > 0` one has
`∑ᵢ λᵢfᵢ(x) ≥ ε` for every `x ∈ C`.

If (b) holds, the `λᵢ` can be chosen so that at most `n + 1` of them are non-zero — the last clause
of the book's statement, carried here as `t.card ≤ n + 1`.

Specialises `alternative_infinite_system`. -/
theorem theorem_21_3 {ι : Type*} {C : Set (Rn n)} {f : ι → Rn n → EReal}
    (hf : ∀ i, ClosedProperConvexFn (f i)) (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hrec : ∀ y : Rn n, (∀ i, recessionFn (f i) y ≤ 0) → y ∈ recessionCone C → y = 0) :
    (∃ x ∈ C, ∀ i, f i x ≤ 0) ∨
      ∃ (t : Finset ι) (l : ι → ℝ) (ε : ℝ), (∀ i, 0 ≤ l i) ∧ (∀ i ∉ t, l i = 0) ∧ 0 < ε ∧
        t.card ≤ n + 1 ∧ ∀ x ∈ C, (ε : EReal) ≤ ∑ i ∈ t, (l i : EReal) * f i x := by
  simpa only [finrank_euclideanSpace_fin] using
    alternative_infinite_system (B := pairing n) hf hC hCc hCne hrec

/-- **Rockafellar, Theorem 21.3**, the "only one" half: at a solution of the weak system every term
`λᵢfᵢ(x)` is non-positive, so the sum cannot be bounded below by a positive `ε`. -/
theorem theorem_21_3_exclusive {ι : Type*} {C : Set (Rn n)} {f : ι → Rn n → EReal}
    {t : Finset ι} {l : ι → ℝ} {ε : ℝ} (hl : ∀ i, 0 ≤ l i) (hε : 0 < ε)
    (h : ∀ x ∈ C, (ε : EReal) ≤ ∑ i ∈ t, (l i : EReal) * f i x) :
    ¬ ∃ x ∈ C, ∀ i, f i x ≤ 0 := by
  rintro ⟨x, hx, hle⟩
  have hsum : ∑ i ∈ t, (l i : EReal) * f i x ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    calc (l i : EReal) * f i x
        ≤ (l i : EReal) * 0 := by
          refine mul_le_mul_of_nonneg_left (hle i) ?_
          exact_mod_cast hl i
      _ = 0 := by simp
  have hle0 : ((ε : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := by
    simpa using le_trans (h x hx) hsum
  exact absurd (EReal.coe_le_coe_iff.1 hle0) (not_le.2 hε)

/-- **Rockafellar, Corollary 21.3.1.** Under the recession hypothesis of Theorem 21.3, existence
for an infinite system reduces to existence for its finite subsystems: if for every `ε > 0` and
every set of `m ≤ n + 1` indices `i₁, …, i_m` the system `f_{i₁}(x) < ε, …, f_{i_m}(x) < ε` has a
solution in `C`, then there is an `x ∈ C` with `fᵢ(x) ≤ 0` for every `i ∈ I`.

Specialises `exists_forall_le_zero_of_forall_subsystem`. -/
theorem corollary_21_3_1 {ι : Type*} {C : Set (Rn n)} {f : ι → Rn n → EReal}
    (hf : ∀ i, ClosedProperConvexFn (f i)) (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hrec : ∀ y : Rn n, (∀ i, recessionFn (f i) y ≤ 0) → y ∈ recessionCone C → y = 0)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ S : Finset ι, S.card ≤ n + 1 →
      ∃ x ∈ C, ∀ i ∈ S, f i x < (ε : EReal)) :
    ∃ x ∈ C, ∀ i, f i x ≤ 0 := by
  refine exists_forall_le_zero_of_forall_subsystem (B := pairing n) hf hC hCc hCne hrec ?_
  simpa only [finrank_euclideanSpace_fin] using hsub

/-- **Rockafellar, Corollary 21.3.2 (Helly's Theorem).** Let `{Cᵢ | i ∈ I}` be a collection of
non-empty closed convex sets in `ℝⁿ`, `I` an arbitrary index set, and assume the `Cᵢ` have no
common direction of recession. If every subcollection consisting of `n + 1` or fewer sets has a
non-empty intersection, then the entire collection has a non-empty intersection.

The recession hypothesis cannot be dropped; the book's counterexample is discussed in the module
docstring. Compare `theorem_21_6`, where the collection is finite and neither closedness nor a
recession hypothesis is needed.

Specialises `helly_of_no_common_recession`. -/
theorem corollary_21_3_2 {ι : Type*} {K : ι → Set (Rn n)} (hconv : ∀ i, Convex ℝ (K i))
    (hcl : ∀ i, IsClosed (K i)) (hne : ∀ i, (K i).Nonempty)
    (hrec : ∀ y : Rn n, (∀ i, y ∈ recessionCone (K i)) → y = 0)
    (hinter : ∀ S : Finset ι, S.card ≤ n + 1 → (⋂ i ∈ S, K i).Nonempty) :
    (⋂ i, K i).Nonempty := by
  refine helly_of_no_common_recession (B := pairing n) hconv hcl hne hrec ?_
  simpa only [finrank_euclideanSpace_fin] using hinter

/-! ### Theorems 21.4 and 21.5: the polyhedral refinements -/

/-- The book's "`fᵢ` is an affine function", for a function that Rockafellar takes to be
`EReal`-valued and defined on all of `ℝⁿ`: `f(x) = ⟨x, b⟩ - β`.

`isAffineFn_iff_eq_affineFn` is the bridge to the backbone's `affineFn`, which is the same thing
written against a pairing. -/
def IsAffineFn (f : Rn n → EReal) : Prop :=
  ∃ (b : Rn n) (β : ℝ), ∀ x, f x = ((inner ℝ x b - β : ℝ) : EReal)

/-- The bridge lemma for `IsAffineFn`: an affine function of `ℝⁿ` in the book's sense is exactly an
`affineFn` of the standard pairing. -/
theorem isAffineFn_iff_eq_affineFn {f : Rn n → EReal} :
    IsAffineFn f ↔ ∃ (b : Rn n) (β : ℝ), f = affineFn (pairing n) b β := by
  constructor
  · rintro ⟨b, β, h⟩
    exact ⟨b, β, funext fun x => by rw [h x, affineFn_eq_coe, pairing_apply]⟩
  · rintro ⟨b, β, rfl⟩
    exact ⟨b, β, fun x => by rw [affineFn_eq_coe, pairing_apply]⟩

/-- **Rockafellar, Theorem 21.4.** The hypothesis about directions of recession in Theorem 21.3
and Corollary 21.3.1 may be replaced by the following weaker hypothesis if `C = ℝⁿ`: there exists a
finite subset `I₀` of `I` such that `fᵢ` is affine for each `i ∈ I₀`, and such that each direction
which is a direction of recession of `fᵢ` for every `i ∈ I` is actually a direction in which `fᵢ`
is constant for every `i ∈ I \ I₀`.

"Direction in which `fᵢ` is constant" is `constancySpace (f i)`. Compare `theorem_21_3`, whose
hypothesis is this one with `I₀ = ∅`, since `0` lies in every constancy space.

Specialises `alternative_infinite_system_univ_of_affine_tail`. -/
theorem theorem_21_4 {ι : Type*} {f : ι → Rn n → EReal} (hf : ∀ i, ClosedProperConvexFn (f i))
    (I₀ : Finset ι) (haff : ∀ i ∈ I₀, IsAffineFn (f i))
    (hrec : ∀ y : Rn n, (∀ i, recessionFn (f i) y ≤ 0) → ∀ i ∉ I₀, y ∈ constancySpace (f i)) :
    (∃ x : Rn n, ∀ i, f i x ≤ 0) ∨
      ∃ (t : Finset ι) (l : ι → ℝ) (ε : ℝ), (∀ i, 0 ≤ l i) ∧ (∀ i ∉ t, l i = 0) ∧ 0 < ε ∧
        t.card ≤ n + 1 ∧ ∀ x : Rn n, (ε : EReal) ≤ ∑ i ∈ t, (l i : EReal) * f i x := by
  have hB : (pairing n).SeparatingRight := by
    have h := separatingRight_flip_of_separatingDual (pairing n)
    rwa [flip_pairing] at h
  simpa only [finrank_euclideanSpace_fin] using
    alternative_infinite_system_univ_of_affine_tail (B := pairing n) hB hf I₀
      (fun i hi => isAffineFn_iff_eq_affineFn.1 (haff i hi)) hrec

/-- **Rockafellar, Theorem 21.4** for Corollary 21.3.1: under the affine-tail hypothesis, an
infinite system of weak convex inequalities on `ℝⁿ` is solvable as soon as every subsystem of at
most `n + 1` of the inequalities is solvable to within an arbitrarily small tolerance.

Specialises `exists_forall_le_zero_of_forall_subsystem_of_affine_tail`. -/
theorem theorem_21_4_subsystem {ι : Type*} {f : ι → Rn n → EReal}
    (hf : ∀ i, ClosedProperConvexFn (f i)) (I₀ : Finset ι) (haff : ∀ i ∈ I₀, IsAffineFn (f i))
    (hrec : ∀ y : Rn n, (∀ i, recessionFn (f i) y ≤ 0) → ∀ i ∉ I₀, y ∈ constancySpace (f i))
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ S : Finset ι, S.card ≤ n + 1 →
      ∃ x : Rn n, ∀ i ∈ S, f i x < (ε : EReal)) :
    ∃ x : Rn n, ∀ i, f i x ≤ 0 := by
  have hB : (pairing n).SeparatingRight := by
    have h := separatingRight_flip_of_separatingDual (pairing n)
    rwa [flip_pairing] at h
  refine exists_forall_le_zero_of_forall_subsystem_of_affine_tail (B := pairing n) hB hf I₀
    (fun i hi => isAffineFn_iff_eq_affineFn.1 (haff i hi)) hrec ?_
  simpa only [finrank_euclideanSpace_fin] using hsub

/-- **Rockafellar, Theorem 21.5.** The hypothesis in Helly's Theorem (Corollary 21.3.2) about
directions of recession may be replaced by the following weaker hypothesis: there exists a finite
subset `I₀` of `I` such that `Cᵢ` is polyhedral for every `i ∈ I₀`, and such that each direction
which is a direction of recession of `Cᵢ` for every `i ∈ I` is actually a direction in which `Cᵢ`
is linear for every `i ∈ I \ I₀`.

"Direction in which `Cᵢ` is linear" is `linealitySpace (K i)`.

Specialises `helly_of_polyhedral_tail`. -/
theorem theorem_21_5 {ι : Type*} {K : ι → Set (Rn n)} (hconv : ∀ i, Convex ℝ (K i))
    (hcl : ∀ i, IsClosed (K i)) (hne : ∀ i, (K i).Nonempty) (I₀ : Finset ι)
    (hpoly : ∀ i ∈ I₀, Polyhedral (K i))
    (hrec : ∀ y : Rn n, (∀ i, y ∈ recessionCone (K i)) → ∀ i ∉ I₀, y ∈ linealitySpace (K i))
    (hinter : ∀ S : Finset ι, S.card ≤ n + 1 → (⋂ i ∈ S, K i).Nonempty) :
    (⋂ i, K i).Nonempty := by
  have hB : (pairing n).SeparatingRight := by
    have h := separatingRight_flip_of_separatingDual (pairing n)
    rwa [flip_pairing] at h
  refine helly_of_polyhedral_tail (B := pairing n) hB hconv hcl hne I₀ hpoly hrec ?_
  simpa only [finrank_euclideanSpace_fin] using hinter

/-! ### Theorem 21.6 and its corollaries: finite collections -/

/-- **Rockafellar, Theorem 21.6.** Let `{Cᵢ | i ∈ I}` be a *finite* collection of convex sets in
`ℝⁿ` (not necessarily closed). If every subcollection consisting of `n + 1` or fewer sets has a
non-empty intersection, then the entire collection has a non-empty intersection.

Rockafellar derives this from Corollary 21.3.2 by replacing each `Cᵢ` with the convex hull of a
finite selection; the backbone takes Mathlib's route through Radon's theorem instead, which is why
`corollary_21_6_1` and `corollary_21_6_2` below do not depend on Theorem 21.3.

Specialises `helly_finite`. -/
theorem theorem_21_6 {ι : Type*} {K : ι → Set (Rn n)} {s : Finset ι}
    (hconv : ∀ i ∈ s, Convex ℝ (K i))
    (hinter : ∀ t ⊆ s, t.card ≤ n + 1 → (⋂ i ∈ t, K i).Nonempty) :
    (⋂ i ∈ s, K i).Nonempty := by
  refine helly_finite hconv ?_
  simpa only [finrank_euclideanSpace_fin] using hinter

/-- **Rockafellar, Corollary 21.6.1.** Given a system
`f₁(x) < 0, …, f_k(x) < 0, f_{k+1}(x) ≤ 0, …, f_m(x) ≤ 0` with all `fᵢ` convex on `ℝⁿ` (the
inequalities may be all strict or all weak): if every subsystem consisting of `n + 1` or fewer
inequalities has a solution in a given convex set `C`, then the system as a whole has a solution
in `C`.

The book's `1, …, k` is the index type `ι` and its `k+1, …, m` is `κ`, so "`n + 1` or fewer
inequalities" is `S.card + T.card ≤ n + 1`. Rockafellar's proof, verbatim: apply Theorem 21.6 to
`C` together with the level sets.

Specialises `exists_mem_of_forall_subsystem`. -/
theorem corollary_21_6_1 {ι κ : Type*} [Finite ι] [Finite κ] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} {g : κ → Rn n → EReal} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hg : ∀ j, ConvexFn (g j))
    (hsub : ∀ (S : Finset ι) (T : Finset κ), S.card + T.card ≤ n + 1 →
      ∃ x ∈ C, (∀ i ∈ S, f i x < 0) ∧ ∀ j ∈ T, g j x ≤ 0) :
    ∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, g j x ≤ 0 := by
  refine exists_mem_of_forall_subsystem hC hf hg ?_
  simpa only [finrank_euclideanSpace_fin] using hsub

/-- **Rockafellar, Corollary 21.6.2.** If alternative (b) holds in Theorem 21.1, the numbers `λᵢ`
can actually be chosen so that no more than `n + 1` of them differ from `0`.

The sparsity is stated as a `Finset` `S` of size at most `n + 1` outside which every `λᵢ` vanishes,
which avoids having to decide `λᵢ ≠ 0`. Extending a short multiplier vector by zeros is harmless
precisely because `0 · (+∞) = 0` in `EReal`.

**The book states this for Theorem 21.2 as well**; that half is `corollary_21_6_2_affine`, which
the backbone does not have and which is proved here from Corollary 21.6.1 and Theorem 21.2.

Specialises `sparse_alternative_of_convex_system`. -/
theorem corollary_21_6_2 {ι : Type*} [Fintype ι] [Nonempty ι] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i))
    (hdom : ∀ i, ri C ⊆ dom (f i)) :
    (∃ x ∈ C, ∀ i, f i x < 0) ∨
      ∃ (S : Finset ι) (l : ι → ℝ), S.card ≤ n + 1 ∧ (∀ i ∉ S, l i = 0) ∧
        (∀ i, 0 ≤ l i) ∧ l ≠ 0 ∧ ∀ x ∈ C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x := by
  simpa only [finrank_euclideanSpace_fin] using
    sparse_alternative_of_convex_system hC hf hp hdom

/-- A real affine function of `ℝⁿ`, read into `EReal`, is a convex function. This is what lets the
affine constraints of Theorem 21.2 enter Corollary 21.6.1's finite collection of convex sets. -/
theorem convexFn_coe_affineMap (g : Rn n →ᵃ[ℝ] ℝ) : ConvexFn (fun x => ((g x : ℝ) : EReal)) := by
  refine convexFn_of_epi_combo fun x y p q hx hy s t hs ht hst => ?_
  rw [_root_.EReal.coe_le_coe_iff] at hx hy ⊢
  rw [Convex.combo_affine_apply hst]
  simp only [smul_eq_mul]
  nlinarith

/-- **Rockafellar, Corollary 21.6.2** for **Theorem 21.2**: if alternative (b) holds there, the
`λ₁, …, λ_m` can be chosen so that no more than `n + 1` of them differ from `0` — the count running
over the affine multipliers as well as the convex ones, since the book's `λ₁, …, λ_m` is one list.

The book's proof, verbatim: if alternative (a) fails it already fails for a subsystem of at most
`n + 1` inequalities (Corollary 21.6.1, with the affine constraints read as the convex functions
`x ↦ ⟨aⱼ, x⟩ - αⱼ`), and Theorem 21.2 applied to that subsystem produces multipliers which extend
by zero. Unlike `corollary_21_6_2` there is no degenerate case to dispose of: an *empty* convex
part would make the subsystem solvable at the feasible point supplied by `hfeas`, contradicting
its selection. -/
theorem corollary_21_6_2_affine {ι κ : Type*} [Fintype ι] [Fintype κ] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} {a : κ → (Rn n →ᵃ[ℝ] ℝ)} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hp : ∀ i, Proper (f i)) (hdom : ∀ i, ri C ⊆ dom (f i))
    (hfeas : ∃ x ∈ ri C, ∀ j, a j x ≤ 0) :
    (∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0) ∨
      ∃ (S : Finset ι) (T : Finset κ) (l : ι → ℝ) (μ : κ → ℝ),
        S.card + T.card ≤ n + 1 ∧ (∀ i ∉ S, l i = 0) ∧ (∀ j ∉ T, μ j = 0) ∧
          (∀ i, 0 ≤ l i) ∧ (∀ j, 0 ≤ μ j) ∧ l ≠ 0 ∧
          ∀ x ∈ C, (0 : EReal)
            ≤ (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal) := by
  classical
  by_cases halt : ∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0
  · exact Or.inl halt
  refine Or.inr ?_
  have hsmall : ∃ (S : Finset ι) (T : Finset κ), S.card + T.card ≤ n + 1 ∧
      ¬ ∃ x ∈ C, (∀ i ∈ S, f i x < 0) ∧ ∀ j ∈ T, a j x ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ (S : Finset ι) (T : Finset κ), S.card + T.card ≤ n + 1 →
        ∃ x ∈ C, (∀ i ∈ S, f i x < 0) ∧ ∀ j ∈ T, ((a j x : ℝ) : EReal) ≤ 0 := by
      intro S T hST
      obtain ⟨x, hx, hxf, hxa⟩ := hcon S T hST
      exact ⟨x, hx, hxf, fun j hj => by exact_mod_cast hxa j hj⟩
    obtain ⟨x, hx, hxf, hxa⟩ :=
      corollary_21_6_1 (g := fun j x => ((a j x : ℝ) : EReal)) hC hf
        (fun j => convexFn_coe_affineMap (a j)) hsub
    exact halt ⟨x, hx, hxf, fun j => by exact_mod_cast hxa j⟩
  obtain ⟨S, T, hcard, hSalt⟩ := hsmall
  obtain ⟨y₀, hy₀, hy₀a⟩ := hfeas
  rcases theorem_21_2 (ι := ↥S) (κ := ↥T) (f := fun i : ↥S => f i) (a := fun j : ↥T => a j) hC
      (fun i => hf i) (fun i => hp i) (fun i => hdom i) ⟨y₀, hy₀, fun j => hy₀a j⟩ with
    ⟨x, hx, hxf, hxa⟩ | ⟨l', μ', hl'0, hμ'0, hl'ne, hl'⟩
  · exact absurd ⟨x, hx, fun i hi => hxf ⟨i, hi⟩, fun j hj => hxa ⟨j, hj⟩⟩ hSalt
  refine ⟨S, T, fun i => if h : i ∈ S then l' ⟨i, h⟩ else 0,
    fun j => if h : j ∈ T then μ' ⟨j, h⟩ else 0, hcard, fun i hi => by simp [hi],
    fun j hj => by simp [hj], ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i ∈ S
    · simpa [h] using hl'0 ⟨i, h⟩
    · simp [h]
  · intro j
    by_cases h : j ∈ T
    · simpa [h] using hμ'0 ⟨j, h⟩
    · simp [h]
  · intro hzero
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ↥S, l' i₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hl'ne (funext hcon)
    have h := congrFun hzero (i₀ : ι)
    simp only [i₀.2, Pi.zero_apply, Subtype.coe_eta, ↓reduceDIte] at h
    exact hi₀ h
  · intro x hx
    have hshrinkl : ∑ i, ((if h : i ∈ S then l' ⟨i, h⟩ else 0 : ℝ) : EReal) * f i x
        = ∑ i ∈ S, ((if h : i ∈ S then l' ⟨i, h⟩ else 0 : ℝ) : EReal) * f i x := by
      refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
      intro i _ hi
      simp [hi]
    have hshrinkm : ∑ j, (if h : j ∈ T then μ' ⟨j, h⟩ else 0 : ℝ) * a j x
        = ∑ j ∈ T, (if h : j ∈ T then μ' ⟨j, h⟩ else 0 : ℝ) * a j x := by
      refine (Finset.sum_subset (Finset.subset_univ T) ?_).symm
      intro j _ hj
      simp [hj]
    rw [hshrinkl, hshrinkm, ← Finset.sum_coe_sort S, ← Finset.sum_coe_sort T]
    have hcl : ∀ i : ↥S, ((if h : (i : ι) ∈ S then l' ⟨(i : ι), h⟩ else 0 : ℝ) : EReal)
        * f i x = (l' i : EReal) * f i x := by
      intro i
      simp only [i.2, Subtype.coe_eta, ↓reduceDIte]
    have hcm : ∀ j : ↥T, (if h : (j : κ) ∈ T then μ' ⟨(j : κ), h⟩ else 0 : ℝ) * a j x
        = μ' j * a j x := by
      intro j
      simp only [j.2, Subtype.coe_eta, ↓reduceDIte]
    rw [Finset.sum_congr rfl fun i _ => hcl i, Finset.sum_congr rfl fun j _ => hcm j]
    exact hl' x hx

end Rockafellar
