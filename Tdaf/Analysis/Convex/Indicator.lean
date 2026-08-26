/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Epigraph

/-!
# Indicator functions

The indicator function `δ(· | s)` of a set, which is `0` on `s` and `+∞` off it. It is the device by
which every statement about convex *sets* becomes an instance of a statement about convex
*functions*; Rockafellar introduces it in §4 for exactly that purpose and uses it throughout.

## Main results

* `convexFn_indicatorFn` — `δ(· | s)` is convex iff `s` is convex.
* `indicatorFn_ne_bot` — indicator functions never take the value `⊥`.
* `dom_indicatorFn` — the effective domain of `δ(· | s)` is `s`.
* `indicatorFn_add`, `indicatorFn_finsetSum` — adding indicators intersects the sets, for two
  summands and for a `Finset` of them.
* `epi_indicatorFn` — the epigraph of `δ(· | s)` is the "half-cylinder" `s ×ˢ Ici 0`.
* `indicatorFn_vadd` — translating the set translates the indicator.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §4.
-/

open Set Pointwise

namespace Tdaf.ConvexAnalysis

section Basic

variable {E : Type*}

/-- The indicator function `δ(· | s)` of a set `s`: `0` on `s`, `⊤` off it. -/
noncomputable def indicatorFn (s : Set E) : E → EReal := restrict s (fun _ => 0)

@[simp] theorem indicatorFn_of_mem {s : Set E} {x : E} (hx : x ∈ s) : indicatorFn s x = 0 :=
  restrict_of_mem hx

@[simp] theorem indicatorFn_of_notMem {s : Set E} {x : E} (hx : x ∉ s) : indicatorFn s x = ⊤ :=
  restrict_of_notMem hx

theorem indicatorFn_ne_bot (s : Set E) (x : E) : indicatorFn s x ≠ ⊥ := by
  by_cases hx : x ∈ s <;> simp [hx]

@[simp] theorem dom_indicatorFn (s : Set E) : dom (indicatorFn s) = s := by
  ext x; by_cases hx : x ∈ s <;> simp [hx]

/-- **Adding indicators intersects the sets.** `0 + 0 = 0`, and `⊤` absorbs everything an
indicator can be. This is why every "intersection" corollary in the book — Cor 16.4.1's polar of
an intersection, Cor 23.8.1's normal cone to an intersection — is the indicator instance of a
statement about sums, with no side condition. -/
@[simp] theorem indicatorFn_add (s t : Set E) :
    indicatorFn s + indicatorFn t = indicatorFn (s ∩ t) := by
  funext x
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;>
    simp [Pi.add_apply, hs, ht]

/-- **The `m`-ary `indicatorFn_add`**: a finite sum of indicators is the indicator of the
intersection, `δ(· | C₁) + ⋯ + δ(· | Cₘ) = δ(· | C₁ ∩ ⋯ ∩ Cₘ)`, with no side condition and no
`s.Nonempty`: over the empty `Finset` both sides are the zero function, since `⋂ i ∈ ∅, C i` is
`univ`.

The point is the same as `indicatorFn_add`'s. Rockafellar's intersection corollaries for `m` sets
— Corollary 23.8.1's normal cone to `C₁ ∩ ⋯ ∩ Cₘ` — are the indicator instances of his `m`-ary
statements about sums, and it is the sum over a `Finset` that they need. -/
theorem indicatorFn_finsetSum {ι : Type*} (C : ι → Set E) (s : Finset ι) :
    ∑ i ∈ s, indicatorFn (C i) = indicatorFn (⋂ i ∈ s, C i) := by
  induction s using Finset.cons_induction with
  | empty => funext z; simp
  | cons i t hi ih =>
    rw [Finset.sum_cons, ih, indicatorFn_add]
    congr 1
    ext z
    simp [Finset.mem_cons]

/-- The epigraph of an indicator function is a "half-cylinder with cross-section `s`"
(Rockafellar §4). -/
theorem epi_indicatorFn (s : Set E) : epi (indicatorFn s) = s ×ˢ Ici (0 : ℝ) := by
  ext p
  by_cases hp : p.1 ∈ s <;> simp [epi, hp, EReal.coe_nonneg]

end Basic

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `δ(· | s)` is a convex function exactly when `s` is a convex set (Rockafellar §4). -/
@[simp] theorem convexFn_indicatorFn {s : Set E} : ConvexFn (indicatorFn s) ↔ Convex ℝ s := by
  constructor
  · intro h
    simpa using h.convex_dom
  · intro h
    refine ⟨?_⟩
    rw [epi_indicatorFn]
    exact h.prod (convex_Ici 0)

omit [Module ℝ E] in
/-- **Translating the set translates the indicator**: `δ(x | a + s) = δ(x - a | s)`. This is what
turns Rockafellar's normal form for a partial affine function, `δ(· | L + a) + ⟨·, a*⟩ + α`, into an
instance of the translation row of Theorem 12.3. -/
@[simp] theorem indicatorFn_vadd (a : E) (s : Set E) (x : E) :
    indicatorFn (a +ᵥ s) x = indicatorFn s (x - a) := by
  have hmem : x ∈ a +ᵥ s ↔ x - a ∈ s := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
  by_cases hx : x - a ∈ s
  · rw [indicatorFn_of_mem (hmem.2 hx), indicatorFn_of_mem hx]
  · rw [indicatorFn_of_notMem fun h => hx (hmem.1 h), indicatorFn_of_notMem hx]

omit [AddCommGroup E] [Module ℝ E] in
/-- Adding an indicator function restricts the effective domain (Rockafellar §5). -/
theorem restrict_eq_add_indicatorFn {s : Set E} {f : E → EReal} (hf : ∀ x, f x ≠ ⊥) :
    restrict s f = f + indicatorFn s := by
  funext x
  by_cases hx : x ∈ s
  · simp [hx]
  · simp only [restrict_of_notMem hx, Pi.add_apply, indicatorFn_of_notMem hx]
    exact (EReal.add_top_of_ne_bot (hf x)).symm

end Module

end Tdaf.ConvexAnalysis
