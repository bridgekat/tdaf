/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Barrier
import Tdaf.Analysis.Convex.Polyhedral.Duality
import Tdaf.Analysis.Convex.Polyhedral.Separation

/-!
# Closedness of a sum with a polyhedral set

Rockafellar's Theorem 20.3 and Corollary 20.3.1. Corollary 9.1.1 keeps `C₁ + C₂` closed only when
every cancelling pair of recession directions lies in *both* lineality spaces; if `C₁` is
polyhedral, the requirement on the `C₁` side disappears.

## Main results

* `isClosed_add_of_polyhedral` — **Theorem 20.3**.
* `separatesStrongly_of_polyhedral_of_recession` — **Corollary 20.3.1**.
* `nonempty_dom_supportFn_inter_relint` — the constraint qualification Theorem 20.3 turns on,
  read off from Theorem 20.2 applied to the two barrier cones.

## Design notes

**The proof is Rockafellar's, with Corollary 20.2.1 replaced by Theorem 20.2 itself.** Rockafellar
translates the separation condition of Theorem 20.2 into support functions and then recognises the
support function of a barrier cone as the indicator of a recession cone (Corollary 14.2.1). Here
Theorem 20.2 is applied directly to the barrier cones `K₁ = dom δ*(· | C₁)` and
`K₂ = dom δ*(· | C₂)`: a separating functional is a point `v` of `E` (compatibility of the
pairing), and Corollary 14.2.1
turns the three conditions on it — nonpositive on `K₁`, nonnegative on `K₂`, not identically zero on
`K₂` — into `v ∈ 0⁺C₁`, `-v ∈ 0⁺C₂` and `v ∉ 0⁺C₂`. That is exactly a counterexample to the
hypothesis.

**Closedness is read off the effective domains, not from an infimal convolution formula.** Once
`IsExactSum.of_polyhedral` gives `(δ*(· | C₁) + δ*(· | C₂))* = δ(· | C₁) □ δ(· | C₂)`, the left side
is `δ(· | cl (C₁ + C₂))` by `conj_supportFn_of_convex` and the effective domain of the right side is
`C₁ + C₂` by `dom_infConv`. Comparing domains gives `cl (C₁ + C₂) = C₁ + C₂` with no computation of
the infimal convolution itself.

**The pairing is carried through Corollary 20.3.1 even though its statement does not mention it.**
Strong separation is stated over `E →L[ℝ] ℝ`, but the proof needs Theorem 20.3, which needs a
compatible pairing to speak about barrier cones.
-/

open Set
open scoped Pointwise

namespace Tdaf.ConvexAnalysis

section Closedness

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C₁ C₂ : Set E}

/-- The barrier cone of a polyhedral convex set is polyhedral: its support function is the
conjugate of a polyhedral indicator, hence polyhedral by **Theorem 19.2**, and the effective domain
of a polyhedral function is polyhedral by **Theorem 19.1**. -/
theorem polyhedral_dom_supportFn (h₁ : Polyhedral C₁) :
    Polyhedral (dom (supportFn B C₁)) := by
  have hfn : PolyhedralFn (supportFn B C₁) := by
    rw [supportFn_eq_conj_indicatorFn]
    exact PolyhedralFn.conj (B := B) (polyhedralFn_indicatorFn h₁)
  exact hfn.polyhedral_dom

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The barrier cone always contains the origin. -/
theorem zero_mem_dom_supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (hne : C₁.Nonempty) :
    (0 : F) ∈ dom (supportFn B C₁) := by
  rw [mem_dom, supportFn_zero hne]
  exact _root_.EReal.zero_lt_top

/-- **The constraint qualification of Theorem 20.3.** Under the recession hypothesis the barrier
cone of `C₁` meets the *relative interior* of the barrier cone of `C₂`.

This is where polyhedrality of `C₁` is spent: Theorem 20.2 says that the two barrier cones can
otherwise be separated by a hyperplane not containing the second one, and Corollary 14.2.1 reads
such a hyperplane as a recession direction violating the hypothesis. -/
theorem nonempty_dom_supportFn_inter_relint [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (h₁ : Polyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hcl₂ : IsClosed C₂) (hne₂ : C₂.Nonempty)
    (hrec : ∀ v ∈ recessionCone C₁, -v ∈ recessionCone C₂ → v ∈ recessionCone C₂) :
    (dom (supportFn B C₁) ∩ ri (dom (supportFn B C₂))).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hcon
  obtain ⟨ψ, γ, hsep, hns⟩ :=
    (exists_separates_not_subset_iff_disjoint_relint (polyhedral_dom_supportFn h₁)
      (convexFn_supportFn B C₂).convex_dom
      ⟨0, zero_mem_dom_supportFn B hne₂⟩).2 hcon
  have hγ : γ = 0 := by
    have hl : ψ 0 ≤ γ := hsep.le_of_mem_left (zero_mem_dom_supportFn B hne₁)
    have hr : γ ≤ ψ 0 := hsep.le_of_mem_right (zero_mem_dom_supportFn B hne₂)
    rw [map_zero] at hl hr
    linarith
  subst hγ
  obtain ⟨v, hv⟩ := exists_pairing_eq B.flip ψ
  have hv₁ : v ∈ recessionCone C₁ := by
    rw [← polarCone_dom_supportFn (B := B) h₁.convex h₁.isClosed hne₁]
    intro y hy
    have h := hsep.le_of_mem_left hy
    rw [hv y] at h
    exact h
  have hv₂ : -v ∈ recessionCone C₂ := by
    rw [← polarCone_dom_supportFn (B := B) h₂ hcl₂ hne₂]
    intro y hy
    have h := hsep.le_of_mem_right hy
    rw [hv y] at h
    have hneg : B.flip y (-v) = -(B.flip y v) := map_neg _ _
    rw [hneg]
    linarith
  have hv₃ : v ∉ recessionCone C₂ := by
    rw [← polarCone_dom_supportFn (B := B) h₂ hcl₂ hne₂]
    intro hmem
    refine hns fun y hy => ?_
    have h1 : B.flip y v ≤ 0 := hmem y hy
    have h2 := hsep.le_of_mem_right hy
    rw [hv y] at h2
    have h3 : ψ y = 0 := by rw [hv y]; linarith
    exact h3
  exact hv₃ (hrec v hv₁ hv₂)

/-- **Rockafellar, Theorem 20.3.** Let `C₁` be a nonempty polyhedral convex set and `C₂` a nonempty
closed convex set. If every direction of recession of `C₁` whose opposite recedes `C₂` is itself a
direction of recession of `C₂` — that is, a direction in which `C₂` is linear — then `C₁ + C₂` is
closed.

Corollary 9.1.1 (`Convex.isClosed_add`) asks in addition that such a direction lie in the lineality
space of `C₁`; polyhedrality of `C₁` removes that requirement. -/
theorem isClosed_add_of_polyhedral [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (h₁ : Polyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hcl₂ : IsClosed C₂) (hne₂ : C₂.Nonempty)
    (hrec : ∀ v ∈ recessionCone C₁, -v ∈ recessionCone C₂ → v ∈ recessionCone C₂) :
    IsClosed (C₁ + C₂) := by
  have : IsCompatiblePairing B.flip.flip := ‹IsCompatiblePairing B›
  obtain ⟨x₀, hx₀₁, hx₀₂⟩ :=
    nonempty_dom_supportFn_inter_relint (B := B) h₁ hne₁ h₂ hcl₂ hne₂ hrec
  have hfn₁ : PolyhedralFn (supportFn B C₁) := by
    rw [supportFn_eq_conj_indicatorFn]
    exact PolyhedralFn.conj (B := B) (polyhedralFn_indicatorFn h₁)
  have hexact : IsExactSum B.flip (supportFn B C₁) (supportFn B C₂) :=
    IsExactSum.of_polyhedral hfn₁ (proper_supportFn hne₁)
      ⟨convexFn_supportFn B C₂, closedFn_supportFn, proper_supportFn hne₂⟩ hx₀₁ hx₀₂
  have hL : conj B.flip (supportFn B C₁ + supportFn B C₂)
      = indicatorFn (closure (C₁ + C₂)) := by
    rw [← supportFn_add]
    exact conj_supportFn_of_convex (h₁.convex.add h₂)
  have hkey := hexact.conj_add
  rw [hL, conj_supportFn h₁.convex h₁.isClosed, conj_supportFn h₂ hcl₂] at hkey
  have hdom := congrArg dom hkey
  rw [dom_indicatorFn, dom_infConv, dom_indicatorFn, dom_indicatorFn] at hdom
  exact closure_eq_iff_isClosed.1 hdom

/-- **Rockafellar, Corollary 20.3.1.** Two disjoint sets, one polyhedral and the other closed, can
be separated *strongly* as soon as their only common direction of recession is one in which the
closed one is linear.

Compare Corollary 11.4.2, which asks that the two sets have no common direction of recession at
all, and Corollary 19.3.3, where both sets are polyhedral and no recession hypothesis is needed. -/
theorem separatesStrongly_of_polyhedral_of_recession [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip]
    (h₁ : Polyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hcl₂ : IsClosed C₂) (hne₂ : C₂.Nonempty) (hdisj : Disjoint C₁ C₂)
    (hrec : ∀ v ∈ recessionCone C₁, v ∈ recessionCone C₂ → -v ∈ recessionCone C₂) :
    ∃ (f : E →L[ℝ] ℝ) (c : ℝ), SeparatesStrongly f c C₁ C₂ := by
  refine (separatesStrongly_iff_zero_notMem_closure_sub h₁.convex h₂).2 ?_
  have hclosed : IsClosed (C₁ + (-C₂)) := by
    refine isClosed_add_of_polyhedral (B := B) h₁ hne₁ h₂.neg hcl₂.neg hne₂.neg ?_
    intro v hv₁ hv₂
    rw [recessionCone_neg, Set.mem_neg] at hv₂ ⊢
    rw [neg_neg] at hv₂
    exact hrec v hv₁ hv₂
  rw [sub_eq_add_neg, hclosed.closure_eq]
  rintro ⟨x, hx, y, hy, hxy⟩
  rw [Set.mem_neg] at hy
  have hxy' : x + y = 0 := hxy
  have hxe : x = -y := add_eq_zero_iff_eq_neg.1 hxy'
  exact Set.disjoint_left.1 hdisj hx (hxe ▸ hy)

end Closedness

end Tdaf.ConvexAnalysis
