/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Tdaf.Analysis.Convex.Recession.Closedness
import Tdaf.Analysis.Convex.Separation
import Tdaf.Surface.Rockafellar.Part2.Section06

/-!
# Rockafellar, §11: Separation Theorems

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §11, pp. 95–101: the three notions of
separation, the fundamental separation construction, and supporting hyperplanes. All sixteen
numbered results are here, stated over `Rn n = ℝⁿ` in the book's own vocabulary — a hyperplane is
`{x | ⟨x, b⟩ = β}` with `b ≠ 0`, and separation is an inclusion of the two sets in the opposing
closed half-spaces — and closed by specialising the backbone.

## Contents

| label | declaration |
|---|---|
| Theorem 11.1 | `theorem_11_1_ab`, `theorem_11_1_c` |
| Theorem 11.2 | `theorem_11_2` |
| Theorem 11.3 | `theorem_11_3` |
| Theorem 11.4 | `theorem_11_4`, `theorem_11_4_closure` |
| Corollary 11.4.1 | `corollary_11_4_1` |
| Corollary 11.4.2 | `corollary_11_4_2` |
| Theorem 11.5 | `theorem_11_5` |
| Corollary 11.5.1 | `corollary_11_5_1` |
| Corollary 11.5.2 | `corollary_11_5_2` |
| Theorem 11.6 | `theorem_11_6` |
| Corollary 11.6.1 | `corollary_11_6_1` |
| Corollary 11.6.2 | `corollary_11_6_2` |
| Theorem 11.7 | `theorem_11_7`, `theorem_11_7'` |
| Corollary 11.7.1 | `corollary_11_7_1` |
| Corollary 11.7.2 | `corollary_11_7_2` |
| Corollary 11.7.3 | `corollary_11_7_3` |

## The section's definitions

* `Tdaf.Surface.linFn b` — the vector `b` read as the linear function `⟨·, b⟩`. It lives in the
  shared surface header, not here, because §13, §14 and §18 want it too. The book quantifies over
  vectors where the backbone quantifies over continuous linear functionals; `exists_linFn` says the
  two are the same quantification in `ℝⁿ`, and every statement below is stated over vectors.
* `Rockafellar.SeparatesRn b β C₁ C₂`, `SeparatesProperlyRn`, `SeparatesStrictlyRn`,
  `SeparatesStronglyRn` — the four notions of p. 95, each carrying `b ≠ 0` so that
  `{x | ⟨x, b⟩ = β}` really is a hyperplane (Theorem 1.3). `SeparatesStronglyRn` is written the way
  the book writes it, with `Cᵢ + εB` inside the *open* half-spaces; `separatesStronglyRn_iff` is
  the bridge to the backbone's gap definition, and is the substance of Theorem 11.1(c).
* `Rockafellar.SeparableProperly`, `SeparableStrongly` — "there exists a hyperplane separating `C₁`
  and `C₂` properly / strongly", which is what every numbered result of the section is about.
* `Rockafellar.IsSupportingHalfSpace b β C` — the supporting half-space of p. 99. The bridge to
  the backbone's `IsSupporting` is `isSupportingHalfSpace_iff`.

**Which set lies on which side.** Rockafellar's Theorem 11.1 puts `C₁` in the *upper* half-space
and `C₂` in the lower one, while the backbone's `Separates f c s t` puts `s` below and `t` above.
The definitions here therefore read `Separates (linFn b) β C₂ C₁`, so that the inequalities in
every statement are the book's. `separableProperly_iff_exists` and `separableStrongly_iff_exists`
are the bridges to the backbone's unordered `∃ f c` form, and they absorb the swap through
`SeparatesProperly.symm`.

## What is not here

* **The example of `C₁ = {(ξ₁, ξ₂) | ξ₁ > 0, ξ₂ ≥ ξ₁⁻¹}` and `C₂ = {(ξ₁, 0) | ξ₁ ≥ 0}`** (p. 97) —
  *omitted*. The unnumbered pair of disjoint closed convex sets in `ℝ²` that can be separated only
  by a hyperplane containing `C₂`, showing that "properly" cannot be strengthened in Theorem 11.3
  and that Theorem 11.4 is not implied by disjointness. It proves nothing used later, and
  transcribing it needs coordinate machinery for no return.
* **Strict separation** — *omitted*, exactly as in the book. `SeparatesStrictlyRn` is defined
  because p. 95 defines it; Rockafellar then numbers no result about it, and neither does this
  module.
* **The forward references of p. 98** (Corollary 19.3.3, Theorem 20.2, Corollary 20.3.1,
  Theorem 22.6, and the sharpening of Theorem 11.5 in Theorem 18.8) — *deferred by scope*: they
  are the polyhedral separation results and belong to their own sections.

## Where the book's hypotheses had to change

**Corollaries 11.5.2 and 11.7.3 need `C` non-empty.** The book's hypothesis is `C ≠ ℝⁿ` alone. In
`ℝ⁰` the empty set is a convex subset other than `ℝ⁰` and there is no non-zero `b` at all, so the
conclusion fails; every other §11 result carries Rockafellar's standing non-emptiness hypothesis
anyway. The backbone's versions of these two are stated with `closure C ≠ univ`, because they are
false in infinite dimensions; here `Convex.relint_closure` (Theorem 6.3) turns `C ≠ ℝⁿ` back into
that hypothesis, which is the book's own argument.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §11.
-/

open Set Pointwise

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

variable {n : ℕ}

/-! ### Vectors as linear functions

Rockafellar writes a hyperplane as `{x | ⟨x, b⟩ = β}` and quantifies over the vector `b`; the
backbone quantifies over a continuous linear functional. In `ℝⁿ` the two quantifications agree, and
`linFn` together with `exists_linFn` is the translation. Both live in
`Tdaf/Surface/Common/Euclidean.lean`, since §13, §14 and §18 want them too. -/

/-! ### The four notions of separation (p. 95) -/

/-- **Rockafellar, §11 (p. 95).** The hyperplane `H = {x | ⟨x, b⟩ = β}`, `b ≠ 0`, *separates* `C₁`
and `C₂`: `C₁` is contained in the closed half-space `{x | ⟨x, b⟩ ≥ β}` and `C₂` in the opposite
one.

Recorded through the backbone's `Separates`, whose two sets go in the other order. -/
def SeparatesRn (b : Rn n) (β : ℝ) (C₁ C₂ : Set (Rn n)) : Prop :=
  b ≠ 0 ∧ Separates (linFn b) β C₂ C₁

/-- **Rockafellar, §11 (p. 95).** `H` separates `C₁` and `C₂` *properly*: it separates them, and
they are not both actually contained in `H` itself. -/
def SeparatesProperlyRn (b : Rn n) (β : ℝ) (C₁ C₂ : Set (Rn n)) : Prop :=
  b ≠ 0 ∧ SeparatesProperly (linFn b) β C₂ C₁

/-- **Rockafellar, §11 (p. 95).** `H` separates `C₁` and `C₂` *strictly*: the two sets belong to
opposing *open* half-spaces. The book defines this notion and then numbers no result about it. -/
def SeparatesStrictlyRn (b : Rn n) (β : ℝ) (C₁ C₂ : Set (Rn n)) : Prop :=
  b ≠ 0 ∧ (∀ x ∈ C₂, pairing n x b < β) ∧ ∀ x ∈ C₁, β < pairing n x b

/-- **Rockafellar, §11 (p. 95).** `H` separates `C₁` and `C₂` *strongly*: for some `ε > 0`,
`C₁ + εB` is contained in one of the open half-spaces associated with `H` and `C₂ + εB` in the
opposite one, where `B` is the closed Euclidean unit ball.

This is the book's own definition, verbatim; `separatesStronglyRn_iff` identifies it with the
backbone's gap definition, which is condition (c) of Theorem 11.1. -/
def SeparatesStronglyRn (b : Rn n) (β : ℝ) (C₁ C₂ : Set (Rn n)) : Prop :=
  b ≠ 0 ∧ ∃ ε > 0, (∀ x ∈ C₂ + Metric.closedBall (0 : Rn n) ε, pairing n x b < β) ∧
    ∀ x ∈ C₁ + Metric.closedBall (0 : Rn n) ε, β < pairing n x b

/-- **The bridge for `SeparatesStronglyRn`**: the book's `εB` definition is the backbone's gap
`⨆_{C₂} ⟨·, b⟩ < β < ⨅_{C₁} ⟨·, b⟩`. Specialises `separatesStrongly_iff_exists_closedBall`. -/
theorem separatesStronglyRn_iff {b : Rn n} {β : ℝ} {C₁ C₂ : Set (Rn n)} :
    SeparatesStronglyRn b β C₁ C₂ ↔ b ≠ 0 ∧ SeparatesStrongly (linFn b) β C₂ C₁ := by
  simp only [SeparatesStronglyRn, separatesStrongly_iff_exists_closedBall, linFn_apply]

/-- **Rockafellar, §11.** `C₁` and `C₂` can be separated *properly*: some hyperplane does it. -/
def SeparableProperly (C₁ C₂ : Set (Rn n)) : Prop :=
  ∃ (b : Rn n) (β : ℝ), SeparatesProperlyRn b β C₁ C₂

/-- **Rockafellar, §11.** `C₁` and `C₂` can be separated *strongly*: some hyperplane does it. -/
def SeparableStrongly (C₁ C₂ : Set (Rn n)) : Prop :=
  ∃ (b : Rn n) (β : ℝ), SeparatesStronglyRn b β C₁ C₂

/-- **The bridge to the backbone for proper separability.** Rockafellar's "there exists a
hyperplane separating `C₁` and `C₂` properly" is the backbone's
`∃ f c, SeparatesProperly f c C₁ C₂`: the side-swap is `SeparatesProperly.symm` and `b ≠ 0` is
`SeparatesProperly.ne_zero`. -/
theorem separableProperly_iff_exists {C₁ C₂ : Set (Rn n)} (h₁ : C₁.Nonempty) (h₂ : C₂.Nonempty) :
    SeparableProperly C₁ C₂ ↔ ∃ (f : Rn n →L[ℝ] ℝ) (c : ℝ), SeparatesProperly f c C₁ C₂ := by
  constructor
  · rintro ⟨b, β, -, hsep⟩
    exact ⟨-linFn b, -β, hsep.symm⟩
  · rintro ⟨f, c, hsep⟩
    obtain ⟨b, hb⟩ := exists_linFn (-f)
    have hb0 : b ≠ 0 := by
      intro hzero
      have hz : linFn b = 0 := linFn_eq_zero_iff.2 hzero
      rw [hb, neg_eq_zero] at hz
      exact hsep.ne_zero h₁ h₂ hz
    exact ⟨b, -c, hb0, by rw [hb]; exact hsep.symm⟩

/-- **The bridge to the backbone for strong separability**, exactly as for proper separability. -/
theorem separableStrongly_iff_exists {C₁ C₂ : Set (Rn n)} (h₁ : C₁.Nonempty) (h₂ : C₂.Nonempty) :
    SeparableStrongly C₁ C₂ ↔ ∃ (f : Rn n →L[ℝ] ℝ) (c : ℝ), SeparatesStrongly f c C₁ C₂ := by
  constructor
  · rintro ⟨b, β, hsep⟩
    rw [separatesStronglyRn_iff] at hsep
    exact ⟨-linFn b, -β, hsep.2.symm⟩
  · rintro ⟨f, c, hsep⟩
    obtain ⟨b, hb⟩ := exists_linFn (-f)
    have hb0 : b ≠ 0 := by
      intro hzero
      have hz : linFn b = 0 := linFn_eq_zero_iff.2 hzero
      rw [hb, neg_eq_zero] at hz
      exact hsep.ne_zero h₁ h₂ hz
    exact ⟨b, -c, separatesStronglyRn_iff.2 ⟨hb0, by rw [hb]; exact hsep.symm⟩⟩

/-- Strong separation passes to subsets: shrinking the sets only shrinks the two extrema. The
backbone has `Separates.mono` but not this one. -/
theorem separatesStrongly_mono {f : Rn n →L[ℝ] ℝ} {c : ℝ} {s t s' t' : Set (Rn n)}
    (h : SeparatesStrongly f c s t) (hs : s' ⊆ s) (ht : t' ⊆ t) : SeparatesStrongly f c s' t' :=
  ⟨lt_of_le_of_lt (iSup₂_le fun _ hx => coe_apply_le_iSup₂ (hs hx)) h.iSup_lt,
    lt_of_lt_of_le h.lt_iInf (le_iInf₂ fun _ hx => iInf₂_le_coe_apply (ht hx))⟩

/-! ### Theorem 11.1 -/

/-- **Rockafellar, Theorem 11.1**, conditions (a) and (b). Let `C₁` and `C₂` be non-empty sets in
`ℝⁿ`. There exists a hyperplane separating `C₁` and `C₂` properly if and only if there exists a
vector `b` such that

(a) `inf {⟨x, b⟩ | x ∈ C₁} ≥ sup {⟨x, b⟩ | x ∈ C₂}`, and
(b) `sup {⟨x, b⟩ | x ∈ C₁} > inf {⟨x, b⟩ | x ∈ C₂}`.

The extrema are taken in `EReal`, which removes the boundedness side conditions the book leaves
implicit. Specialises `exists_separatesProperly_iff_iSup_le_iInf`. -/
theorem theorem_11_1_ab {C₁ C₂ : Set (Rn n)} (h₁ : C₁.Nonempty) (h₂ : C₂.Nonempty) :
    SeparableProperly C₁ C₂ ↔ ∃ b : Rn n,
      (⨆ x ∈ C₂, ((pairing n x b : ℝ) : EReal)) ≤ ⨅ x ∈ C₁, ((pairing n x b : ℝ) : EReal) ∧
        (⨅ x ∈ C₂, ((pairing n x b : ℝ) : EReal)) < ⨆ x ∈ C₁, ((pairing n x b : ℝ) : EReal) := by
  constructor
  · rintro ⟨b, β, -, hsep⟩
    exact ⟨b, by
      simpa only [linFn_apply] using (exists_separatesProperly_iff_iSup_le_iInf h₂ h₁).1 ⟨β, hsep⟩⟩
  · rintro ⟨b, hb⟩
    obtain ⟨β, hβ⟩ := (exists_separatesProperly_iff_iSup_le_iInf (f := linFn b) h₂ h₁).2
      (by simpa only [linFn_apply] using hb)
    exact ⟨b, β, linFn_eq_zero_iff.not.1 (hβ.ne_zero h₂ h₁), hβ⟩

/-- **Rockafellar, Theorem 11.1**, condition (c). There exists a hyperplane separating the
non-empty sets `C₁` and `C₂` strongly if and only if there exists a vector `b` such that

(c) `inf {⟨x, b⟩ | x ∈ C₁} > sup {⟨x, b⟩ | x ∈ C₂}`.

Specialises `exists_separatesStrongly_iff_iSup_lt_iInf`; the passage from Rockafellar's `εB`
definition to this gap is `separatesStronglyRn_iff`, which is the substance of his proof. -/
theorem theorem_11_1_c {C₁ C₂ : Set (Rn n)} (h₁ : C₁.Nonempty) (h₂ : C₂.Nonempty) :
    SeparableStrongly C₁ C₂ ↔ ∃ b : Rn n,
      (⨆ x ∈ C₂, ((pairing n x b : ℝ) : EReal)) < ⨅ x ∈ C₁, ((pairing n x b : ℝ) : EReal) := by
  constructor
  · rintro ⟨b, β, hsep⟩
    rw [separatesStronglyRn_iff] at hsep
    exact ⟨b, by
      simpa only [linFn_apply] using exists_separatesStrongly_iff_iSup_lt_iInf.1 ⟨β, hsep.2⟩⟩
  · rintro ⟨b, hb⟩
    obtain ⟨β, hβ⟩ := (exists_separatesStrongly_iff_iSup_lt_iInf (f := linFn b) (s := C₂)
      (t := C₁)).2 (by simpa only [linFn_apply] using hb)
    exact ⟨b, β, separatesStronglyRn_iff.2 ⟨linFn_eq_zero_iff.not.1 (hβ.ne_zero h₂ h₁), hβ⟩⟩

/-! ### Theorem 11.2, the fundamental construction -/

/-- **Rockafellar, Theorem 11.2.** Let `C` be a non-empty relatively open convex set in `ℝⁿ`, and
let `M` be a non-empty affine set in `ℝⁿ` not meeting `C`. Then there exists a hyperplane `H`
containing `M`, such that one of the open half-spaces associated with `H` contains `C`.

The backbone has this only for *open* `C` (`exists_separates_of_isOpen_of_disjoint_affine`) and, in
the relatively open form, only for `M` a single point (`exists_lt_of_notMem_relint`). The step from
the point case to a general affine `M` is here: `C + M.direction` misses the base point of `M`, so
the point case applies to it, and a functional bounded above on a coset of `M.direction` is
constant along it (`eq_of_le_on_affineSubspace`). Strictness on `C` is Corollary 11.6.2
(`notMem_relint_iff_exists_isMaxOn`) applied inside `ri C = C`. -/
theorem theorem_11_2 {C M : Set (Rn n)} (hC : Convex ℝ C) (hCne : C.Nonempty)
    (hCo : IsRelativelyOpen C) (hM : IsAffineSet M) (hMne : M.Nonempty)
    (hdisj : Disjoint C M) :
    ∃ (b : Rn n) (β : ℝ), b ≠ 0 ∧ (∀ x ∈ M, pairing n x b = β) ∧ ∀ x ∈ C, pairing n x b < β := by
  obtain ⟨p, hp⟩ := hMne
  obtain ⟨c₀, hc₀⟩ := hCne
  set A := hM.toAffineSubspace with hA
  set W := A.direction with hW
  have hpA : p ∈ A := hp
  set D : Set (Rn n) := C + (W : Set (Rn n)) with hD
  have hCD : C ⊆ D := fun x hx => Set.mem_add.2 ⟨x, hx, 0, W.zero_mem, add_zero x⟩
  have hDconv : Convex ℝ D := hC.add W.convex
  have hpD : p ∉ D := by
    intro hmem
    obtain ⟨c, hc, w, hw, hcw⟩ := Set.mem_add.1 hmem
    have hcM : c ∈ M := by
      have hmem' : (-w) +ᵥ p ∈ A := AffineSubspace.vadd_mem_of_mem_direction (W.neg_mem hw) hpA
      have hce : (-w) +ᵥ p = c := by rw [vadd_eq_add, ← hcw]; abel
      rwa [hce] at hmem'
    exact Set.disjoint_left.1 hdisj hc hcM
  obtain ⟨g, hgle, x₁, hx₁, hglt⟩ :=
    exists_lt_of_notMem_relint hDconv ⟨c₀, hCD hc₀⟩ fun hmem => hpD (intrinsicInterior_subset hmem)
  have hgW : ∀ w ∈ W, g w = 0 := by
    intro w hw
    have hsub : ∀ y ∈ AffineSubspace.mk' c₀ W, -(g p) ≤ (-g) y := by
      intro y hy
      have hyW : y -ᵥ c₀ ∈ W := by
        simpa [AffineSubspace.direction_mk'] using
          AffineSubspace.vsub_mem_direction hy (AffineSubspace.self_mem_mk' c₀ W)
      have hyD : y ∈ D := Set.mem_add.2 ⟨c₀, hc₀, y - c₀, by simpa using hyW, by abel⟩
      simpa using neg_le_neg (hgle y hyD)
    have hw' : w +ᵥ c₀ ∈ AffineSubspace.mk' c₀ W :=
      AffineSubspace.vadd_mem_of_mem_direction
        (by simpa [AffineSubspace.direction_mk'] using hw) (AffineSubspace.self_mem_mk' c₀ W)
    have heq := eq_of_le_on_affineSubspace (f := -g) hsub hw' (AffineSubspace.self_mem_mk' c₀ W)
    simp only [neg_apply, vadd_eq_add, map_add] at heq
    linarith
  have hgC : ∀ x ∈ C, g x ≤ g p := fun x hx => hgle x (hCD hx)
  obtain ⟨c₁, hc₁, hc₁lt⟩ : ∃ c ∈ C, g c < g p := by
    obtain ⟨c, hc, w, hw, hcw⟩ := Set.mem_add.1 hx₁
    refine ⟨c, hc, ?_⟩
    have hsum : g c + g w = g x₁ := by rw [← map_add, hcw]
    rw [hgW w hw, add_zero] at hsum
    rw [hsum]
    exact hglt
  have hgstrict : ∀ x ∈ C, g x < g p := by
    intro x hx
    rcases lt_or_eq_of_le (hgC x hx) with h | h
    · exact h
    · exfalso
      have hnot : x ∉ ri C := (notMem_relint_iff_exists_isMaxOn hC hx).2
        ⟨g, fun y hy => by rw [h]; exact hgC y hy, c₁, hc₁, by rw [h]; exact hc₁lt.ne⟩
      rw [hCo] at hnot
      exact hnot hx
  obtain ⟨b, hb⟩ := exists_linFn g
  refine ⟨b, g p, ?_, ?_, ?_⟩
  · intro hb0
    subst hb0
    have hg0 : g = 0 := by rw [← hb]; exact linFn_eq_zero_iff.2 rfl
    rw [hg0] at hc₁lt
    simp at hc₁lt
  · intro x hx
    have hxW : x -ᵥ p ∈ W := AffineSubspace.vsub_mem_direction hx hpA
    have hgx : g (x - p) = 0 := hgW _ (by simpa using hxW)
    rw [map_sub, sub_eq_zero] at hgx
    rw [← linFn_apply b x, hb]
    exact hgx
  · intro x hx
    rw [← linFn_apply b x, hb]
    exact hgstrict x hx

/-! ### Theorem 11.3, the main separation theorem -/

/-- **Rockafellar, Theorem 11.3.** Let `C₁` and `C₂` be non-empty convex sets in `ℝⁿ`. In order
that there exist a hyperplane separating `C₁` and `C₂` properly, it is necessary and sufficient
that `ri C₁` and `ri C₂` have no point in common.

Specialises `exists_separatesProperly_iff_disjoint_relint`. -/
theorem theorem_11_3 {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    SeparableProperly C₁ C₂ ↔ ri C₁ ∩ ri C₂ = ∅ := by
  rw [separableProperly_iff_exists hne₁ hne₂,
    exists_separatesProperly_iff_disjoint_relint h₁ h₂ hne₁ hne₂, Set.disjoint_iff_inter_eq_empty]

/-! ### Theorem 11.4 and its corollaries -/

/-- **Rockafellar, Theorem 11.4**, in the second of the two forms he gives it: strong separation of
two non-empty convex sets is possible exactly when `0 ∉ cl (C₁ - C₂)`.

Specialises `separatesStrongly_iff_zero_notMem_closure_sub`. -/
theorem theorem_11_4_closure {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    SeparableStrongly C₁ C₂ ↔ (0 : Rn n) ∉ closure (C₁ - C₂) := by
  rw [separableStrongly_iff_exists hne₁ hne₂,
    separatesStrongly_iff_zero_notMem_closure_sub h₁ h₂]

/-- **Rockafellar, Theorem 11.4.** Let `C₁` and `C₂` be non-empty convex sets in `ℝⁿ`. In order
that there exist a hyperplane separating `C₁` and `C₂` strongly, it is necessary and sufficient
that `inf {|x₁ - x₂| | x₁ ∈ C₁, x₂ ∈ C₂} > 0`.

`theorem_11_4_closure` is the same statement written as `0 ∉ cl (C₁ - C₂)`, which is the form the
backbone proves; a positive infimum of `|x₁ - x₂|` is exactly a ball around the origin missing
`C₁ - C₂`. -/
theorem theorem_11_4 {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    SeparableStrongly C₁ C₂ ↔ ∃ ε > 0, ∀ x₁ ∈ C₁, ∀ x₂ ∈ C₂, ε ≤ ‖x₁ - x₂‖ := by
  rw [theorem_11_4_closure h₁ h₂ hne₁ hne₂]
  constructor
  · intro h
    rw [Metric.mem_closure_iff] at h
    push Not at h
    obtain ⟨ε, hε, hball⟩ := h
    refine ⟨ε, hε, fun x₁ hx₁ x₂ hx₂ => ?_⟩
    have hd := hball _ (Set.sub_mem_sub hx₁ hx₂)
    rwa [dist_zero_left] at hd
  · rintro ⟨ε, hε, hsep⟩ hmem
    rw [Metric.mem_closure_iff] at hmem
    obtain ⟨y, hy, hylt⟩ := hmem ε hε
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Set.mem_sub.1 hy
    rw [dist_zero_left] at hylt
    exact absurd (hsep x₁ hx₁ x₂ hx₂) (not_le.2 hylt)

/-- **Rockafellar, Corollary 11.4.1.** Let `C₁` and `C₂` be non-empty disjoint closed convex sets
in `ℝⁿ` having no common directions of recession. Then there exists a hyperplane separating `C₁`
and `C₂` strongly.

Rockafellar's proof verbatim: `0 ∉ C₁ - C₂` by disjointness, and `cl (C₁ - C₂) = C₁ - C₂` by
Corollary 9.1.2 (`Convex.isClosed_add_of_neg_notMem_recessionCone`) applied to `C₁` and `-C₂`,
whose recession cone is `-0⁺C₂` (`recessionCone_neg`). -/
theorem corollary_11_4_1 {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (hc₁ : IsClosed C₁)
    (hne₁ : C₁.Nonempty) (h₂ : Convex ℝ C₂) (hc₂ : IsClosed C₂) (hne₂ : C₂.Nonempty)
    (hdisj : Disjoint C₁ C₂) (hrec : recessionCone C₁ ∩ recessionCone C₂ ⊆ {0}) :
    SeparableStrongly C₁ C₂ := by
  have hkey : ∀ z ∈ recessionCone C₁, -z ∈ recessionCone (-C₂) → z = 0 := by
    intro z hz hnz
    rw [recessionCone_neg, Set.mem_neg, neg_neg] at hnz
    exact hrec ⟨hz, hnz⟩
  have hclosed : IsClosed (C₁ + -C₂) :=
    Convex.isClosed_add_of_neg_notMem_recessionCone h₁ hc₁ hne₁ h₂.neg hc₂.neg hne₂.neg hkey
  rw [← sub_eq_add_neg] at hclosed
  rw [theorem_11_4_closure h₁ h₂ hne₁ hne₂, hclosed.closure_eq]
  intro hmem
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_sub.1 hmem
  rw [sub_eq_zero] at hxy
  exact Set.disjoint_left.1 hdisj hx (hxy ▸ hy)

/-- **Rockafellar, Corollary 11.4.2.** Let `C₁` and `C₂` be non-empty convex sets in `ℝⁿ` whose
closures are disjoint. If either set is bounded, there exists a hyperplane separating `C₁` and `C₂`
strongly.

Specialises `separatesStrongly_of_disjoint_isCompact_isClosed` and its mirror: a bounded closed set
in `ℝⁿ` is compact. The book instead deduces this from Corollary 11.4.1. -/
theorem corollary_11_4_2 {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) (hdisj : Disjoint (closure C₁) (closure C₂))
    (hbdd : Bornology.IsBounded C₁ ∨ Bornology.IsBounded C₂) :
    SeparableStrongly C₁ C₂ := by
  rw [separableStrongly_iff_exists hne₁ hne₂]
  obtain ⟨f, c, hsep⟩ : ∃ (f : Rn n →L[ℝ] ℝ) (c : ℝ),
      SeparatesStrongly f c (closure C₁) (closure C₂) := by
    rcases hbdd with hb | hb
    · exact separatesStrongly_of_disjoint_isCompact_isClosed h₁.closure
        (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure)
        h₂.closure isClosed_closure hdisj
    · exact separatesStrongly_of_disjoint_isClosed_isCompact h₁.closure isClosed_closure
        h₂.closure (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure) hdisj
  exact ⟨f, c, separatesStrongly_mono hsep subset_closure subset_closure⟩

/-! ### Theorem 11.5 and its corollaries -/

/-- **Rockafellar, Theorem 11.5.** A closed convex set `C` is the intersection of the closed
half-spaces which contain it.

Specialises `isClosed_convex_eq_iInter_halfspaces`, reindexed over vectors by `exists_linFn`. The
degenerate index `b = 0` is harmless: `{x | ⟨x, 0⟩ ≤ β}` is `ℝⁿ` whenever `β ≥ 0`, which is the
only case in which it contains a non-empty `C`. -/
theorem theorem_11_5 {C : Set (Rn n)} (hC : Convex ℝ C) (hCc : IsClosed C) :
    ⋂ (b : Rn n) (β : ℝ) (_ : ∀ y ∈ C, pairing n y b ≤ β),
      {x : Rn n | pairing n x b ≤ β} = C := by
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [mem_iff_forall_le_halfSpace hC hCc]
  constructor
  · intro h f c hf
    obtain ⟨b, rfl⟩ := exists_linFn f
    simp only [linFn_apply] at hf ⊢
    exact h b c hf
  · intro h b c hb
    simpa only [linFn_apply] using h (linFn b) c (by simpa only [linFn_apply] using hb)

/-- **Rockafellar, Corollary 11.5.1.** Let `S` be any subset of `ℝⁿ`. Then `cl (conv S)` is the
intersection of all the closed half-spaces containing `S`.

Specialises `closure_convexHull_eq_iInter_halfspaces`. -/
theorem corollary_11_5_1 (S : Set (Rn n)) :
    ⋂ (b : Rn n) (β : ℝ) (_ : ∀ y ∈ S, pairing n y b ≤ β), {x : Rn n | pairing n x b ≤ β} =
      closure (convexHull ℝ S) := by
  rw [← closure_convexHull_eq_iInter_halfspaces S]
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h f c hf
    obtain ⟨b, rfl⟩ := exists_linFn f
    simp only [linFn_apply] at hf ⊢
    exact h b c hf
  · intro h b c hb
    simpa only [linFn_apply] using h (linFn b) c (by simpa only [linFn_apply] using hb)

/-- **Rockafellar, Corollary 11.5.2.** Let `C` be a convex subset of `ℝⁿ` other than `ℝⁿ` itself.
Then there exists a closed half-space containing `C`; in other words, there exists some `b ∈ ℝⁿ`,
`b ≠ 0`, such that the linear function `⟨·, b⟩` is bounded above on `C`.

`C.Nonempty` is added to the book's hypotheses — see the module docstring. The book's step
`cl C ≠ ℝⁿ` is `Convex.relint_closure`, Theorem 6.3. Specialises
`exists_ne_zero_forall_le_of_closure_ne_univ`. -/
theorem corollary_11_5_2 {C : Set (Rn n)} (hC : Convex ℝ C) (hne : C.Nonempty)
    (h : C ≠ Set.univ) : ∃ (b : Rn n) (β : ℝ), b ≠ 0 ∧ ∀ x ∈ C, pairing n x b ≤ β := by
  have hcl : closure C ≠ Set.univ := by
    intro hcl
    refine h (Set.eq_univ_of_univ_subset ?_)
    have hri : ri C = Set.univ := by rw [← Convex.relint_closure hC, hcl, intrinsicInterior_univ]
    rw [← hri]
    exact intrinsicInterior_subset
  obtain ⟨f, c, hf0, hf⟩ := exists_ne_zero_forall_le_of_closure_ne_univ hC hne hcl
  obtain ⟨b, rfl⟩ := exists_linFn f
  exact ⟨b, c, linFn_eq_zero_iff.not.1 hf0, by simpa only [linFn_apply] using hf⟩

/-! ### Theorem 11.6, supporting hyperplanes -/

/-- **Rockafellar, §11 (p. 99).** A *supporting half-space* to `C` is a closed half-space
`{x | ⟨x, b⟩ ≤ β}`, `b ≠ 0`, which contains `C` and has a point of `C` in its boundary. The
boundary `{x | ⟨x, b⟩ = β}` is then a *supporting hyperplane* to `C`. -/
def IsSupportingHalfSpace (b : Rn n) (β : ℝ) (C : Set (Rn n)) : Prop :=
  b ≠ 0 ∧ (∀ x ∈ C, pairing n x b ≤ β) ∧ ∃ x ∈ C, pairing n x b = β

/-- **The bridge for `IsSupportingHalfSpace`**: it is the backbone's `IsSupporting` for the
functional `⟨·, b⟩`. -/
theorem isSupportingHalfSpace_iff {b : Rn n} {β : ℝ} {C : Set (Rn n)} :
    IsSupportingHalfSpace b β C ↔ IsSupporting (linFn b) β C := by
  constructor
  · rintro ⟨hb, hle, hex⟩
    exact ⟨linFn_eq_zero_iff.not.2 hb, fun x hx => by simpa only [linFn_apply] using hle x hx,
      by simpa only [linFn_apply] using hex⟩
  · rintro ⟨hb, hle, hex⟩
    exact ⟨linFn_eq_zero_iff.not.1 hb, fun x hx => by simpa only [linFn_apply] using hle hx,
      by simpa only [linFn_apply] using hex⟩

/-- **Rockafellar, Theorem 11.6.** Let `C` be a convex set, and let `D` be a non-empty convex
subset of `C`. In order that there exist a non-trivial supporting hyperplane to `C` containing `D`,
it is necessary and sufficient that `D` be disjoint from `ri C`.

The backbone's `exists_isSupporting_iff_disjoint_interior` is the `interior` version, which needs
`(interior C).Nonempty`; the `ri` version is proved here the way the book proves it — a non-trivial
supporting hyperplane to `C` through `D` is the same thing as a proper separation of `D` and `C`,
and `ri D ⊆ D` makes Theorem 11.3's hypothesis follow from the book's. -/
theorem theorem_11_6 {C D : Set (Rn n)} (hC : Convex ℝ C) (hD : Convex ℝ D) (hDC : D ⊆ C)
    (hDne : D.Nonempty) :
    (∃ (b : Rn n) (β : ℝ), IsSupportingHalfSpace b β C ∧ (∀ x ∈ D, pairing n x b = β) ∧
      ∃ x ∈ C, pairing n x b ≠ β) ↔ D ∩ ri C = ∅ := by
  obtain ⟨d₀, hd₀⟩ := hDne
  constructor
  · rintro ⟨b, β, ⟨-, hle, -⟩, hDβ, y, hy, hyne⟩
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have hxC : x ∈ C := hDC hx.1
    refine (notMem_relint_iff_exists_isMaxOn hC hxC).2 ⟨linFn b, fun z hz => ?_, y, hy, ?_⟩ hx.2
    · simp only [linFn_apply, hDβ x hx.1]
      exact hle z hz
    · simpa only [linFn_apply, hDβ x hx.1] using hyne
  · intro hdisj
    have hri : ri D ∩ ri C = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx =>
        Set.eq_empty_iff_forall_notMem.1 hdisj x ⟨intrinsicInterior_subset hx.1, hx.2⟩
    obtain ⟨b, β, hb, hsep⟩ := (theorem_11_3 hD hC ⟨d₀, hd₀⟩ ⟨d₀, hDC hd₀⟩).2 hri
    have hCle : ∀ x ∈ C, pairing n x b ≤ β := fun x hx => by
      simpa only [linFn_apply] using hsep.le_of_mem_left hx
    have hDeq : ∀ x ∈ D, pairing n x b = β := fun x hx =>
      le_antisymm (hCle x (hDC hx)) (by simpa only [linFn_apply] using hsep.le_of_mem_right hx)
    obtain ⟨y, hy, hyne⟩ : ∃ y ∈ C, pairing n y b ≠ β := by
      by_contra hcon
      push Not at hcon
      refine hsep.not_subset fun z hz => ?_
      rcases hz with hz | hz
      · simpa only [Set.mem_ofPred_eq, linFn_apply] using hcon z hz
      · simpa only [Set.mem_ofPred_eq, linFn_apply] using hDeq z hz
    exact ⟨b, β, ⟨hb, hCle, d₀, hDC hd₀, hDeq d₀ hd₀⟩, hDeq, y, hy, hyne⟩

/-- **Rockafellar, Corollary 11.6.1.** A convex set has a non-zero normal at each of its boundary
points.

Rockafellar's normal to `C` at `x` is the backbone's `normalCone (pairing n) C x`. Specialises
`exists_ne_zero_isMaxOn_of_mem_frontier`. -/
theorem corollary_11_6_1 {C : Set (Rn n)} (hC : Convex ℝ C) {x : Rn n} (hx : x ∈ C)
    (hfr : x ∈ frontier C) : ∃ b ∈ normalCone (pairing n) C x, b ≠ 0 := by
  obtain ⟨g, hg0, hg⟩ := exists_ne_zero_isMaxOn_of_mem_frontier hC hx hfr
  obtain ⟨b, rfl⟩ := exists_linFn g
  refine ⟨b, fun z hz => ?_, linFn_eq_zero_iff.not.1 hg0⟩
  have hzx := hg z hz
  simp only [linFn_apply] at hzx
  simp only [map_sub, LinearMap.sub_apply, sub_nonpos]
  exact hzx

/-- **Rockafellar, Corollary 11.6.2.** Let `C` be a convex set. An `x ∈ C` is a relative boundary
point of `C` if and only if there exists a linear function `h` not constant on `C` such that `h`
achieves its maximum over `C` at `x`.

Specialises `notMem_relint_iff_exists_isMaxOn`; `relbd` is §6's relative boundary. -/
theorem corollary_11_6_2 {C : Set (Rn n)} (hC : Convex ℝ C) {x : Rn n} (hx : x ∈ C) :
    x ∈ relbd C ↔ ∃ b : Rn n, (∀ y ∈ C, pairing n y b ≤ pairing n x b) ∧
      ∃ y ∈ C, pairing n y b ≠ pairing n x b := by
  rw [mem_relbd_iff, notMem_relint_iff_exists_isMaxOn hC hx]
  simp only [subset_closure hx, true_and]
  constructor
  · rintro ⟨g, hle, y, hy, hne⟩
    obtain ⟨b, rfl⟩ := exists_linFn g
    exact ⟨b, by simpa only [linFn_apply] using hle, y, hy, by simpa only [linFn_apply] using hne⟩
  · rintro ⟨b, hle, y, hy, hne⟩
    exact ⟨linFn b, by simpa only [linFn_apply] using hle, y, hy,
      by simpa only [linFn_apply] using hne⟩

/-! ### Theorem 11.7, cones and homogeneous half-spaces -/

/-- **Rockafellar, Theorem 11.7.** Let `C₁` and `C₂` be non-empty subsets of `ℝⁿ`, at least one of
which is a cone. If there exists a hyperplane which separates `C₁` and `C₂` properly, then there
exists a hyperplane which separates `C₁` and `C₂` properly *and passes through the origin*.

Stated with the cone on the `C₂` side; `SeparatesProperlyRn b 0 C₁ C₂` says the separating
hyperplane is `{x | ⟨x, b⟩ = 0}`, which contains the origin. Specialises
`SeparatesProperly.zero_of_isCone_left`. -/
theorem theorem_11_7 {C₁ C₂ : Set (Rn n)} (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty)
    (hcone : IsCone C₂) (h : SeparableProperly C₁ C₂) :
    ∃ b : Rn n, SeparatesProperlyRn b 0 C₁ C₂ := by
  obtain ⟨b, β, hb, hsep⟩ := h
  exact ⟨b, hb, hsep.zero_of_isCone_left (fun _ ha _ hx => hcone _ ha _ hx) hne₂ hne₁⟩

/-- **Rockafellar, Theorem 11.7**, with the cone on the `C₁` side. -/
theorem theorem_11_7' {C₁ C₂ : Set (Rn n)} (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty)
    (hcone : IsCone C₁) (h : SeparableProperly C₁ C₂) :
    ∃ b : Rn n, SeparatesProperlyRn b 0 C₁ C₂ := by
  obtain ⟨b, β, hb, hsep⟩ := h
  exact ⟨b, hb, hsep.zero_of_isCone_right (fun _ ha _ hx => hcone _ ha _ hx) hne₂ hne₁⟩

/-- **Rockafellar, Corollary 11.7.1.** A non-empty closed convex cone in `ℝⁿ` is the intersection
of the homogeneous closed half-spaces which contain it, a homogeneous half-space being one with the
origin on its boundary.

Specialises `isClosed_convex_isCone_eq_iInter_halfSpaceCone`. -/
theorem corollary_11_7_1 {K : Set (Rn n)} (hconv : Convex ℝ K) (hcone : IsCone K)
    (hcl : IsClosed K) (hne : K.Nonempty) :
    ⋂ (b : Rn n) (_ : ∀ y ∈ K, pairing n y b ≤ 0), {x : Rn n | pairing n x b ≤ 0} = K := by
  refine Eq.trans ?_ (isClosed_convex_isCone_eq_iInter_halfSpaceCone hconv
    (fun _ ha _ hx => hcone _ ha _ hx) hcl hne)
  ext x
  simp only [Set.mem_iInter, coe_halfSpaceCone, Set.mem_ofPred_eq]
  constructor
  · intro h f hf
    obtain ⟨b, rfl⟩ := exists_linFn f
    simp only [linFn_apply] at hf ⊢
    exact h b hf
  · intro h b hb
    simpa only [linFn_apply] using h (linFn b) (by simpa only [linFn_apply] using hb)

/-- **Rockafellar, Corollary 11.7.2.** Let `S` be any subset of `ℝⁿ`, and let `K` be the closure of
the convex cone generated by `S`. Then `K` is the intersection of all the homogeneous closed
half-spaces containing `S`.

The cone generated by `S` is `PointedCone.hull ℝ S`, which contains the origin. Rockafellar's own
proof needs that ("a homogeneous closed half-space is in particular a closed convex cone containing
the origin"), so no generality is lost. Specialises `closure_hull_eq_iInter_halfSpaceCone`. -/
theorem corollary_11_7_2 (S : Set (Rn n)) :
    ⋂ (b : Rn n) (_ : ∀ y ∈ S, pairing n y b ≤ 0), {x : Rn n | pairing n x b ≤ 0} =
      closure (PointedCone.hull ℝ S : Set (Rn n)) := by
  rw [← closure_hull_eq_iInter_halfSpaceCone S]
  ext x
  simp only [Set.mem_iInter, coe_halfSpaceCone, Set.mem_ofPred_eq]
  constructor
  · intro h f hf
    obtain ⟨b, rfl⟩ := exists_linFn f
    simp only [linFn_apply] at hf ⊢
    exact h b hf
  · intro h b hb
    simpa only [linFn_apply] using h (linFn b) (by simpa only [linFn_apply] using hb)

/-- **Rockafellar, Corollary 11.7.3.** Let `K` be a convex cone in `ℝⁿ` other than `ℝⁿ` itself.
Then `K` is contained in some homogeneous closed half-space of `ℝⁿ`; in other words, there exists
some vector `b ≠ 0` such that `⟨x, b⟩ ≤ 0` for every `x ∈ K`.

`K.Nonempty` is added to the book's hypotheses, exactly as in Corollary 11.5.2. Specialises
`exists_ne_zero_forall_le_zero_of_closure_ne_univ`. -/
theorem corollary_11_7_3 {K : Set (Rn n)} (hconv : Convex ℝ K) (hcone : IsCone K)
    (hne : K.Nonempty) (h : K ≠ Set.univ) :
    ∃ b : Rn n, b ≠ 0 ∧ ∀ x ∈ K, pairing n x b ≤ 0 := by
  have hcl : closure K ≠ Set.univ := by
    intro hcl
    refine h (Set.eq_univ_of_univ_subset ?_)
    have hri : ri K = Set.univ := by
      rw [← Convex.relint_closure hconv, hcl, intrinsicInterior_univ]
    rw [← hri]
    exact intrinsicInterior_subset
  obtain ⟨f, hf0, hf⟩ := exists_ne_zero_forall_le_zero_of_closure_ne_univ hconv
    (fun _ ha _ hx => hcone _ ha _ hx) hne hcl
  obtain ⟨b, rfl⟩ := exists_linFn f
  exact ⟨b, linFn_eq_zero_iff.not.1 hf0, by simpa only [linFn_apply] using hf⟩

end Rockafellar
