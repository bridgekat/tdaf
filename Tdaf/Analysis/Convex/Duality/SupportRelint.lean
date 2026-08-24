/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Support
import Tdaf.Analysis.Convex.RelativeInterior

/-!
# Relative interiors, interiors and affine hulls from the support function

The support function of a set records the closed half-spaces containing it, and therefore knows the
closed convex hull exactly: `x ∈ cl (conv s)` if and only if `⟨x, y⟩ ≤ δ*(y | s)` for every `y`
(`mem_closure_convexHull_iff_le_supportFn`, in `Tdaf/Analysis/Convex/Duality/Support.lean`). In
finite dimensions it knows more — the relative interior, the interior and the affine hull of a
convex set can all be read off from *which* of those inequalities are strict.

The dividing line is the set of directions in which the support function is **additively
reversible**, `-δ*(-y | C) = δ*(y | C)`. These are exactly the directions in which `⟨·, y⟩` is
constant on `C` (`neg_supportFn_neg_eq_iff`), i.e. the directions along which `C` lies inside a
hyperplane; no inequality can be strict there, and the three descriptions differ only in what they
ask of them: the relative interior asks for strictness everywhere else, the interior asks for
strictness in every direction but `0` — so there are no reversible directions to spare — and the
affine hull asks for equality in the reversible directions and nothing at all elsewhere.

## What is here

* `supportFn_eq_coe_of_forall_eq`, `supportFn_neg_eq_neg_iff`, `neg_supportFn_neg_eq_iff` — the
  reversible directions of a support function are its directions of constancy. Layer A.
* `exists_forall_eq_of_notMem_affineSpan` — a point off the affine hull is cut away from it by a
  direction in which the pairing is constant on the set.
* `mem_relint_iff_lt_supportFn` — **Rockafellar, Theorem 13.1**, the `ri` clause.
* `mem_interior_iff_lt_supportFn` — the same theorem's `int` clause.
* `mem_affineSpan_iff_eq_supportFn` — its `aff` clause, which is **Corollary 1.4.1**: the affine
  hull of a set is the intersection of the hyperplanes containing it.

## What is not here

The closure clause of Theorem 13.1 is `mem_closure_convexHull_iff_le_supportFn`, in
`Duality/Support.lean`. It is the one clause of the four that holds in any locally convex space, so
it stays in the light module; the three here are layer D.

## Design notes

### All three clauses are genuinely finite-dimensional

Let `φ` be a discontinuous linear functional and `C = ker φ`, a dense proper subspace. Then
`aff C = C` and `ri C = C` — the relative interior is taken inside `aff C`, which is `C` itself —
while `int C = ∅`. A continuous `⟨·, y⟩` constant on the dense set `C` is identically zero, so the
reversible directions of `δ*(· | C)` are exactly the `y` with `⟨·, y⟩ = 0`, and `δ*(y | C) = +∞` in
every other direction. All three conditions below are therefore satisfied by *every* point of the
space, and all three clauses fail. Finite-dimensionality enters through `Convex.relint_closure` and
`notMem_relint_iff_exists_isMaxOn` (Corollary 11.6.2) for the `ri` clause, through
`Convex.interior_nonempty_iff_affineSpan_eq_top` for the `int` clause, and through closedness of
affine subspaces for the `aff` clause.

### Two hypotheses the book does not write, both in the `int` clause

* **`B.SeparatingRight`.** Rockafellar identifies `Rⁿ` with its dual, where `y ≠ 0` and
  `⟨·, y⟩ ≠ 0` are the same condition. Over a pairing they are not: a `y ≠ 0` pairing trivially
  with all of `E` would demand `⟨x, y⟩ = 0 < δ*(y | C) = 0`, which no point of any nonempty `C`
  satisfies.
* **`C.Nonempty`.** For `C = ∅` the condition is *false* — `⟨x, y⟩ < -∞` never holds — as long as
  some `y ≠ 0` exists, which it does whenever `E ≠ 0`. Over the zero space it is vacuously true
  while `int ∅ = ∅`, so the book's statement fails there. Nonemptiness is the honest hypothesis,
  and the applications have it anyway.

### The `aff` clause needs no convexity

Corollary 1.4.1 is a statement about arbitrary sets, and the proof below never convexifies: a point
off `aff C` is separated from the *affine subspace* `aff C`, which is closed because the dimension
is finite. Only nonemptiness is needed, exactly as the book says.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §13 (Theorem 13.1) and
  §1 (Corollary 1.4.1).
-/

namespace Tdaf.ConvexAnalysis

/-! ### Directions of constancy -/

section Constancy

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Set E} {y : F}

/-- **The support function in a direction of constancy is that constant.** -/
theorem supportFn_eq_coe_of_forall_eq (hs : s.Nonempty) {c : ℝ} (h : ∀ x ∈ s, B x y = c) :
    supportFn B s y = ((c : ℝ) : EReal) := by
  obtain ⟨x₀, hx₀⟩ := hs
  refine le_antisymm (supportFn_le_coe_iff.2 fun x hx => (h x hx).le) ?_
  rw [← h x₀ hx₀]
  exact le_supportFn hx₀ y

/-- **A support function is additively reversible in the direction `y` exactly when `⟨·, y⟩` is
constant on the set.**

`δ*(-y | s) = -δ*(y | s)` says that the supremum and the infimum of `⟨·, y⟩` over `s` agree.
Nonemptiness of `s` is needed — for `s = ∅` both sides are `-∞` and `-(-∞) = +∞`. -/
theorem supportFn_neg_eq_neg_iff (hs : s.Nonempty) (y : F) :
    supportFn B s (-y) = -supportFn B s y ↔ ∃ c : ℝ, ∀ x ∈ s, B x y = c := by
  obtain ⟨x₀, hx₀⟩ := hs
  constructor
  · intro h
    have hbot : supportFn B s y ≠ ⊥ := supportFn_ne_bot ⟨x₀, hx₀⟩ y
    have hbot' : supportFn B s (-y) ≠ ⊥ := supportFn_ne_bot ⟨x₀, hx₀⟩ (-y)
    have htop : supportFn B s y ≠ ⊤ := by
      intro ht
      rw [ht, _root_.EReal.neg_top] at h
      exact hbot' h
    obtain ⟨c, hc⟩ :=
      Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top hbot (lt_top_iff_ne_top.2 htop)
    refine ⟨c, fun x hx => ?_⟩
    have h1 : B x y ≤ c := supportFn_le_coe_iff.1 hc.le x hx
    have h2 : B x (-y) ≤ -c := by
      refine supportFn_le_coe_iff.1 ?_ x hx
      rw [h, hc, ← _root_.EReal.coe_neg]
    rw [map_neg] at h2
    linarith
  · rintro ⟨c, hc⟩
    have hy : supportFn B s y = ((c : ℝ) : EReal) :=
      supportFn_eq_coe_of_forall_eq ⟨x₀, hx₀⟩ hc
    have hy' : supportFn B s (-y) = ((-c : ℝ) : EReal) :=
      supportFn_eq_coe_of_forall_eq ⟨x₀, hx₀⟩ fun x hx => by rw [map_neg, hc x hx]
    rw [hy, hy', _root_.EReal.coe_neg]

/-- `supportFn_neg_eq_neg_iff` in the orientation Theorem 13.1 uses:
`-δ*(-y | s) = δ*(y | s)`. -/
theorem neg_supportFn_neg_eq_iff (hs : s.Nonempty) (y : F) :
    -supportFn B s (-y) = supportFn B s y ↔ ∃ c : ℝ, ∀ x ∈ s, B x y = c := by
  rw [neg_eq_iff_eq_neg]
  exact supportFn_neg_eq_neg_iff hs y

end Constancy

/-! ### Theorem 13.1: the relative interior, the interior and the affine hull -/

section FiniteDim

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {C : Set E}

/-- **A point outside the affine hull is cut away from it by a direction of constancy**
(Rockafellar, Corollary 1.4.1): the affine hull of a nonempty set is the intersection of the
hyperplanes containing it.

The affine hull is closed because the dimension is finite, so a point outside it is strongly
separated from it; and a functional bounded below on an affine set is constant on it
(`eq_of_le_on_affineSubspace`), which turns the separation into a hyperplane. -/
theorem exists_forall_eq_of_notMem_affineSpan (hne : C.Nonempty) {x : E}
    (hx : x ∉ affineSpan ℝ C) :
    ∃ (y : F) (c : ℝ), (∀ z ∈ C, B z y = c) ∧ B x y ≠ c := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨g, u, v, hgx, huv, hgA⟩ := geometric_hahn_banach_compact_closed
    (convex_singleton x) isCompact_singleton (affineSpan ℝ C).convex
    (affineSpan ℝ C).closed_of_finiteDimensional (Set.disjoint_singleton_left.2 hx)
  obtain ⟨y, hy⟩ := exists_pairing_eq B g
  refine ⟨y, g p, fun z hz => ?_, ?_⟩
  · rw [← hy z]
    exact eq_of_le_on_affineSubspace (fun w hw => (hgA w hw).le)
      (subset_affineSpan ℝ C hz) (subset_affineSpan ℝ C hp)
  · rw [← hy x]
    have h₁ : g x < u := hgx x rfl
    have h₂ : v < g p := hgA p (subset_affineSpan ℝ C hp)
    exact ne_of_lt (by linarith)

/-- **Rockafellar, Theorem 13.1**, the `ri` clause: a point lies in the relative interior of a
convex set exactly when it satisfies every inequality the support function records, *strictly* in
every direction in which the support function is not additively reversible.

This is Corollary 11.6.2 (`notMem_relint_iff_exists_isMaxOn`) read through the pairing: the
inequality `⟨x, y⟩ ≤ δ*(y | C)` is an equality precisely when `⟨·, y⟩` attains its maximum over `C`
at `x`, and such a maximum is compatible with `x ∈ ri C` only for a `⟨·, y⟩` constant on `C`. -/
theorem mem_relint_iff_lt_supportFn (hC : Convex ℝ C) (x : E) :
    x ∈ ri C ↔ (∀ y : F, ((B x y : ℝ) : EReal) ≤ supportFn B C y) ∧
      ∀ y : F, -supportFn B C (-y) ≠ supportFn B C y →
        ((B x y : ℝ) : EReal) < supportFn B C y := by
  constructor
  · intro hx
    have hxC : x ∈ C := intrinsicInterior_subset hx
    refine ⟨fun y => le_supportFn hxC y, fun y hy => ?_⟩
    rcases lt_or_eq_of_le (le_supportFn (B := B) hxC y) with hlt | heq
    · exact hlt
    · exfalso
      have hmax : ∀ z ∈ C, evalCLM B y z ≤ evalCLM B y x := fun z hz => by
        simpa using supportFn_le_coe_iff.1 (le_of_eq heq.symm) z hz
      have hnc : ¬∃ c : ℝ, ∀ z ∈ C, B z y = c :=
        fun h => hy ((neg_supportFn_neg_eq_iff (B := B) ⟨x, hxC⟩ y).2 h)
      obtain ⟨z, hz, hzne⟩ : ∃ z ∈ C, B z y ≠ B x y := by
        by_contra hcon
        push Not at hcon
        exact hnc ⟨B x y, hcon⟩
      exact (notMem_relint_iff_exists_isMaxOn hC hxC).2
        ⟨evalCLM B y, hmax, z, hz, by simpa using hzne⟩ hx
  · rintro ⟨hle, hlt⟩
    have hxcl : x ∈ closure C := by
      have h := (mem_closure_convexHull_iff_le_supportFn (B := B) C x).2 hle
      rwa [hC.convexHull_eq] at h
    have hne : C.Nonempty := closure_nonempty_iff.1 ⟨x, hxcl⟩
    rw [← Convex.relint_closure hC]
    by_contra hnot
    obtain ⟨g, hmax, z, hz, hzne⟩ := (notMem_relint_iff_exists_isMaxOn hC.closure hxcl).1 hnot
    obtain ⟨y, hy⟩ := exists_pairing_eq B g
    have hsupp : supportFn B C y = ((g x : ℝ) : EReal) := by
      rw [← supportFn_closure (B := B) C]
      refine le_antisymm (supportFn_le_coe_iff.2 fun w hw => ?_) ?_
      · rw [← hy w]; exact hmax w hw
      · rw [hy x]; exact le_supportFn hxcl y
    obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ w ∈ C, B w y = c := by
      refine (neg_supportFn_neg_eq_iff (B := B) hne y).1 ?_
      by_contra hcon
      have hstrict := hlt y hcon
      rw [hsupp, ← hy x] at hstrict
      exact absurd hstrict (lt_irrefl _)
    have hclc : closure C ⊆ {w : E | B w y = c} :=
      closure_minimal (fun w hw => hc w hw)
        (isClosed_eq (continuous_pairing B y) continuous_const)
    have hz' : B z y = c := hclc hz
    have hx' : B x y = c := hclc hxcl
    exact hzne (by rw [hy z, hy x, hz', hx'])

/-- **Rockafellar, Theorem 13.1**, the `int` clause: a point lies in the interior of a nonempty
convex set exactly when it satisfies *strictly* every inequality the support function records in a
nonzero direction.

The relative interior is the interior exactly when the set lies in no hyperplane, i.e. when `0` is
the only reversible direction; asking for strictness in every nonzero direction is asking for
both at once. -/
theorem mem_interior_iff_lt_supportFn (hC : Convex ℝ C) (hne : C.Nonempty)
    (hB : B.SeparatingRight) (x : E) :
    x ∈ interior C ↔ ∀ y : F, y ≠ 0 → ((B x y : ℝ) : EReal) < supportFn B C y := by
  constructor
  · intro hx
    have htop : affineSpan ℝ C = ⊤ := hC.interior_nonempty_iff_affineSpan_eq_top.1 ⟨x, hx⟩
    have hri : x ∈ ri C := by rwa [intrinsicInterior_eq_interior htop]
    intro y hy
    refine ((mem_relint_iff_lt_supportFn (B := B) hC x).1 hri).2 y ?_
    intro hrev
    obtain ⟨c, hc⟩ := (neg_supportFn_neg_eq_iff (B := B) hne y).1 hrev
    have hmem : ∀ w : E, w ∈ affineSpan ℝ C := by
      intro w
      rw [htop]
      exact AffineSubspace.mem_top ℝ E w
    have hEqOn : Set.EqOn (B.flip y).toAffineMap (AffineMap.const ℝ E c) C := fun w hw => hc w hw
    have hall : ∀ w : E, B w y = c := fun w => by
      simpa using AffineMap.eqOn_affineSpan hEqOn (hmem w)
    have hc0 : c = 0 := by simpa using (hall 0).symm
    exact hy (hB y fun z => by rw [hall z, hc0])
  · intro h
    have htop : affineSpan ℝ C = ⊤ := by
      by_contra hcon
      obtain ⟨p, hp⟩ : ∃ p : E, p ∉ affineSpan ℝ C := by
        by_contra hall
        push Not at hall
        exact hcon (eq_top_iff.2 fun q _ => hall q)
      obtain ⟨y, c, hc, hpc⟩ := exists_forall_eq_of_notMem_affineSpan (B := B) hne hp
      obtain ⟨w, hw⟩ := hne
      have hy0 : y ≠ 0 := by
        rintro rfl
        have hc0 : c = 0 := by simpa using (hc w hw).symm
        exact hpc (by simp [hc0])
      have h₁ : B x y < c := by
        have hlt := h y hy0
        rw [supportFn_eq_coe_of_forall_eq (B := B) ⟨w, hw⟩ hc] at hlt
        exact_mod_cast hlt
      have h₂ : B x (-y) < -c := by
        have hlt := h (-y) (neg_ne_zero.2 hy0)
        rw [supportFn_eq_coe_of_forall_eq (B := B) ⟨w, hw⟩
          fun z hz => by rw [map_neg, hc z hz]] at hlt
        exact_mod_cast hlt
      rw [map_neg] at h₂
      linarith
    rw [← intrinsicInterior_eq_interior htop, mem_relint_iff_lt_supportFn (B := B) hC x]
    refine ⟨fun y => ?_, fun y hrev => ?_⟩
    · by_cases hy : y = 0
      · subst hy
        simp [supportFn_zero hne]
      · exact (h y hy).le
    · refine h y fun hy => ?_
      subst hy
      exact hrev (by simp [supportFn_zero hne])

/-- **Rockafellar, Theorem 13.1**, the `aff` clause — equivalently **Corollary 1.4.1**: the affine
hull of a nonempty set is the set of points that satisfy with equality every inequality the support
function records reversibly.

Convexity is not needed: the reversible directions of `δ*(· | C)` describe the hyperplanes
containing `C`, and the affine hull of any set is their intersection. -/
theorem mem_affineSpan_iff_eq_supportFn (hne : C.Nonempty) (x : E) :
    x ∈ affineSpan ℝ C ↔ ∀ y : F, -supportFn B C (-y) = supportFn B C y →
      ((B x y : ℝ) : EReal) = supportFn B C y := by
  constructor
  · intro hx y hrev
    obtain ⟨c, hc⟩ := (neg_supportFn_neg_eq_iff (B := B) hne y).1 hrev
    have hEqOn : Set.EqOn (B.flip y).toAffineMap (AffineMap.const ℝ E c) C := fun w hw => hc w hw
    have hxc : B x y = c := by simpa using AffineMap.eqOn_affineSpan hEqOn hx
    rw [hxc, supportFn_eq_coe_of_forall_eq (B := B) hne hc]
  · intro h
    by_contra hx
    obtain ⟨y, c, hc, hxc⟩ := exists_forall_eq_of_notMem_affineSpan (B := B) hne hx
    have hsupp : supportFn B C y = ((c : ℝ) : EReal) :=
      supportFn_eq_coe_of_forall_eq (B := B) hne hc
    have hrev : -supportFn B C (-y) = supportFn B C y :=
      (neg_supportFn_neg_eq_iff (B := B) hne y).2 ⟨c, hc⟩
    have heq := h y hrev
    rw [hsupp] at heq
    exact hxc (by exact_mod_cast heq)

end FiniteDim

end Tdaf.ConvexAnalysis
