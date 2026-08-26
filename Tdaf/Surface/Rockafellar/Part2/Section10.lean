/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Continuity
import Tdaf.Analysis.Convex.Convergence
import Tdaf.Analysis.Convex.Operations.Basic
import Tdaf.Analysis.Convex.Simplicial
import Tdaf.Surface.Common.Euclidean

/-!
# Rockafellar, §10: Continuity of Convex Functions

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §10, pp. 82–94: the situations in which a
convex function is automatically upper semicontinuous, hence continuous, together with the
equi-Lipschitz and convergence theory that follows from them. Every numbered result of the section
is here, stated in the book's own terms over `Rn n = ℝⁿ` and closed by specialising the backbone.

The section is entirely finite-dimensional: all thirteen results are coordinate-bound, and each one
rests on Theorem 6.2 (`ri C ≠ ∅` for non-empty convex `C`) somewhere below.

## Contents

| label | declaration |
|---|---|
| Theorem 10.1 | `theorem_10_1` |
| Corollary 10.1.1 | `corollary_10_1_1` |
| Theorem 10.2 | `theorem_10_2`, `theorem_10_2_closed` |
| Theorem 10.3 | `theorem_10_3`, `theorem_10_3_unique` |
| Theorem 10.4 | `theorem_10_4` |
| Theorem 10.5 | `theorem_10_5`, `theorem_10_5_lipschitzian` |
| Corollary 10.5.1 | `corollary_10_5_1` |
| Corollary 10.5.2 | `corollary_10_5_2` |
| Theorem 10.6 | `theorem_10_6`, `theorem_10_6_ab` |
| Theorem 10.7 | `theorem_10_7`, `theorem_10_7_dense` |
| Theorem 10.8 | `theorem_10_8` |
| Corollary 10.8.1 | `corollary_10_8_1` |
| Theorem 10.9 | `theorem_10_9` |

## The section's definitions

* **Continuity relative to `S`** (p. 82) is `ContinuousOn f S`; Mathlib's
  `continuousOn_iff_continuous_domRestrict` identifies it with continuity of the restriction, which
  is the book's own phrasing. Recorded here as `continuousOn_iff_continuous_restrict_rn`.
* **Locally simplicial** (p. 84) is the backbone's `LocallySimplicial`, transcribed from the book
  without change: a finite union of simplices contained in `S` that agrees with `S` near each
  point.
* **Lipschitzian relative to `S`** (p. 86) is `LipschitzianOn`, with the bridge
  `lipschitzianOn_iff` to `∃ K : ℝ≥0, LipschitzOnWith K f S`.
* **Equi-Lipschitzian relative to `S`** (p. 88) is `EquiLipschitzianOn`, with the bridge
  `equiLipschitzianOn_iff` to a single `K` serving the whole family.
* **Pointwise bounded** and **uniformly bounded on `S`** (p. 88) are `PointwiseBoundedOn` and
  `UniformlyBoundedOn`, with the bridges `pointwiseBoundedOn_iff` and `uniformlyBoundedOn_iff` to
  the `BddBelow`/`BddAbove` and `|f i x| ≤ M` shapes the backbone takes as hypotheses.

## The gap the book leaves, and where it went

Theorem 10.2's proof triangulates a simplex around an interior point, a step Rockafellar calls
"intuitively obvious" (p. 84) and never proves; Theorem 20.5, which is supposed to supply the
same kind of fact for polyhedra, is also a sketch. **The backbone does not need the triangulation
at all.** `Simplicial.lean` proves upper semicontinuity relative to a simplex at *every* point of
it, not only at a vertex, by a direct barycentric estimate: for a fixed `ε` chosen in advance,
every point whose weights satisfy `wᵢ ≥ (1 - ε) μᵢ` is `(1 - ε) x + ε y` with `y` still in the
simplex, and affine independence makes that a neighbourhood condition by compactness. Rockafellar's
vertex case is `μ = eᵢ₀`. So `theorem_10_2` below is unconditional, and §20 inherits no obligation
from §10 — `Polyhedral.locallySimplicial` (Theorem 20.5) is proved on its own terms.

## What is not here

* **The parabolic counterexample of p. 83** — *omitted*. The book's unnumbered illustration that a
  closed convex function on `ℝ²` can fail to be continuous at a relative boundary point of its
  domain when approached tangentially. It motivates Theorem 10.2 but proves nothing used later, and
  the support-function computation it turns on is a §13 statement.
* **The three worked examples after Corollary 10.1.1** (`sup` over a parameter set, the infimum of
  `f` over a translate `C + x`, the non-decreasing convex function on the positive orthant) —
  *omitted*. Each is Corollary 10.1.1 or Theorem 10.3 applied to a function built by §5 operations;
  none is a numbered result.
* **The instance `g x = α‖x‖ + β` of Corollary 10.5.2** — *omitted*. A parenthetical in the book's
  statement, not part of it.
* **`liminf` is spelled as a `Frequently`** in `corollary_10_5_1`. Rockafellar writes
  `liminf_{λ → ∞} f (λ y) / λ < ∞`; over `EReal` that quotient needs a division convention the
  backbone deliberately has no need of, so the hypothesis is the equivalent "for some `c`, `f (a y)
  ≤ c a` for arbitrarily large `a`". The book's own proof of the corollary is the observation that
  the quotient is nondecreasing in `λ` (Theorem 8.5), which is exactly what makes the two forms
  agree.
* **Hypothesis (a) of Theorem 10.6 is stated with `cl C'`, not `conv (cl C')`** — *deferred by
  scope*, and see the friction note below. The backbone has the convex-hull weakening
  (`bddAbove_range_of_subset_convexHull_closure`) only in the `interior` form, not in the `ri` form
  that this section needs.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §10.
-/

open Filter Topology
open scoped NNReal

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

/-! ### The definitions of §10 -/

/-- **Continuity relative to `S`** (Rockafellar, §10, p. 82): the restriction of `f` to `S` is a
continuous function. This is `ContinuousOn`, and the identification is Mathlib's. -/
theorem continuousOn_iff_continuous_restrict_rn {n : ℕ} (f : Rn n → EReal) (S : Set (Rn n)) :
    ContinuousOn f S ↔ Continuous (S.domRestrict f) :=
  continuousOn_iff_continuous_domRestrict

/-- **Lipschitzian relative to `S`** (Rockafellar, §10, p. 86): a real-valued function `f` on
`S ⊆ ℝⁿ` for which there is a single `α ≥ 0` with `|f y - f x| ≤ α ‖y - x‖` for all `x, y ∈ S`. -/
def LipschitzianOn {n : ℕ} (f : Rn n → ℝ) (S : Set (Rn n)) : Prop :=
  ∃ α : ℝ, 0 ≤ α ∧ ∀ y ∈ S, ∀ x ∈ S, |f y - f x| ≤ α * ‖y - x‖

/-- **Equi-Lipschitzian relative to `S`** (Rockafellar, §10, p. 88): one `α ≥ 0` serves every
member of the family. -/
def EquiLipschitzianOn {n : ℕ} {ι : Type*} (f : ι → Rn n → ℝ) (S : Set (Rn n)) : Prop :=
  ∃ α : ℝ, 0 ≤ α ∧ ∀ i, ∀ y ∈ S, ∀ x ∈ S, |f i y - f i x| ≤ α * ‖y - x‖

/-- **Pointwise bounded on `S`** (Rockafellar, §10, p. 88): the set of real numbers `f i x`,
`i ∈ I`, is bounded for each `x ∈ S`. -/
def PointwiseBoundedOn {n : ℕ} {ι : Type*} (f : ι → Rn n → ℝ) (S : Set (Rn n)) : Prop :=
  ∀ x ∈ S, Bornology.IsBounded (Set.range fun i => f i x)

/-- **Uniformly bounded on `S`** (Rockafellar, §10, p. 88): `α₁ ≤ f i x ≤ α₂` for all `x ∈ S` and
all `i ∈ I`, with `α₁` and `α₂` independent of both. -/
def UniformlyBoundedOn {n : ℕ} {ι : Type*} (f : ι → Rn n → ℝ) (S : Set (Rn n)) : Prop :=
  ∃ α₁ α₂ : ℝ, ∀ x ∈ S, ∀ i, α₁ ≤ f i x ∧ f i x ≤ α₂

/-- The bridge for `LipschitzianOn`: Rockafellar's Lipschitz condition is Mathlib's
`LipschitzOnWith` with the constant left existentially quantified. -/
theorem lipschitzianOn_iff {n : ℕ} {f : Rn n → ℝ} {S : Set (Rn n)} :
    LipschitzianOn f S ↔ ∃ K : ℝ≥0, LipschitzOnWith K f S := by
  constructor
  · rintro ⟨α, hα, h⟩
    refine ⟨α.toNNReal, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal α hα]
    exact h x hx y hy
  · rintro ⟨K, hK⟩
    refine ⟨K, K.coe_nonneg, fun y hy x hx => ?_⟩
    have h := hK.dist_le_mul y hy x hx
    rwa [Real.dist_eq, dist_eq_norm] at h

/-- The bridge for `EquiLipschitzianOn`: a single `ℝ≥0` constant serving the whole family. -/
theorem equiLipschitzianOn_iff {n : ℕ} {ι : Type*} {f : ι → Rn n → ℝ} {S : Set (Rn n)} :
    EquiLipschitzianOn f S ↔ ∃ K : ℝ≥0, ∀ i, LipschitzOnWith K (f i) S := by
  constructor
  · rintro ⟨α, hα, h⟩
    refine ⟨α.toNNReal, fun i => LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal α hα]
    exact h i x hx y hy
  · rintro ⟨K, hK⟩
    refine ⟨K, K.coe_nonneg, fun i y hy x hx => ?_⟩
    have h := (hK i).dist_le_mul y hy x hx
    rwa [Real.dist_eq, dist_eq_norm] at h

/-- The bridge for `PointwiseBoundedOn`: boundedness of a set of reals is two-sided
boundedness, which is the shape the backbone's hypotheses take. -/
theorem pointwiseBoundedOn_iff {n : ℕ} {ι : Type*} {f : ι → Rn n → ℝ} {S : Set (Rn n)} :
    PointwiseBoundedOn f S ↔ ∀ x ∈ S, BddBelow (Set.range fun i => f i x) ∧
      BddAbove (Set.range fun i => f i x) :=
  forall₂_congr fun _ _ => isBounded_iff_bddBelow_bddAbove

/-- The bridge for `UniformlyBoundedOn`: a two-sided uniform bound is a bound on `|f i x|`, which
is the shape the backbone's conclusions take. -/
theorem uniformlyBoundedOn_iff {n : ℕ} {ι : Type*} {f : ι → Rn n → ℝ} {S : Set (Rn n)} :
    UniformlyBoundedOn f S ↔ ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ x ∈ S, |f i x| ≤ M := by
  constructor
  · rintro ⟨α₁, α₂, h⟩
    refine ⟨max |α₁| |α₂|, le_trans (abs_nonneg α₁) (le_max_left _ _), fun i x hx => ?_⟩
    obtain ⟨h₁, h₂⟩ := h x hx i
    refine abs_le.2 ⟨?_, ?_⟩
    · have hm : |α₁| ≤ max |α₁| |α₂| := le_max_left _ _
      have hn : -|α₁| ≤ α₁ := neg_abs_le α₁
      linarith
    · have hm : |α₂| ≤ max |α₁| |α₂| := le_max_right _ _
      have hn : α₂ ≤ |α₂| := le_abs_self α₂
      linarith
  · rintro ⟨M, -, hM⟩
    exact ⟨-M, M, fun x hx i => abs_le.1 (hM i x hx)⟩

/-! ### Theorem 10.1 -/

/-- **Theorem 10.1.** A convex function `f` on `ℝⁿ` is continuous relative to any
relatively open convex set `C` in its effective domain — in particular relative to `ri (dom f)`,
which is `corollary_10_1_1`'s and Theorem 10.4's form.

The reduction is Rockafellar's own: replacing `f` by the function that agrees with it on `C` and is
`+∞` elsewhere makes `C` the effective domain, so `C = ri C = ri (dom (restrict C f))`, and then
`ConvexFn.continuousOn_relint_dom` applies. The improper case is not excluded: Theorem 7.2
(`ConvexFn.eq_bot_of_mem_relint_dom`) makes the restricted function constantly `-∞` on `C`. -/
theorem theorem_10_1 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) {C : Set (Rn n)}
    (hC : Convex ℝ C) (hCro : ri C = C) (hCdom : C ⊆ dom f) : ContinuousOn f C := by
  have hg : ConvexFn (restrict C f) := hf.restrict hC
  have hdom : dom (restrict C f) = C := by
    ext x
    constructor
    · intro hx
      by_contra hxC
      rw [mem_dom, restrict_of_notMem hxC] at hx
      exact absurd hx (lt_irrefl _)
    · intro hx
      rw [mem_dom, restrict_of_mem hx]
      exact mem_dom.1 (hCdom hx)
  have hri : ri (dom (restrict C f)) = C := by rw [hdom, hCro]
  by_cases hp : Proper (restrict C f)
  · have hcont : ContinuousOn (restrict C f) C := by
      have h := hg.continuousOn_relint_dom hp
      rwa [hri] at h
    exact hcont.congr fun x hx => (restrict_of_mem hx).symm
  · have hconst : ContinuousOn (fun _ : Rn n => (⊥ : EReal)) C := continuousOn_const
    refine hconst.congr fun x hx => ?_
    have hx' : x ∈ ri (dom (restrict C f)) := by rw [hri]; exact hx
    have hbot := hg.eq_bot_of_mem_relint_dom hp hx'
    rwa [restrict_of_mem hx] at hbot

/-! ### Corollary 10.1.1 -/

/-- **Corollary 10.1.1.** A convex function finite on all of `ℝⁿ` is necessarily
continuous.

"finite on all of `ℝⁿ`" is `dom f = univ` together with properness, which is the `≠ -∞` half. -/
theorem corollary_10_1_1 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    (hdom : dom f = Set.univ) : Continuous f :=
  hf.continuous_of_dom_eq_univ hp hdom

/-! ### Theorem 10.2 -/

/-- **Theorem 10.2.** Let `f` be a convex function on `ℝⁿ`, and let `S` be any locally
simplicial subset of `dom f`. Then `f` is upper semicontinuous relative to `S`.

Rockafellar's proof triangulates each simplex around `x` so as to make `x` a vertex, a step he calls
"intuitively obvious" and does not prove; the backbone avoids it — see the module docstring.
Improperness is not excluded, and the book's parenthetical about `∞ - ∞` is what
`ConvexFn.epi_combo` handles by never leaving `ℝ`. -/
theorem theorem_10_2 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) {S : Set (Rn n)}
    (hS : LocallySimplicial S) (hSdom : S ⊆ dom f) : UpperSemicontinuousOn f S :=
  hf.upperSemicontinuousOn_of_locallySimplicial hS hSdom

/-- **Theorem 10.2**, second assertion: if `f` is closed, `f` is actually continuous
relative to `S`.

A closed function is lower semicontinuous (`ClosedFn.lowerSemicontinuous`), and Theorem 10.2
supplies the other half. -/
theorem theorem_10_2_closed {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (hcl : ClosedFn f)
    {S : Set (Rn n)} (hS : LocallySimplicial S) (hSdom : S ⊆ dom f) : ContinuousOn f S :=
  hf.continuousOn_of_locallySimplicial (ClosedFn.lowerSemicontinuous hcl) hS hSdom

/-! ### Theorem 10.3 -/

/-- **Theorem 10.3.** Let `C` be a locally simplicial convex set, and let `f` be a
finite convex function on `ri C` which is bounded above on every bounded subset of `ri C`. Then `f`
can be extended to a continuous finite convex function on the whole of `C`.

"A finite convex function on `ri C`" is transcribed as a convex `f : ℝⁿ → (-∞, +∞]` with
`dom f = ri C`, which is how §4 reads a function given only on a set. The extension produced is
`cl f`, exactly Rockafellar's; uniqueness is `theorem_10_3_unique`. -/
theorem theorem_10_3 {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) (hCls : LocallySimplicial C)
    (hne : C.Nonempty) {f : Rn n → EReal} (hf : ConvexFn f) (hbot : ∀ x, f x ≠ ⊥)
    (hdom : dom f = ri C)
    (hbdd : ∀ S ⊆ ri C, Bornology.IsBounded S → ∃ c : ℝ, ∀ x ∈ S, f x ≤ (c : EReal)) :
    ∃ g : Rn n → EReal, ConvexFn g ∧ ClosedFn g ∧ Proper g ∧ Set.EqOn g f (ri C) ∧
      C ⊆ dom g ∧ ContinuousOn g C :=
  exists_closedFn_continuousOn_of_locallySimplicial hC hCls hne hf hbot hdom hbdd

/-- **Theorem 10.3**, uniqueness: "there can be only one such extension, since
`C ⊆ cl (ri C)`".

It — as the book's one-line argument already shows — needs neither local simpliciality of `C` nor
convexity of the two functions. -/
theorem theorem_10_3_unique {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) {g₁ g₂ : Rn n → EReal}
    (h₁ : ContinuousOn g₁ C) (h₂ : ContinuousOn g₂ C) (h : Set.EqOn g₁ g₂ (ri C)) :
    Set.EqOn g₁ g₂ C :=
  eqOn_of_continuousOn_of_eqOn_relint hC h₁ h₂ h

/-! ### Theorem 10.4 -/

/-- **Theorem 10.4.** Let `f` be a proper convex function, and let `S` be any closed
bounded subset of `ri (dom f)`. Then `f` is Lipschitzian relative to `S`.

Closed and bounded is compact in `ℝⁿ`, which is the only place finite dimension enters beyond
Theorem 10.1. The Lipschitz condition is about real values, so the statement is about `(f
·).toReal`, which properness makes faithful on `dom f`. -/
theorem theorem_10_4 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    {S : Set (Rn n)} (hScl : IsClosed S) (hSb : Bornology.IsBounded S) (hSri : S ⊆ ri (dom f)) :
    LipschitzianOn (fun x => (f x).toReal) S :=
  lipschitzianOn_iff.2
    (hf.exists_lipschitzOnWith_of_isCompact hp (Metric.isCompact_of_isClosed_isBounded hScl hSb)
      hSri)

/-! ### Theorem 10.5 -/

/-- **Theorem 10.5.** Let `f` be a finite convex function on `ℝⁿ`. In order that `f`
be uniformly continuous relative to `ℝⁿ`, it is necessary and sufficient that the recession
function `f0⁺` be finite everywhere.

"Finite everywhere" is spelled `≠ ⊤`: the other half, `f0⁺ ≠ -∞`, is automatic from properness of
`f` (`proper_recessionFn`). -/
theorem theorem_10_5 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    (hdom : dom f = Set.univ) :
    (UniformContinuous fun x => (f x).toReal) ↔ ∀ y, recessionFn f y ≠ ⊤ :=
  hf.uniformContinuous_toReal_iff hp hdom

/-- **Theorem 10.5**, second assertion: in that event `f` is actually Lipschitzian
relative to `ℝⁿ`.

The constant is Rockafellar's `α = sup {(f0⁺) z | ‖z‖ = 1}`, finite by Corollary 10.1.1 applied to
`f0⁺`. -/
theorem theorem_10_5_lipschitzian {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    (hdom : dom f = Set.univ) (hrec : ∀ y, recessionFn f y ≠ ⊤) :
    LipschitzianOn (fun x => (f x).toReal) Set.univ := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzWith_of_recessionFn_ne_top hp hdom hrec
  exact lipschitzianOn_iff.2 ⟨K, hK.lipschitzOnWith⟩

/-! ### Corollary 10.5.1 -/

/-- **Corollary 10.5.1.** A finite convex function `f` is Lipschitzian relative to
`ℝⁿ` if `liminf_{λ → ∞} f (λ y) / λ < ∞` for every `y`.

The `liminf` is spelled as "for some `c`, `f (a y) ≤ c a` for arbitrarily large `a`", which is what
it says once the `EReal` quotient is avoided; the two agree because the quotient is nondecreasing in
`λ`, which is Theorem 8.5 and is also the book's whole proof of the corollary. -/
theorem corollary_10_5_1 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    (hdom : dom f = Set.univ)
    (h : ∀ y : Rn n, ∃ c : ℝ, ∃ᶠ a : ℝ in atTop, f (a • y) ≤ ((c * a : ℝ) : EReal)) :
    LipschitzianOn (fun x => (f x).toReal) Set.univ := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzWith_of_frequently_le hp hdom h
  exact lipschitzianOn_iff.2 ⟨K, hK.lipschitzOnWith⟩

/-! ### Corollary 10.5.2 -/

/-- **Corollary 10.5.2.** Let `g` be any finite convex function Lipschitzian relative
to `ℝⁿ`. Then every finite convex function `f` with `f ≤ g` is likewise Lipschitzian relative to
`ℝⁿ`.

It drops the convexity of `g`: Rockafellar's proof runs through `f0⁺ ≤ g0⁺`, but the estimate only
needs `g` Lipschitz. The hypothesis is kept here so the statement is the book's. -/
theorem corollary_10_5_2 {n : ℕ} {f g : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    (hdom : dom f = Set.univ) (_hg : ConvexFn g) (hgp : Proper g) (hgdom : dom g = Set.univ)
    (hglip : LipschitzianOn (fun x => (g x).toReal) Set.univ) (hle : ∀ x, f x ≤ g x) :
    LipschitzianOn (fun x => (f x).toReal) Set.univ := by
  obtain ⟨K, hK⟩ := lipschitzianOn_iff.1 hglip
  rw [lipschitzOnWith_univ] at hK
  obtain ⟨K', hK'⟩ := hf.exists_lipschitzWith_of_le_lipschitz hp hdom hK fun x => by
    rw [coe_toReal_of_dom_eq_univ hgp hgdom x]; exact hle x
  exact lipschitzianOn_iff.2 ⟨K', hK'.lipschitzOnWith⟩

/-! ### Theorem 10.6 -/

/-- **Theorem 10.6.** Let `C` be a relatively open convex set, and let `{f i | i ∈ I}`
be an arbitrary collection of convex functions finite and pointwise bounded on `C`. Let `S` be any
closed bounded subset of `C`. Then `{f i}` is uniformly bounded on `S` and equi-Lipschitzian
relative to `S`.

"Relatively open" is `ri C = C`; "finite and convex on `C`" is Mathlib's `ConvexOn ℝ C`, which is
real-valued, exactly as the book's collection is. `I` may be empty. -/
theorem theorem_10_6 {n : ℕ} {ι : Type*} {C : Set (Rn n)} (hC : Convex ℝ C) (hCro : ri C = C)
    {f : ι → Rn n → ℝ} (hf : ∀ i, ConvexOn ℝ C (f i)) (hbdd : PointwiseBoundedOn f C)
    {S : Set (Rn n)} (hScl : IsClosed S) (hSb : Bornology.IsBounded S) (hSC : S ⊆ C) :
    UniformlyBoundedOn f S ∧ EquiLipschitzianOn f S := by
  have hbdd' : ∀ x ∈ ri C, Bornology.IsBounded (Set.range fun i => f i x) := by
    rw [hCro]; exact hbdd
  have hSC' : S ⊆ ri C := by rw [hCro]; exact hSC
  obtain ⟨hub, hlip⟩ := exists_forall_abs_le_and_lipschitzOnWith_of_isCompact_relint hC hf hbdd'
    (Metric.isCompact_of_isClosed_isBounded hScl hSb) hSC'
  exact ⟨uniformlyBoundedOn_iff.2 hub, equiLipschitzianOn_iff.2 hlip⟩

/-- **Theorem 10.6**, weakened hypotheses: the conclusion survives if pointwise
boundedness is replaced by

(a) a subset `C'` of `C` with `cl C' ⊇ C` on which `sup {f i x | i ∈ I}` is finite, and
(b) at least one `x ∈ C` at which `inf {f i x | i ∈ I}` is finite.

The book's (a) reads `conv (cl C') ⊇ C`, which is weaker than the `cl C' ⊇ C` used here; the
convex-hull weakening is in the backbone only in its `interior` form
(`bddAbove_range_of_subset_convexHull_closure`) and not in the `ri` form this section needs. -/
theorem theorem_10_6_ab {n : ℕ} {ι : Type*} {C C' : Set (Rn n)} (hC : Convex ℝ C)
    (hCro : ri C = C) {f : ι → Rn n → ℝ} (hf : ∀ i, ConvexOn ℝ C (f i)) (hC'sub : C' ⊆ C)
    (hdense : C ⊆ closure C') (hab : ∀ x ∈ C', BddAbove (Set.range fun i => f i x))
    (hbe : ∃ z ∈ C, BddBelow (Set.range fun i => f i z))
    {S : Set (Rn n)} (hScl : IsClosed S) (hSb : Bornology.IsBounded S) (hSC : S ⊆ C) :
    UniformlyBoundedOn f S ∧ EquiLipschitzianOn f S := by
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hdense' : ri C ⊆ closure C' := by rw [hCro]; exact hdense
  have hbe' : ∃ z ∈ ri C, BddBelow (Set.range fun i => f i z) := by rw [hCro]; exact hbe
  have hSC' : S ⊆ ri C := by rw [hCro]; exact hSC
  have hS : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSb
  exact ⟨uniformlyBoundedOn_iff.2
      (exists_forall_abs_le_of_isCompact_relint hC hf hC'ri hdense' hab hbe' hS hSC'),
    equiLipschitzianOn_iff.2
      (exists_forall_lipschitzOnWith_of_isCompact_relint hC hf hC'ri hdense' hab hbe' hS hSC')⟩

/-! ### Theorem 10.7 -/

/-- **Theorem 10.7.** Let `C` be a relatively open convex set in `ℝⁿ`, and let `T` be
any locally compact topological space. Let `f` be a real-valued function on `C × T` such that
`f (x, t)` is convex in `x` for each `t` and continuous in `t` for each `x`. Then `f` is jointly
continuous on `C × T`.

`T` is a type, so "continuous on `C × T`" is `ContinuousOn F (C ×ˢ univ)`. -/
theorem theorem_10_7 {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) (hCro : ri C = C) {T : Type*}
    [TopologicalSpace T] [LocallyCompactSpace T] {F : Rn n × T → ℝ}
    (hconv : ∀ t : T, ConvexOn ℝ C fun x => F (x, t))
    (hcont : ∀ x ∈ C, Continuous fun t => F (x, t)) :
    ContinuousOn F (C ×ˢ (Set.univ : Set T)) := by
  have hsub : C ⊆ ri C := by rw [hCro]
  have hdense : ri C ⊆ closure C := by rw [hCro]; exact subset_closure
  have h := continuousOn_prod_of_convexOn_relint (C' := C) hC hconv hsub hdense hcont
  rwa [hCro] at h

/-- **Theorem 10.7**, weakened hypothesis: it is enough that `f (x, ·)` be continuous
for each `x` in some subset `C'` of `C` with `cl C' ⊇ C`.

Specialises `continuousOn_prod_of_convexOn_relint` directly. -/
theorem theorem_10_7_dense {n : ℕ} {C C' : Set (Rn n)} (hC : Convex ℝ C) (hCro : ri C = C)
    {T : Type*} [TopologicalSpace T] [LocallyCompactSpace T] {F : Rn n × T → ℝ}
    (hconv : ∀ t : T, ConvexOn ℝ C fun x => F (x, t)) (hC'sub : C' ⊆ C)
    (hdense : C ⊆ closure C') (hcont : ∀ x ∈ C', Continuous fun t => F (x, t)) :
    ContinuousOn F (C ×ˢ (Set.univ : Set T)) := by
  have hsub : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hdense' : ri C ⊆ closure C' := by rw [hCro]; exact hdense
  have h := continuousOn_prod_of_convexOn_relint hC hconv hsub hdense' hcont
  rwa [hCro] at h

/-! ### Theorem 10.8 -/

/-- **Theorem 10.8.** Let `C` be a relatively open convex set and `f 1, f 2, …` a
sequence of finite convex functions on `C` converging pointwise on a subset `C'` of `C` with
`cl C' ⊇ C`. The limit then exists for every `x ∈ C`, is finite and convex, and the convergence is
uniform on each closed bounded subset of `C`. -/
theorem theorem_10_8 {n : ℕ} {C C' : Set (Rn n)} (hC : Convex ℝ C) (hCro : ri C = C)
    {f : ℕ → Rn n → ℝ} (hf : ∀ i, ConvexOn ℝ C (f i)) (hC'sub : C' ⊆ C)
    (hdense : C ⊆ closure C')
    (hcv : ∀ x ∈ C', ∃ L : ℝ, Tendsto (fun i => f i x) atTop (𝓝 L)) :
    ∃ g : Rn n → ℝ, ConvexOn ℝ C g ∧ (∀ x ∈ C, Tendsto (fun i => f i x) atTop (𝓝 (g x))) ∧
      ∀ ⦃S : Set (Rn n)⦄, IsClosed S → Bornology.IsBounded S → S ⊆ C →
        TendstoUniformlyOn f g atTop S := by
  have hsub : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hdense' : ri C ⊆ closure C' := by rw [hCro]; exact hdense
  obtain ⟨g, hgc, hgt, hgu⟩ := exists_tendstoUniformlyOn_of_dense_relint hC hf hsub hdense' hcv
  rw [hCro] at hgc hgt hgu
  exact ⟨g, hgc, hgt, fun S hScl hSb hSC =>
    hgu (Metric.isCompact_of_isClosed_isBounded hScl hSb) hSC⟩

/-! ### Corollary 10.8.1 -/

/-- **Corollary 10.8.1.** Let `f` be a finite convex function on a relatively open
convex set `C`, and `f 1, f 2, …` finite convex functions on `C` with `limsup_i f i x ≤ f x` for
every `x ∈ C`. Then for each closed bounded `S ⊆ C` and each `ε > 0` there is an `i₀` with
`f i x ≤ f x + ε` for all `i ≥ i₀` and all `x ∈ S`.

The `limsup` hypothesis is spelled "for every `δ > 0`, eventually `f i x ≤ f x + δ`", which is what
it means for a real sequence. -/
theorem corollary_10_8_1 {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) (hCro : ri C = C)
    {f : ℕ → Rn n → ℝ} (hf : ∀ i, ConvexOn ℝ C (f i)) {g : Rn n → ℝ} (hg : ConvexOn ℝ C g)
    (hle : ∀ x ∈ C, ∀ δ > 0, ∀ᶠ i in atTop, f i x ≤ g x + δ)
    {S : Set (Rn n)} (hScl : IsClosed S) (hSb : Bornology.IsBounded S) (hSC : S ⊆ C)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ i in atTop, ∀ x ∈ S, f i x ≤ g x + ε := by
  have hle' : ∀ x ∈ ri C, ∀ δ > 0, ∀ᶠ i in atTop, f i x ≤ g x + δ := by rw [hCro]; exact hle
  have hSC' : S ⊆ ri C := by rw [hCro]; exact hSC
  exact eventually_forall_le_add_of_eventually_le_relint hC hf hg hle'
    (Metric.isCompact_of_isClosed_isBounded hScl hSb) hSC' hε

/-! ### Theorem 10.9 -/

/-- **Theorem 10.9.** Let `C` be a relatively open convex set and `f 1, f 2, …` a
sequence of finite convex functions on `C` whose values are bounded at each point of a dense subset
`C'` of `C`. It is then possible to select a subsequence converging uniformly on closed bounded
subsets of `C` to some finite convex function `f`.

The book's proof needs a countable dense subset of `C'`, extracted by hand from the rational balls;
the backbone gets it from separability of `ℝⁿ`. -/
theorem theorem_10_9 {n : ℕ} {C C' : Set (Rn n)} (hC : Convex ℝ C) (hCro : ri C = C)
    {f : ℕ → Rn n → ℝ} (hf : ∀ i, ConvexOn ℝ C (f i)) (hC'sub : C' ⊆ C)
    (hdense : C ⊆ closure C') (hbdd : PointwiseBoundedOn f C') :
    ∃ (φ : ℕ → ℕ) (g : Rn n → ℝ), StrictMono φ ∧ ConvexOn ℝ C g ∧
      (∀ x ∈ C, Tendsto (fun i => f (φ i) x) atTop (𝓝 (g x))) ∧
      ∀ ⦃S : Set (Rn n)⦄, IsClosed S → Bornology.IsBounded S → S ⊆ C →
        TendstoUniformlyOn (fun i => f (φ i)) g atTop S := by
  have hsub : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hdense' : ri C ⊆ closure C' := by rw [hCro]; exact hdense
  obtain ⟨φ, g, hφ, hgc, hgt, hgu⟩ :=
    exists_subseq_tendstoUniformlyOn_relint hC hf hsub hdense' hbdd
  rw [hCro] at hgc hgt hgu
  exact ⟨φ, g, hφ, hgc, hgt, fun S hScl hSb hSC =>
    hgu (Metric.isCompact_of_isClosed_isBounded hScl hSb) hSC⟩

end Rockafellar
