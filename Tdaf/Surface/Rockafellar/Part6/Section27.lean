/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Optimization.Minimum
import Tdaf.Analysis.Convex.Optimization.Prox
import Tdaf.Analysis.Convex.Polyhedral.Duality
import Tdaf.Analysis.Convex.Subgradient.StrictlyConvex
import Tdaf.Surface.Rockafellar.Part5.Section25

/-!
# Rockafellar, §27: The Minimum of a Convex Function

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §27, pp. 263–272: the unconstrained
minimum of a convex function, its duality with `f*` at the origin, existence and well-posedness
under a recession hypothesis, minimisation over a convex set, and the optimality condition
`0 ∈ ∂h(x) + N_C(x)`.

This is the first section of Part VI, and it is where §§8, 13, 14, 23 and 25 are cashed in.
Theorem 27.1 is a nine-clause omnibus whose printed proof (10449) is a one-line pointer list to
those five sections, so every clause here is a specialisation of something that already exists;
the work was finding which. Theorems 27.2 and 27.3 are the existence theory, and Theorem 27.4 is
§23's sum rule read at `h + δ(· | C)`.

## Contents

| label | declaration |
|---|---|
| Theorem 27.1(a) | `theorem_27_1_a`, `theorem_27_1_a_bddBelow` |
| Theorem 27.1(b) | `theorem_27_1_b`, `theorem_27_1_b_attained`, `theorem_27_1_b_relint`,
  `theorem_27_1_b_constancy` |
| Theorem 27.1(c) | `theorem_27_1_c`, `theorem_27_1_c_free` |
| Theorem 27.1(d) | `theorem_27_1_d`, `theorem_27_1_d_recession`, `theorem_27_1_d_setOf_le` |
| Theorem 27.1(e) | `theorem_27_1_e`, `theorem_27_1_e_differentiable`,
  `theorem_27_1_e_gradientVec` |
| Theorem 27.1(f) | `theorem_27_1_f_setOf_le`, `theorem_27_1_f_argmin`,
  `theorem_27_1_f_polarCone` |
| Theorem 27.1(g) | `theorem_27_1_g_setOf_le`, `theorem_27_1_g_argmin` |
| Theorem 27.1(h) | `theorem_27_1_h`, `theorem_27_1_h_epsSubgradient` |
| Theorem 27.1(i) | `theorem_27_1_i`, `theorem_27_1_i_notMem`, `theorem_27_1_ai` |
| Theorem 27.2 | `theorem_27_2_finite`, `theorem_27_2_attained`, `theorem_27_2_argmin`,
  `theorem_27_2_wellPosed` |
| Corollary 27.2.1 | `corollary_27_2_1_isBounded`, `corollary_27_2_1_clusterPt`,
  `corollary_27_2_1_infDist` |
| `Corollary 27.2.2` | `corollary_27_2_2` |
| Theorem 27.3 | `theorem_27_3`, `theorem_27_3_polyhedral`, `theorem_27_3_lineality` |
| Corollary 27.3.1 | `corollary_27_3_1`, `corollary_27_3_1_unconstrained` |
| Corollary 27.3.2 | `corollary_27_3_2`, `corollary_27_3_2_unconstrained` |
| Corollary 27.3.3 | `corollary_27_3_3`, `corollary_27_3_3_polyhedral` |
| Theorem 27.4 | `theorem_27_4_sufficient`, `theorem_27_4_necessary`,
  `theorem_27_4_necessary_polyhedral` |
| p. 271 application (10673) | `nearest_iff_sub_mem_normalCone` |
| p. 264 remarks (10405–10417) | `convex_argmin_surface`, `isClosed_argmin`,
  `subsingleton_argmin_of_strictConvexOnFn`, `mem_argmin_iff_zero_mem_subgradient_surface`,
  `mem_argmin_iff_zero_le_dirDeriv`, `mem_argmin_of_localMin` |

## The section's definitions

Three of the section's four objects are backbone definitions and are used without a surface copy.

* `Tdaf.ConvexAnalysis.argmin f` is Rockafellar's **minimum set** `lev_{inf f} f` (10405), defined
  as `{x | ∀ z, f x ≤ f z}`. It is *not* `IsMinOn f Set.univ`: the unfolded form is exactly the
  subgradient inequality at `x* = 0`, which is why `mem_argmin_iff_zero_mem_subgradient_surface`
  is `Iff.rfl`-adjacent and why "§27 is §23 at the origin" is literally true.
  `mem_argmin_iff_isMinOn` is the bridge to Mathlib's predicate.
* `lev_α f` is `{x | f x ≤ (α : EReal)}`, written out. The book gives it a notation and the
  backbone does not, because every statement about it is a statement about a sublevel set of an
  `EReal`-valued function and the set-builder is shorter than the notation.
* `inf f` is `⨅ x, f x` in `EReal`, so "bounded below", "finite" and "attained" are `≠ ⊥`,
  `≠ ⊥ ∧ ≠ ⊤` and `(argmin f).Nonempty`.

The one definition introduced here is `Rockafellar.IsDirectionOfRecession`, the book's **direction
of recession of `f`** (10451): a nonzero `y` with `f (x + λ y)` non-increasing in `λ` for every
`x`. Its bridge is `isDirectionOfRecession_iff` (Theorem 8.6), and
`recessionConeFn_eq_zero_iff` / `recessionConeFn_inter_eq_zero_iff` turn "`f` has no direction of
recession" and "`h` and `C` have none in common" into the backbone's `0⁺f = {0}` and
`0⁺f ∩ 0⁺C = {0}`. The theorems below take the *book's* form of the hypothesis and specialise the
backbone's.

## Where the book's hypotheses had to change

**Theorem 27.1(a) needs no hypothesis at all**, not even convexity. `f*(0) = ⨆ x (⟨x,0⟩ - f x)` is
a reindexing of `-(⨅ x, f x)`. Rockafellar's standing "closed proper convex" is there for the
other eight clauses, and his own proof says as much.

**Theorem 27.1(b), first sentence, needs no properness.** The `EReal` step is
`EReal.le_sub_iff_add_le` at `c = 0`, and `0` is neither `⊥` nor `⊤`.

**Theorem 27.1(c) states only one of the book's two finiteness bounds on each side.** Rockafellar
asks that `f*(0)` be finite — `≠ ⊥` and `≠ ⊤`. For a proper `f` the first half is automatic
(`conj_ne_bot`), and symmetrically `inf f ≠ ⊤` is automatic because `dom f ≠ ∅`. Writing "finite"
out in full would put a redundant conjunct on each side of an `↔`; `theorem_27_1_c_free` records
the two bounds that were dropped, so that the reading can be checked.

**Theorem 27.1(d) does not need Corollary 13.3.4**, contrary to Rockafellar's proof: Corollary
14.2.2 already says that every level set is bounded exactly when the origin is interior to
`dom f*`, and Theorem 27.2 turns that into existence of a minimiser. Neither does (g) need a
shifted-function API, although the book's proof is "Theorem 13.5 applied to `f - α`": Corollary
13.2.1 computes the closure of a generated function as a support function directly.

**Theorem 27.1(h) is an infimum, not a limit.** The book writes `lim_{α ↓ inf f}`. The level sets
increase with `α`, so their support functions do, and the monotone limit *is* the infimum; no
filter is needed. The reindexing `α = inf f + ε` is the book's own, made inside its proof.

**Theorem 27.1(i) quantifies `y ≠ 0` for free.** At `y = 0` the book's inequality at `λ = 1` would
read `0 ≤ -ε` at any point of the non-empty effective domain, so the clause cannot be satisfied
there; the backbone records the `y ≠ 0` rather than assuming it.

**§27's minimising results are stated for arbitrary filters in the backbone, and for sequences
here.** Rockafellar's Corollaries 27.2.1 and 27.2.2 are about sequences `x₁, x₂, …`, and that is
how `corollary_27_2_1_isBounded`, `corollary_27_2_1_clusterPt` and `corollary_27_2_2` read. The
backbone's `tendsto_infDist_argmin`, `mem_argmin_of_mapClusterPt` and
`tendsto_of_argmin_eq_singleton` take an arbitrary filter, of which `atTop` on `ℕ` is one
instance; `corollary_27_2_1_infDist` keeps the general form beside the sequential ones. Only
`corollary_27_2_1_isBounded`, whose conclusion is about the *range* of a sequence, genuinely needs
`ℕ`.

**Theorem 27.2's closed bounded minimum set is stated as compact.** In `ℝⁿ` the two are the same
(Heine–Borel), and compactness is what the proof produces.

**Theorem 27.3 has a third form the book does not state.** `theorem_27_3_lineality` weakens the
non-polyhedral hypothesis from "no common direction of recession" to "every common direction of
recession is one in which `h` is constant *and* `C` is linear", with no polyhedrality anywhere.
It is what the backbone's projection argument proves for free, and it sits strictly between the
book's two clauses.

**Corollary 27.3.3's polyhedral refinement is stated with two index types rather than an index set
and a finite subset.** `ι₀` is the book's `I₀` and `ι₁` its `I ∖ I₀`. The split is the same and it
keeps every `DecidableEq` out of the statement (`gotchas.md` SET11).

**Theorem 27.4's sufficiency half needs nothing**: not properness of `h`, not convexity of `C`, not
`x ∈ C`. The subgradient inequality and the normality inequality simply add.

## What is not here

* **The p. 266 counterexample** (book, 10471–10491) — *omitted with a reason*. It is unnumbered,
  and it exhibits a finite convex `f` on `ℝ²` (10471) attaining its infimum relative to every
  *line*
  and yet is unbounded below: `f(ξ₁, ξ₂) = d(x, P)² - ξ₁` with `P = {ξ₂ ≥ ξ₁²}`. What it costs is
  not §27's: the function is an infimal convolution `|·|² □ δ(· | P)` whose value has to be
  computed as the squared distance to a parabola, which is a §16 computation and a page of
  one-variable algebra, and the conclusion it supports — that `f 0⁺ ≥ 0` everywhere is compatible
  with `inf f = -∞` — is available as a *theorem* without it, `theorem_27_1_ai`, which is what the
  book's own follow-up sentence at 10491 says the example is for.
* **The p. 267 one-dimensional reading of Theorem 27.2** (10469) — *omitted with a reason*.
  "A closed proper convex function on the real line attains its infimum if it is neither
  non-increasing nor non-decreasing" is Theorem 27.2 at `n = 1` with `IsDirectionOfRecession`
  unfolded, and the book states it as a remark, not as a result.
* **The p. 269 worked example of Corollary 27.3.3** (10543–10627) — *omitted with a reason*.
  Unnumbered; it instantiates the corollary at `fᵢ(x) = (1/pᵢ)⟨x, Qᵢx⟩^{pᵢ/2} + ⟨aᵢ, x⟩ + αᵢ` and
  what it needs beyond this section is Corollary 8.5.2's recession formula for such an `fᵢ` and
  the gauge computation of §15.
* **The p. 271 example of minimising a separable `h` over a subspace** (10687–10748) — *deferred by
  scope*. Its last third turns on Theorem 22.6 and the elementary vectors of a subspace, which is
  the combinatorial matroid theory §22 is deferred for. The book's *other* application of
  Theorem 27.4, the nearest point of a convex set (10673), **is** here, as
  `nearest_iff_sub_mem_normalCone`.

## Backbone gaps

Each is proved as a `private` lemma below and should move.

1. **`proper_indicatorFn`** — **done**. It is public in `Tdaf/Analysis/Convex/Indicator.lean`, as
   the biconditional `Proper (indicatorFn s) ↔ s.Nonempty`, beside `dom_indicatorFn` and
   `indicatorFn_ne_bot`, which are its two halves. The two call sites here take `.2`.

2. **`Polyhedral.biInter` and `Polyhedral.iInter`**, in
   `Tdaf/Analysis/Convex/Polyhedral/Ops.lean`. Wanted:
   `(∀ i, Polyhedral (S i)) → ∀ s : Finset ι, Polyhedral (⋂ i ∈ s, S i)` and its `[Finite ι]`
   corollary. That file has only the binary `Polyhedral.inter`, although the defining datum of
   `Polyhedral` is already a `Finset` of half-spaces, so the indexed forms are a `Finset.union`
   away if proved there rather than by the induction used here.
3. **`polyhedralFn_setOf_le`**, in `Tdaf/Analysis/Convex/Polyhedral/Function.lean`. Wanted:
   `PolyhedralFn f → ∀ α : ℝ, Polyhedral {x | f x ≤ (α : EReal)}` — a level set of a polyhedral
   convex function is a polyhedral convex set. It is `Polyhedral.comap_affine` applied to
   `x ↦ (x, α)` and is three lines; `Function.lean` states the epigraph direction
   (`polyhedralFn_indicatorFn` builds an epigraph *from* a polyhedral set) and never the level-set
   direction, which is what a constraint system `fᵢ(x) ≤ 0` needs.

`zero_mem_relint_dom_conj_iff_recessionConeFn_subset_constancySpace` — the last sentence of
Theorem 27.1(b) — was a fourth gap and is now in `Optimization/Minimum.lean`, beside the
`interior` twin `zero_mem_interior_dom_conj_iff_recessionConeFn_eq_zero` that Theorem 27.1(d)
runs on.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §27 (pp. 263–272).
  Theorem 27.1 with its nine clauses, Theorem 27.2 with Corollaries 27.2.1 and 27.2.2,
  Theorem 27.3 with Corollaries 27.3.1, 27.3.2 and 27.3.3, and Theorem 27.4. Corollary 27.2.1 is
  **stated with no printed proof**; the polyhedral clause of Theorem 27.3 is proved from Helly's
  theorem in the book and from a projection here.
-/

open Bornology Filter Set Topology

open scoped Pointwise

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

variable {n : ℕ}

/-! ### The section's vocabulary -/

section Vocabulary

variable {f : Rn n → EReal} {y : Rn n}

/-- Rockafellar's **direction of recession of `f`** (book, line 10451): the direction of a nonzero
vector `y` such that `f (x + λ y)` is a non-increasing function of `λ` for every choice of `x`. -/
def IsDirectionOfRecession (f : Rn n → EReal) (y : Rn n) : Prop :=
  y ≠ 0 ∧ ∀ x : Rn n, Antitone fun l : ℝ => f (x + l • y)

/-- **The bridge to the backbone.** A direction of recession is a nonzero element of
`recessionConeFn f`, by Theorem 8.6 (`forall_antitone_iff_recessionFn_nonpos`), which needs no
hypothesis on `f` at all. -/
theorem isDirectionOfRecession_iff :
    IsDirectionOfRecession f y ↔ y ≠ 0 ∧ y ∈ recessionConeFn f :=
  and_congr_right fun _ => forall_antitone_iff_recessionFn_nonpos

/-- **"`f` has no direction of recession" is `0⁺f = {0}`.** This is the hypothesis of Theorem 27.2
and of the non-polyhedral case of Theorem 27.3, and it is how the backbone spells it. -/
theorem recessionConeFn_eq_zero_iff (f : Rn n → EReal) :
    recessionConeFn f = {0} ↔ ¬ ∃ y : Rn n, IsDirectionOfRecession f y := by
  constructor
  · rintro h ⟨y, hy0, hy⟩
    exact hy0 (by
      rw [← Set.mem_singleton_iff, ← h]
      exact forall_antitone_iff_recessionFn_nonpos.1 hy)
  · intro h
    refine Set.eq_singleton_iff_unique_mem.2 ⟨recessionFn_apply_zero_le f, fun z hz => ?_⟩
    by_contra hz0
    exact h ⟨z, hz0, forall_antitone_iff_recessionFn_nonpos.2 hz⟩

/-- **"`f` and `C` have no direction of recession in common"**, the hypothesis of Theorem 27.3,
against the backbone's `0⁺f ∩ 0⁺C = {0}`. -/
theorem recessionConeFn_inter_eq_zero_iff (f : Rn n → EReal) (C : Set (Rn n)) :
    recessionConeFn f ∩ recessionCone C = {0}
      ↔ ¬ ∃ y : Rn n, IsDirectionOfRecession f y ∧ y ∈ recessionCone C := by
  constructor
  · rintro h ⟨y, ⟨hy0, hy⟩, hyC⟩
    exact hy0 (by
      rw [← Set.mem_singleton_iff, ← h]
      exact ⟨forall_antitone_iff_recessionFn_nonpos.1 hy, hyC⟩)
  · intro h
    refine Set.eq_singleton_iff_unique_mem.2
      ⟨⟨recessionFn_apply_zero_le f, zero_mem_recessionCone C⟩, fun z hz => ?_⟩
    by_contra hz0
    exact h ⟨z, ⟨hz0, forall_antitone_iff_recessionFn_nonpos.2 hz.1⟩, hz.2⟩

end Vocabulary

/-! ### The section's opening remarks (book, lines 10405–10417)

Four unnumbered facts the section states before Theorem 27.1 and then uses throughout. The third
is one of the most quoted sentences in the book. -/

section Opening

variable {f : Rn n → EReal} {x : Rn n}

/-- **Book, line 10405**: the minimum set of `f` is a convex subset of `ℝⁿ`.

Specialises `convex_argmin`. It is a level set of `f` whenever it is nonempty
(`argmin_eq_setOf_le`), which is the book's reason. -/
theorem convex_argmin_surface (hf : ConvexFn f) : Convex ℝ (argmin f) :=
  convex_argmin hf

/-- **Book, line 10405**: the minimum set is closed when `f` is closed. -/
theorem isClosed_argmin (hf : ClosedProperConvexFn f) : IsClosed (argmin f) := by
  rcases Set.eq_empty_or_nonempty (argmin f) with hE | ⟨a, ha⟩
  · rw [hE]; exact isClosed_empty
  · obtain ⟨x₀, hx₀⟩ := hf.proper.dom_nonempty
    obtain ⟨μ, hμ⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot a)
      (lt_of_le_of_lt (ha x₀) (mem_dom.1 hx₀))
    rw [argmin_eq_setOf_le ha hμ]
    exact (lowerSemicontinuous_iff_isClosed_le.1 hf.lowerSemicontinuous) μ

/-- **Book, line 10405**: the minimum set contains at most one point when `f` is strictly convex on
`dom f`.

The book asserts this in passing. The argument is the one the phrase suggests: two distinct
minimisers lie in `dom f` — a minimiser of a proper `f` has a finite value — and their midpoint
would have a *strictly* smaller value. -/
theorem subsingleton_argmin_of_strictConvexOnFn (hp : Proper f)
    (hs : StrictConvexOnFn f (dom f)) : (argmin f).Subsingleton := by
  intro x hx y hy
  by_contra hne
  obtain ⟨x₀, hx₀⟩ := hp.dom_nonempty
  have hxd : x ∈ dom f := mem_dom.2 (lt_of_le_of_lt (hx x₀) (mem_dom.1 hx₀))
  have hyd : y ∈ dom f := mem_dom.2 (lt_of_le_of_lt (hy x₀) (mem_dom.1 hx₀))
  obtain ⟨μ, hμ⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) (mem_dom.1 hxd)
  have hxy : f x = f y := le_antisymm (hx y) (hy x)
  have hstrict := hs hxd hyd hne (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  rw [← hxy, hμ] at hstrict
  have hval : ((1 / 2 : ℝ) : EReal) * (μ : EReal) + ((1 / 2 : ℝ) : EReal) * (μ : EReal)
      = (μ : EReal) := by
    rw [Tdaf.EReal.coe_mul_coe, ← _root_.EReal.coe_add, _root_.EReal.coe_eq_coe_iff]
    ring
  rw [hval] at hstrict
  exact absurd (hμ ▸ hx ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) (not_le.2 hstrict)

/-- **Book, line 10409**: `x` belongs to the minimum set of `f` exactly when `0 ∈ ∂f(x)`.

"True simply by the definition of subgradient", as the book says: `argmin f` unfolds to the
subgradient inequality at `x* = 0`. Specialises `mem_argmin_iff_zero_mem_subgradient`. -/
theorem mem_argmin_iff_zero_mem_subgradient_surface (f : Rn n → EReal) (x : Rn n) :
    x ∈ argmin f ↔ (0 : Rn n) ∈ subgradient (pairing n) f x :=
  mem_argmin_iff_zero_mem_subgradient (pairing n) f x

/-- **Book, line 10411**: by Theorem 23.2, `0 ∈ ∂f(x)` exactly when `f` is finite at `x` and
`f'(x; y) ≥ 0` for every `y`. -/
theorem mem_argmin_iff_zero_le_dirDeriv (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    x ∈ argmin f ↔ ∀ y : Rn n, 0 ≤ dirDeriv f x y := by
  rw [mem_argmin_iff_zero_mem_subgradient_surface, mem_subgradient_iff_le_dirDeriv ht hb]
  exact forall_congr' fun y => by simp

/-- **Book, line 10417**, unnumbered and one of the most quoted sentences in the subject: a *local*
minimum of a proper convex function is a *global* minimum.

Rockafellar routes it through Theorem 23.2 — the directional derivatives see only an arbitrarily
small neighbourhood, so `f'(x; y) ≥ 0` for every `y`, and `0 ∈ ∂f(x)`. The proof here is the
underlying convexity estimate directly: for any `z`, a short enough step from `x` towards `z` stays
in the ball, and the convexity inequality along `[x, z]` transfers the local bound to `z`. -/
theorem mem_argmin_of_localMin (hf : ConvexFn f) (hp : Proper f) (hx : x ∈ dom f)
    {ε : ℝ} (hε : 0 < ε) (hloc : ∀ z : Rn n, dist z x < ε → f x ≤ f z) : x ∈ argmin f := by
  obtain ⟨μ, hμ⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) (mem_dom.1 hx)
  intro z
  rcases eq_or_ne (f z) ⊤ with hz | hz
  · rw [hz]; exact le_top
  obtain ⟨ν, hν⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot z)
    (lt_top_iff_ne_top.2 hz)
  have hr : (0 : ℝ) ≤ ‖z - x‖ := norm_nonneg _
  set t : ℝ := min 1 (ε / (2 * (‖z - x‖ + 1))) with htdef
  have hden : (0 : ℝ) < 2 * (‖z - x‖ + 1) := by positivity
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htr : t * ‖z - x‖ < ε := by
    have h1 : t ≤ ε / (2 * (‖z - x‖ + 1)) := min_le_right _ _
    have h2 : t * ‖z - x‖ ≤ ε / (2 * (‖z - x‖ + 1)) * ‖z - x‖ :=
      mul_le_mul_of_nonneg_right h1 hr
    have h3 : ε / (2 * (‖z - x‖ + 1)) * ‖z - x‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    linarith
  have hdist : dist (x + t • (z - x)) x < ε := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    exact htr
  have hcombo := hf.epi_combo (x := x) (y := z) (μ := μ) (ν := ν) (le_of_eq hμ) (le_of_eq hν)
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
  have hpt : (1 - t) • x + t • z = x + t • (z - x) := by module
  rw [hpt] at hcombo
  have hchain : (μ : EReal) ≤ (((1 - t) * μ + t * ν : ℝ) : EReal) :=
    le_trans (hμ ▸ hloc _ hdist) hcombo
  rw [_root_.EReal.coe_le_coe_iff] at hchain
  rw [hμ, hν, _root_.EReal.coe_le_coe_iff]
  nlinarith

end Opening

/-! ### Theorem 27.1(a): the infimum is `-f*(0)` -/

section Theorem271

variable {f : Rn n → EReal}

/-- **Rockafellar, Theorem 27.1(a)** (book, line 10423): `inf f = -f*(0)`.

Specialises `iInf_eq_neg_conj_zero`, which needs **no hypothesis at all** — not the "closed proper
convex" of the theorem's preamble, nor even convexity. `f*(0) = ⨆ x (⟨x, 0⟩ - f x) = -(⨅ x, f x)`
is a reindexing of a supremum. Rockafellar's own proof says as much ("by the definition of `f*(0)`
in §12"); the standing hypothesis is there for the other eight clauses. -/
theorem theorem_27_1_a (f : Rn n → EReal) : (⨅ x, f x) = -(conj (pairing n) f 0) :=
  iInf_eq_neg_conj_zero (pairing n) f

/-- **Rockafellar, Theorem 27.1(a)**, second sentence: `f` is bounded below exactly when
`0 ∈ dom f*`. Also hypothesis-free. -/
theorem theorem_27_1_a_bddBelow (f : Rn n → EReal) :
    (⊥ : EReal) < ⨅ x, f x ↔ (0 : Rn n) ∈ dom (conj (pairing n) f) :=
  (zero_mem_dom_conj_iff (pairing n) f).symm

/-! ### Theorem 27.1(b): the minimum set is `∂f*(0)` -/

/-- **Rockafellar, Theorem 27.1(b)** (book, line 10425), first sentence: the minimum set of a
closed convex `f` is `∂f*(0)`.

Specialises `argmin_eq_subgradient_conj_zero`, which is Theorem 23.5 at the origin: `x ∈ ∂f*(0)`
says `f*(0) + f**(x) ≤ ⟨x, 0⟩ = 0`, and Fenchel–Moreau turns `f**` back into `f`. Properness is
not needed — the `EReal` step is `EReal.le_sub_iff_add_le` at `c = 0`, and `0` is neither `⊥` nor
`⊤`. -/
theorem theorem_27_1_b (hf : ConvexFn f) (hc : ClosedFn f) :
    argmin f = subgradient (pairing n) (conj (pairing n) f) 0 := by
  rw [argmin_eq_subgradient_conj_zero (B := pairing n) hf hc, subgradient_flip_pairing]

/-- **Rockafellar, Theorem 27.1(b)**, second sentence: the infimum of `f` is attained exactly when
`f*` is subdifferentiable at the origin. -/
theorem theorem_27_1_b_attained (hf : ConvexFn f) (hc : ClosedFn f) :
    (argmin f).Nonempty ↔ (subgradient (pairing n) (conj (pairing n) f) 0).Nonempty := by
  rw [theorem_27_1_b hf hc]

/-- **Rockafellar, Theorem 27.1(b)**, third sentence: `0 ∈ ri (dom f*)` is enough for the infimum
to be attained. This is Theorem 23.4 for `f*` at the origin. -/
theorem theorem_27_1_b_relint (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f)
    (h0 : (0 : Rn n) ∈ ri (dom (conj (pairing n) f))) : (argmin f).Nonempty := by
  rw [theorem_27_1_b hf hc]
  exact subgradient_nonempty_of_mem_relint_dom (B := pairing n) (convexFn_conj (pairing n) f)
    (proper_conj ⟨hf, hc, hp⟩) h0

/-- **Rockafellar, Theorem 27.1(b)**, last sentence: `0 ∈ ri (dom f*)` exactly when every direction
of recession of `f` is a direction in which `f` is constant.

Specialises `zero_mem_relint_dom_conj_iff_recessionConeFn_subset_constancySpace`, the `ri` twin of
Theorem 27.1(d)'s `zero_mem_interior_dom_conj_iff_recessionConeFn_eq_zero`. Corollary 8.6.1
(`mem_constancySpace_iff`, §8) is what makes `constancySpace f` the book's phrase. -/
theorem theorem_27_1_b_constancy (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    (0 : Rn n) ∈ ri (dom (conj (pairing n) f)) ↔ recessionConeFn f ⊆ constancySpace f :=
  zero_mem_relint_dom_conj_iff_recessionConeFn_subset_constancySpace (B := pairing n) hf hc hp

/-! ### Theorem 27.1(c): finite but unattained -/

/-- **Rockafellar, Theorem 27.1(c)** (book, line 10427): the infimum of a closed proper convex `f`
is finite but unattained exactly when `f*(0)` is finite and `f*'(0; y) = -∞` for some `y`.

Specialises `iInf_ne_bot_and_argmin_eq_empty_iff`. **Only one of the book's two finiteness bounds
carries information on each side.** `f*(0) ≠ ⊥` holds for every proper `f` (`conj_ne_bot`) and
symmetrically `inf f ≠ ⊤` does too (`iInf_ne_top`), so spelling "finite" out in full would put a
redundant conjunct on each side of the equivalence. -/
theorem theorem_27_1_c (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    ((⨅ x, f x) ≠ ⊥ ∧ argmin f = ∅)
      ↔ (conj (pairing n) f 0 ≠ ⊤ ∧ ∃ y : Rn n, dirDeriv (conj (pairing n) f) 0 y = ⊥) :=
  iInf_ne_bot_and_argmin_eq_empty_iff (B := pairing n) hf hc hp

/-- The two bounds Theorem 27.1(c) leaves out, recorded so that the reading "finite" can be checked
against the statement: for a proper `f`, `inf f ≠ ⊤` and `f*(0) ≠ ⊥` hold unconditionally. -/
theorem theorem_27_1_c_free (hp : Proper f) :
    (⨅ x, f x) ≠ ⊤ ∧ conj (pairing n) f 0 ≠ ⊥ :=
  ⟨iInf_ne_top hp, conj_ne_bot hp.dom_nonempty 0⟩

/-! ### Theorem 27.1(d): a nonempty bounded minimum set -/

/-- **Rockafellar, Theorem 27.1(d)** (book, line 10429), first sentence: the minimum set of a
closed proper convex `f` is nonempty and bounded exactly when `0 ∈ int (dom f*)`.

Specialises `argmin_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj`. **Rockafellar's proof
cites Corollary 13.3.4 and the backbone's does not need it**: Corollary 14.2.2 already says that
every level set is bounded exactly when the origin is interior to `dom f*`, and Theorem 27.2 turns
that into existence of a minimiser. -/
theorem theorem_27_1_d (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    ((argmin f).Nonempty ∧ IsBounded (argmin f))
      ↔ (0 : Rn n) ∈ interior (dom (conj (pairing n) f)) :=
  argmin_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj (B := pairing n) hf hc hp

/-- **Rockafellar, Theorem 27.1(d)**, second sentence: that holds exactly when `f` has no
directions of recession. -/
theorem theorem_27_1_d_recession (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    (0 : Rn n) ∈ interior (dom (conj (pairing n) f)) ↔ ¬ ∃ y : Rn n, IsDirectionOfRecession f y :=
  (zero_mem_interior_dom_conj_iff_recessionConeFn_eq_zero (B := pairing n) hf hc hp).trans
    (recessionConeFn_eq_zero_iff f)

/-- **Rockafellar, Theorem 27.1(d)** in the form Theorem 30.4(g) states it: *some* level set of `f`
is nonempty and bounded exactly when the minimum set is. -/
theorem theorem_27_1_d_setOf_le (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    ((argmin f).Nonempty ∧ IsBounded (argmin f))
      ↔ ∃ α : ℝ, {x : Rn n | f x ≤ (α : EReal)}.Nonempty ∧
          IsBounded {x : Rn n | f x ≤ (α : EReal)} :=
  argmin_nonempty_and_isBounded_iff_exists_setOf_le (B := pairing n) hf hc hp

/-! ### Theorem 27.1(e): a unique minimiser is `∇f*(0)` -/

/-- **Rockafellar, Theorem 27.1(e)** (book, line 10431): the minimum set of a closed proper convex
`f` consists of the unique vector `x` exactly when `f*` is differentiable at the origin with
`∇f*(0) = x`.

Clause (b) composed with Theorem 25.1 (`theorem_25_1`, §25), exactly as the book's one-line proof
says. Nothing here needs reflexivity: `∂f*(0)` is `subgradient (pairing n) f* 0`, a subset of `ℝⁿ`,
because the pairing is what says what a dual variable of `f*` is. The backbone's
`argmin_eq_singleton_iff_hasGradientAt_conj_zero` is the same statement over an arbitrary
compatible pairing, where `∇f*(0)` is the continuous functional `⟨·, x⟩` rather than the vector
`x`. -/
theorem theorem_27_1_e (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) {x : Rn n} :
    argmin f = {x} ↔ HasGradientVecAt (conj (pairing n) f) x 0 := by
  rw [theorem_27_1_b hf hc,
    theorem_25_1 (convexFn_conj (pairing n) f) (proper_conj ⟨hf, hc, hp⟩)]

/-- **Rockafellar, Theorem 27.1(e)**, as an existence statement: the infimum is attained at a
unique point exactly when `f*` is differentiable at the origin. -/
theorem theorem_27_1_e_differentiable (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    (∃ x : Rn n, argmin f = {x}) ↔ DifferentiableAtFn (conj (pairing n) f) 0 := by
  rw [differentiableAtFn_iff_exists_hasGradientVecAt]
  exact exists_congr fun _ => theorem_27_1_e hf hc hp

/-- **Rockafellar, Theorem 27.1(e)**, the identification `x = ∇f*(0)`: the unique minimiser is
computed by `gradientVec` (§25). -/
theorem theorem_27_1_e_gradientVec (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) {x : Rn n}
    (h : argmin f = {x}) : x = gradientVec (conj (pairing n) f) 0 :=
  ((theorem_27_1_e hf hc hp).1 h).gradientVec_eq.symm

/-! ### Theorem 27.1(f): all nonempty level sets share a recession cone -/

/-- **Rockafellar, Theorem 27.1(f)** (book, line 10433), first two sentences: every nonempty level
set of a closed proper convex `f` has the recession cone of `f`.

This is Theorem 8.7, already on the surface as `theorem_8_7_recessionCone`; it is restated here
because clause (f) is where §27 uses it. -/
theorem theorem_27_1_f_setOf_le (hf : ClosedProperConvexFn f) {α : ℝ}
    (hne : {x : Rn n | f x ≤ (α : EReal)}.Nonempty) :
    recessionCone {x : Rn n | f x ≤ (α : EReal)} = recessionConeFn f :=
  recessionCone_setOf_le hf.convex hf.isClosed_epi hne

/-- **Rockafellar, Theorem 27.1(f)**, the parenthesis: the minimum set, when nonempty, is itself a
level set, so it too has the recession cone of `f`. -/
theorem theorem_27_1_f_argmin (hf : ClosedProperConvexFn f) {a : Rn n} (ha : a ∈ argmin f)
    {μ : ℝ} (hμ : f a = (μ : EReal)) : recessionCone (argmin f) = recessionConeFn f := by
  rw [argmin_eq_setOf_le ha hμ]
  exact theorem_27_1_f_setOf_le hf ⟨a, le_of_eq hμ⟩

/-- **Rockafellar, Theorem 27.1(f)**, last sentence: that common recession cone is the polar of the
convex cone generated by `dom f*`.

Specialises `recessionCone_setOf_le_eq_polarCone_dom_conj`, which is Theorem 8.7 composed with
Theorem 14.2. `polarCone_hull` is what lets the book's "cone generated by `dom f*`" be replaced by
`dom f*` itself: polarity does not see the cone hull. -/
theorem theorem_27_1_f_polarCone (hf : ClosedProperConvexFn f) {α : ℝ}
    (hne : {x : Rn n | f x ≤ (α : EReal)}.Nonempty) :
    recessionCone {x : Rn n | f x ≤ (α : EReal)}
      = polarCone (pairing n)
          (PointedCone.hull ℝ (dom (conj (pairing n) f)) : Set (Rn n)) := by
  rw [polarCone_hull, ← polarCone_flip_pairing]
  exact recessionCone_setOf_le_eq_polarCone_dom_conj (B := pairing n) hf.convex hf.closed
    hf.proper hne

/-! ### Theorem 27.1(g): support functions of the level sets -/

/-- **Rockafellar, Theorem 27.1(g)** (book, line 10435), first sentence: for each real `α` the
support function of `lev_α f` is the closure of the positively homogeneous convex function
generated by `f* + α`.

Specialises `supportFn_setOf_le`. **It does not need a shifted-function API**, although the book's
proof is "Theorem 13.5 applied to `f - α`": Corollary 13.2.1 computes the closure of a generated
function as a support function with no hypotheses, and the level set it produces is
`{x | f**(x) - α ≤ 0}`. -/
theorem theorem_27_1_g_setOf_le (hf : ConvexFn f) (hc : ClosedFn f) (α : ℝ) :
    supportFn (pairing n) {x : Rn n | f x ≤ (α : EReal)}
      = clFn (posHomGen fun y => conj (pairing n) f y + (α : EReal)) :=
  supportFn_setOf_le (B := pairing n) hf hc α

/-- **Rockafellar, Theorem 27.1(g)**, second sentence: when `f` is bounded below, the support
function of the minimum set is the closure of `f*'(0; ·)`.

Clause (b) plus Theorem 23.2. "Bounded below" enters as `f*(0) ≠ ⊤`, which is clause (a). -/
theorem theorem_27_1_g_argmin (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f)
    (hbdd : (⊥ : EReal) < ⨅ x, f x) :
    supportFn (pairing n) (argmin f) = clFn (dirDeriv (conj (pairing n) f) 0) :=
  supportFn_argmin (B := pairing n) hf hc hp
    (lt_top_iff_ne_top.1 (mem_dom.1 ((theorem_27_1_a_bddBelow f).1 hbdd)))

/-! ### Theorem 27.1(h): the limit of the support functions -/

/-- **Rockafellar, Theorem 27.1(h)** (book, line 10437): if `inf f` is finite then
`lim_{α ↓ inf f} δ*(y | lev_α f) = f*'(0; y)` for every `y`.

Specialises `iInf_supportFn_setOf_le`. **The limit is an infimum**: the level sets increase with
`α`, so their support functions do too, and the backbone states the monotone limit as the infimum
it is — no filter is needed. The reindexing `α = inf f + ε` is Rockafellar's own, made inside his
proof when he identifies `lev_α f` with `∂_ε f*(0)`; that identification is
`epsSubgradient_conj_zero`. -/
theorem theorem_27_1_h (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) {μ : ℝ}
    (hμ : (⨅ x, f x) = (μ : EReal)) (y : Rn n) :
    (⨅ ε ∈ Ioi (0 : ℝ), supportFn (pairing n) {z : Rn n | f z ≤ ((μ + ε : ℝ) : EReal)} y)
      = dirDeriv (conj (pairing n) f) 0 y :=
  iInf_supportFn_setOf_le (B := pairing n) hf hc hp hμ y

/-- The identification the proof of Theorem 27.1(h) runs on: the level sets of `f` above its
infimum are the ε-subdifferentials of `f*` at the origin. Rockafellar states it inside the proof
and does not number it. -/
theorem theorem_27_1_h_epsSubgradient (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) {μ : ℝ}
    (hμ : (⨅ x, f x) = (μ : EReal)) (ε : ℝ) :
    epsSubgradient (pairing n) ε (conj (pairing n) f) 0
      = {z : Rn n | f z ≤ ((μ + ε : ℝ) : EReal)} := by
  rw [← epsSubgradient_conj_zero (B := pairing n) hf hc hp hμ ε, flip_pairing]

/-! ### Theorem 27.1(i): the origin in the closure of `dom f*` -/

/-- **Rockafellar, Theorem 27.1(i)** (book, line 10443), first sentence: `0 ∈ cl (dom f*)` exactly
when `(f0⁺)(y) ≥ 0` for every `y`.

Specialises `zero_mem_closure_dom_conj_iff`, which lives in `Duality/Level.lean` beside the
Corollary 13.3.4 it is the origin-case of. -/
theorem theorem_27_1_i (hf : ClosedProperConvexFn f) :
    (0 : Rn n) ∈ closure (dom (conj (pairing n) f)) ↔ ∀ y : Rn n, 0 ≤ recessionFn f y :=
  zero_mem_closure_dom_conj_iff (B := pairing n) hf

/-- **Rockafellar, Theorem 27.1(i)**, second sentence: `0 ∉ cl (dom f*)` exactly when `f` decreases
at a uniform positive rate along some nonzero direction.

Specialises `zero_notMem_closure_dom_conj_iff`. Two remarks the book does not make: `y ≠ 0` is
automatic, because at `y = 0` the inequality at `λ = 1` would read `0 ≤ -ε` at any point of the
non-empty effective domain; and restricting `x` to `dom f` costs nothing. -/
theorem theorem_27_1_i_notMem (hf : ClosedProperConvexFn f) :
    (0 : Rn n) ∉ closure (dom (conj (pairing n) f)) ↔
      ∃ y : Rn n, y ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ x ∈ dom f, ∀ a : ℝ, 0 ≤ a → f (x + a • y) ≤ f x - ((a * ε : ℝ) : EReal) :=
  zero_notMem_closure_dom_conj_iff (B := pairing n) hf

/-- The book's remark at line 10491, which is clauses (a) and (i) put together: `f` can recede
nowhere at a negative rate and still be unbounded below, and that is exactly the case
`0 ∈ cl (dom f*) \ dom f*`. -/
theorem theorem_27_1_ai (hf : ClosedProperConvexFn f) :
    ((∀ y : Rn n, 0 ≤ recessionFn f y) ∧ (⨅ x, f x) = ⊥)
      ↔ ((0 : Rn n) ∈ closure (dom (conj (pairing n) f)) ∧
          (0 : Rn n) ∉ dom (conj (pairing n) f)) := by
  rw [theorem_27_1_i hf, ← theorem_27_1_a_bddBelow f, not_lt, le_bot_iff]

end Theorem271

/-! ### Theorem 27.2: existence, compactness and well-posedness -/

section Theorem272

variable {f : Rn n → EReal}

/-- **Rockafellar, Theorem 27.2** (book, line 10453), first sentence: a closed proper convex
function with no direction of recession has a finite, attained infimum.

Specialises `exists_iInf_eq_coe` and `argmin_nonempty_of_recessionConeFn_eq_zero`. The backbone's
proof is Mathlib's lower-semicontinuous extreme value theorem on a level set, which Theorem 8.7 and
Theorem 8.4 make compact. -/
theorem theorem_27_2_finite (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) : ∃ μ : ℝ, (⨅ z, f z) = (μ : EReal) :=
  exists_iInf_eq_coe hf.convex hf.closed hf.proper ((recessionConeFn_eq_zero_iff f).2 hrec)

/-- **Rockafellar, Theorem 27.2**, the attainment. -/
theorem theorem_27_2_attained (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) : (argmin f).Nonempty :=
  argmin_nonempty_of_recessionConeFn_eq_zero hf.convex hf.closed hf.proper
    ((recessionConeFn_eq_zero_iff f).2 hrec)

/-- **Rockafellar, Theorem 27.2**, last clause: the minimum set is a nonempty closed bounded convex
set. Closed and bounded is stated as compact, which in `ℝⁿ` is the same thing. -/
theorem theorem_27_2_argmin (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) :
    (argmin f).Nonempty ∧ IsCompact (argmin f) ∧ Convex ℝ (argmin f) :=
  ⟨theorem_27_2_attained hf hrec,
    isCompact_argmin_of_recessionConeFn_eq_zero hf.convex hf.closed hf.proper
      ((recessionConeFn_eq_zero_iff f).2 hrec),
    convex_argmin hf.convex⟩

/-- **Rockafellar, Theorem 27.2**, the well-posedness clause: for every `ε > 0` there is a `δ > 0`
such that every `x` with `f x ≤ inf f + δ` lies within `ε` of the minimum set.

Specialises `exists_pos_forall_exists_mem_argmin_dist_lt`. **Rockafellar's nested-compactness
argument is avoided.** He intersects a nest of closed bounded sets `S_δ` and extracts a common
point; the backbone applies the extreme value theorem once more, to the compact set
`lev_{inf f + 1} f \ (M + ε · int B)`: if it is empty, `δ = 1` works, and otherwise its minimiser
`b` is not a minimiser of `f`, so any `δ` with `inf f + δ < f b` will do. -/
theorem theorem_27_2_wellPosed (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : Rn n, f x ≤ (⨅ z, f z) + (δ : EReal) →
      ∃ z ∈ argmin f, dist x z < ε :=
  exists_pos_forall_exists_mem_argmin_dist_lt hf.convex hf.closed hf.proper
    ((recessionConeFn_eq_zero_iff f).2 hrec) hε

/-! ### Corollary 27.2.1 -/

/-- **Rockafellar, Corollary 27.2.1** (book, line 10457), first assertion: a minimising sequence of
a closed proper convex function with no direction of recession is bounded.

**The book states this corollary with no proof at all.** The argument is the well-posedness clause
of Theorem 27.2 with `ε = 1`: past some index the whole sequence lies within distance `1` of the
compact minimum set, and the finitely many earlier terms are a finite set. -/
theorem corollary_27_2_1_isBounded (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) {u : ℕ → Rn n}
    (hu : Tendsto (fun i => f (u i)) atTop (𝓝 (⨅ z, f z))) : IsBounded (Set.range u) :=
  isBounded_range_of_tendsto_iInf hf.convex hf.closed hf.proper
    ((recessionConeFn_eq_zero_iff f).2 hrec) hu

/-- **Rockafellar, Corollary 27.2.1**, second assertion: every cluster point of a minimising
sequence belongs to the minimum set.

Also unproved in the book. The backbone's `mem_argmin_of_mapClusterPt` is stated for an **arbitrary
filter**, of which Rockafellar's sequential `atTop` is one instance; only
`corollary_27_2_1_isBounded`, whose conclusion is about the range of a *sequence*, needs `ℕ`. -/
theorem corollary_27_2_1_clusterPt (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) {u : ℕ → Rn n}
    (hu : Tendsto (fun i => f (u i)) atTop (𝓝 (⨅ z, f z))) {x : Rn n}
    (hx : MapClusterPt x atTop u) : x ∈ argmin f :=
  mem_argmin_of_mapClusterPt hf.convex hf.closed hf.proper
    ((recessionConeFn_eq_zero_iff f).2 hrec) hu hx

/-- The substance of Corollary 27.2.1, and the lemma both of its assertions are read off: along any
minimising net the distance to the minimum set tends to `0`. -/
theorem corollary_27_2_1_infDist (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) {ι : Type*} {l : Filter ι} {u : ι → Rn n}
    (hu : Tendsto (fun i => f (u i)) l (𝓝 (⨅ z, f z))) :
    Tendsto (fun i => Metric.infDist (u i) (argmin f)) l (𝓝 0) :=
  tendsto_infDist_argmin hf.convex hf.closed hf.proper
    ((recessionConeFn_eq_zero_iff f).2 hrec) hu

/-! ### Corollary 27.2.2 -/

/-- **Rockafellar, `Corollary 27.2.2`** (book, line 10465; the label is printed in mixed case): if
a closed proper convex function attains its infimum at a unique point `x`, every minimising
sequence converges to `x`.

Specialises `tendsto_of_argmin_eq_singleton`, stated for an arbitrary filter. **No recession
hypothesis is needed**, which is the whole content of the book's one-line proof: a one-point
minimum set is a level set, and Theorem 8.7 forces `0⁺f = {0}`. -/
theorem corollary_27_2_2 (hf : ClosedProperConvexFn f) {a : Rn n} (hM : argmin f = {a})
    {u : ℕ → Rn n} (hu : Tendsto (fun i => f (u i)) atTop (𝓝 (⨅ z, f z))) :
    Tendsto u atTop (𝓝 a) :=
  tendsto_of_argmin_eq_singleton hf.convex hf.closed hf.proper hM hu

end Theorem272

/-! ### Theorem 27.3: minimising over a closed convex set -/

section Theorem273

variable {h : Rn n → EReal} {C : Set (Rn n)}

/-- **Rockafellar, Theorem 27.3** (book, line 10495), the non-polyhedral case: a closed proper
convex `h` attains its infimum over a nonempty closed convex `C` as soon as `h` and `C` have no
direction of recession in common.

Specialises `exists_forall_le_of_recessionConeFn_inter_eq_zero`, which is the book's own argument:
`h + δ(· | C)` is closed proper convex whenever it is not identically `+∞`, its directions of
recession are the common ones (`recessionConeFn_add_indicatorFn`, Theorem 9.3 against an
indicator), and Theorem 27.2 applies. The degenerate case `dom h ∩ C = ∅` — where `h` is `+∞`
throughout `C` and every point of `C` minimises — is dispatched separately; the book passes over
it in the clause "if `f` is identically `+∞`". -/
theorem theorem_27_3 (hh : ClosedProperConvexFn h) (hC : Convex ℝ C) (hCc : IsClosed C)
    (hCne : C.Nonempty)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession h y ∧ y ∈ recessionCone C) :
    ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z :=
  exists_forall_le_of_recessionConeFn_inter_eq_zero hh hC hCc hCne
    ((recessionConeFn_inter_eq_zero_iff h C).2 hrec)

/-- **Rockafellar, Theorem 27.3**, the polyhedral refinement: for polyhedral `C` it is enough that
every common direction of recession of `h` and `C` be a direction in which `h` is *constant*.

**The book proves this from Helly's theorem** in the form of Theorem 21.5, applied to `C` together
with the level sets `lev_α h`, `α > inf_C h`. The backbone
(`exists_forall_le_of_polyhedral_of_inter_subset_constancySpace`) does not: the directions of
constancy of `h` form a subspace, and projecting `ℝⁿ` along it leaves `h` untouched while
collapsing the common recession cone to `{0}`, which is the hypothesis of the non-polyhedral case.
Polyhedrality of `C` enters exactly once, through `Polyhedral.recessionCone_image` — a linear map
commutes with `0⁺` on a polyhedral set and, in general, on no other kind. Theorem 21.5 is still not
formalised, and this clause no longer waits for it. -/
theorem theorem_27_3_polyhedral (hh : ClosedProperConvexFn h) (hC : Polyhedral C)
    (hCne : C.Nonempty)
    (hrec : recessionConeFn h ∩ recessionCone C ⊆ constancySpace h) :
    ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z :=
  exists_forall_le_of_polyhedral_of_inter_subset_constancySpace hh hC hCne hrec

/-- **Rockafellar, Theorem 27.3**, non-polyhedral case, in a form the book does not state but its
proof gives: for a general closed convex `C` the hypothesis may be weakened from "no common
direction of recession" to "every common direction of recession is one in which `h` is constant
*and* `C` is linear".

This is strictly stronger than the printed non-polyhedral case and strictly weaker than the
polyhedral refinement, and it is the version the projection argument proves for free. -/
theorem theorem_27_3_lineality (hh : ClosedProperConvexFn h) (hC : Convex ℝ C) (hCc : IsClosed C)
    (hCne : C.Nonempty)
    (hrec : recessionConeFn h ∩ recessionCone C ⊆ constancySpace h ∩ linealitySpace C) :
    ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z :=
  exists_forall_le_of_inter_subset_constancySpace_inter_linealitySpace hh hC hCc hCne hrec

/-! ### Corollary 27.3.1 -/

/-- **Rockafellar, Corollary 27.3.1** (book, line 10505): if every direction of recession of a
closed proper convex `h` is a direction in which `h` is *affine*, then `h` attains its infimum
relative to any polyhedral convex set `C` on which it is bounded below.

Specialises `exists_forall_le_of_polyhedral_of_recessionConeFn_subset_linealitySpaceFn`. The lower
bound is what upgrades "affine along `y`" to "constant along `y`": the slope
`ν = (h0⁺)(y) = -(h0⁺)(-y) ≤ 0` along a half-line that stays in `C` forces `ν = 0`. **The bound
cannot be dropped** — `h(ξ₁, ξ₂) = ξ₁` is affine in every direction and its infimum over
`C = {x | ξ₂ = 0}` is `-∞`.

The hypothesis holds for every affine or convex quadratic `h`, and more generally whenever
`dom h*` is an affine set (Corollary 13.3.2), which is the book's parenthesis. -/
theorem corollary_27_3_1 (hh : ClosedProperConvexFn h) (hC : Polyhedral C) (hCne : C.Nonempty)
    (hrec : recessionConeFn h ⊆ linealitySpaceFn h) {β : ℝ}
    (hbdd : ∀ x ∈ C, (β : EReal) ≤ h x) : ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z :=
  exists_forall_le_of_polyhedral_of_recessionConeFn_subset_linealitySpaceFn hh hC hCne hrec hbdd

/-- The unconstrained case of the polyhedral refinement, which the book does not separate out: a
closed proper convex function whose recession cone consists of directions of constancy attains its
infimum. -/
theorem corollary_27_3_1_unconstrained (hh : ClosedProperConvexFn h)
    (hrec : recessionConeFn h ⊆ constancySpace h) : (argmin h).Nonempty :=
  argmin_nonempty_of_recessionConeFn_subset_constancySpace hh hrec

/-! ### Corollary 27.3.2 -/

/-- **Rockafellar, Corollary 27.3.2** (book, line 10523): a polyhedral convex function attains its
infimum relative to any polyhedral convex set on which it is bounded below.

Specialises `exists_forall_le_of_polyhedralFn_of_polyhedral`. **The book derives this from
Corollary 27.3.1, hence from Helly's theorem, and it needs neither**: restricting `h` to `C` cuts
the epigraph down by Rockafellar's own vertical prism, so the restriction is again polyhedral, and
the finitely generated description `epi h = conv P + cone D` (Theorem 19.1) then minimises the
vertical coordinate at one of the finitely many generating points. -/
theorem corollary_27_3_2 (hh : PolyhedralFn h) (hC : Polyhedral C) (hCne : C.Nonempty)
    (hbdd : (⊥ : EReal) < ⨅ x ∈ C, h x) : ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z :=
  exists_forall_le_of_polyhedralFn_of_polyhedral hh hC hCne hbdd

/-- Corollary 27.3.2 unconstrained: a polyhedral convex function bounded below attains its
infimum. Neither closedness nor properness is assumed — boundedness below already excludes `-∞`,
and `h ≡ +∞` is minimised everywhere. -/
theorem corollary_27_3_2_unconstrained (hh : PolyhedralFn h) (hbdd : (⊥ : EReal) < ⨅ x, h x) :
    (argmin h).Nonempty :=
  argmin_nonempty_of_polyhedralFn hh hbdd

end Theorem273

/-! ### Corollary 27.3.3: an arbitrary system of convex inequalities -/

section Corollary2733

variable {ι : Type*} {f₀ : Rn n → EReal} {g : ι → Rn n → EReal}

/-- **Rockafellar, Corollary 27.3.3** (book, line 10527), the non-polyhedral case: a closed proper
convex `f₀` attains its infimum subject to a consistent system `fᵢ x ≤ 0`, `i ∈ I`, of closed
proper convex constraints, provided `f₀` and the `fᵢ` have no direction of recession in common.

The index set is arbitrary — finite or infinite, as the book insists. Specialises
`exists_forall_le_of_forall_le_zero`: the constraint set is the intersection of the level sets
`lev_0 fᵢ`, its recession cone is the intersection of theirs (Theorem 8.7 plus
`recessionCone_iInter`), and Theorem 27.3 applies. -/
theorem corollary_27_3_3 (hf₀ : ClosedProperConvexFn f₀) (hg : ∀ i, ClosedProperConvexFn (g i))
    (hCne : {x : Rn n | ∀ i, g i x ≤ 0}.Nonempty)
    (hrec : recessionConeFn f₀ ∩ ⋂ i, recessionConeFn (g i) = {0}) :
    ∃ x, (∀ i, g i x ≤ 0) ∧ ∀ z, (∀ i, g i z ≤ 0) → f₀ x ≤ f₀ z :=
  exists_forall_le_of_forall_le_zero hf₀ hg hCne hrec

/-! #### The polyhedral refinement

The book splits the index set as `I = I₀ ⊔ (I ∖ I₀)` with `I₀` finite and the `fᵢ` polyhedral on
it. Two index *types* say the same thing and keep every `DecidableEq` out of the statement
(`gotchas.md` SET11); `ι₀` is the book's `I₀`. -/

/-- **Backbone gap**: `Polyhedral (⋂ i ∈ s, S i)` for a `Finset` of polyhedral sets.
`Polyhedral/Ops.lean` has the binary `Polyhedral.inter` and nothing indexed. -/
private theorem polyhedral_biInter {ι : Type*} {S : ι → Set (Rn n)}
    (hS : ∀ i, Polyhedral (S i)) (s : Finset ι) : Polyhedral (⋂ i ∈ s, S i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using polyhedral_univ
  | cons i t hi ih =>
      have hsplit : (⋂ j ∈ Finset.cons i t hi, S j) = S i ∩ ⋂ j ∈ t, S j := by
        ext z
        simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_cons]
        constructor
        · intro hz
          exact ⟨hz i (Or.inl rfl), fun j hj => hz j (Or.inr hj)⟩
        · rintro ⟨h₁, h₂⟩ j (rfl | hj)
          · exact h₁
          · exact h₂ j hj
      rw [hsplit]
      exact Polyhedral.inter (hS i) ih

/-- **Backbone gap**: the same over a finite index *type*, which is the form a family of
constraints arrives in. -/
private theorem polyhedral_iInter {ι : Type*} [Finite ι] {S : ι → Set (Rn n)}
    (hS : ∀ i, Polyhedral (S i)) : Polyhedral (⋂ i, S i) := by
  obtain ⟨hι⟩ := nonempty_fintype ι
  have h : (⋂ i, S i) = ⋂ i ∈ (Finset.univ : Finset ι), S i := by simp
  rw [h]
  exact polyhedral_biInter hS Finset.univ

/-- **Backbone gap**: a level set of a polyhedral convex function is a polyhedral convex set. It is
the preimage of `epi g` under `x ↦ (x, 0)`, so `Polyhedral.comap` is the whole proof;
`Polyhedral/Function.lean` states no level-set lemma. -/
private theorem polyhedral_setOf_le_zero {g : Rn n → EReal} (hg : PolyhedralFn g) :
    Polyhedral {x : Rn n | g x ≤ ((0 : ℝ) : EReal)} := by
  have h : {x : Rn n | g x ≤ ((0 : ℝ) : EReal)} = (LinearMap.inl ℝ (Rn n) ℝ) ⁻¹' epi g := by
    ext z
    exact Iff.rfl
  rw [h]
  exact Polyhedral.comap hg _

/-- **Rockafellar, Corollary 27.3.3**, the polyhedral refinement (book, line 10527, second
sentence): the infimum is attained if the constraints split into a *finite* polyhedral family
`g₀` and an arbitrary family `g₁`, and the only directions of recession common to `f₀` and all the
constraints are directions in which `f₀` and all the `g₁` are constant.

**`api.md` recorded this clause as genuinely needing Helly's theorem in the form of Theorem 21.5.
It does not.** The book's own reduction — put the non-polyhedral constraints into the objective as
`h = f₀ + δ(· | {g₁ ≤ 0})` and the polyhedral ones into the constraint set `C = {g₀ ≤ 0}` — lands
on the polyhedral case of Theorem 27.3, and that case is proved in the backbone by the
constancy-space projection rather than by Helly. What the reduction costs beyond the book's two
lines is bookkeeping: the recession cone of an intersection of level sets (Theorem 8.7 plus
`recessionCone_iInter`), the recession cone of `f₀ + δ(· | D)` (`recessionConeFn_add_indicatorFn`,
Theorem 9.3), and the degenerate branch where `f₀` is `+∞` at every feasible point, which the book
passes over. -/
theorem corollary_27_3_3_polyhedral {ι₀ ι₁ : Type*} [Finite ι₀]
    {g₀ : ι₀ → Rn n → EReal} {g₁ : ι₁ → Rn n → EReal}
    (hf₀ : ClosedProperConvexFn f₀) (hg₀ : ∀ i, PolyhedralFn (g₀ i))
    (hg₁ : ∀ i, ClosedProperConvexFn (g₁ i))
    (hne : {x : Rn n | (∀ i, g₀ i x ≤ 0) ∧ ∀ i, g₁ i x ≤ 0}.Nonempty)
    (hrec : recessionConeFn f₀ ∩ (⋂ i, recessionConeFn (g₀ i)) ∩ (⋂ i, recessionConeFn (g₁ i))
      ⊆ constancySpace f₀ ∩ ⋂ i, constancySpace (g₁ i)) :
    ∃ x : Rn n, ((∀ i, g₀ i x ≤ 0) ∧ ∀ i, g₁ i x ≤ 0) ∧
      ∀ z : Rn n, ((∀ i, g₀ i z ≤ 0) ∧ ∀ i, g₁ i z ≤ 0) → f₀ x ≤ f₀ z := by
  obtain ⟨C, hCdef⟩ : ∃ C : Set (Rn n), C = ⋂ i, {z : Rn n | g₀ i z ≤ ((0 : ℝ) : EReal)} :=
    ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Set (Rn n), D = ⋂ i, {z : Rn n | g₁ i z ≤ ((0 : ℝ) : EReal)} :=
    ⟨_, rfl⟩
  have hmemC : ∀ z : Rn n, z ∈ C ↔ ∀ i, g₀ i z ≤ 0 := by
    intro z; rw [hCdef]; simp
  have hmemD : ∀ z : Rn n, z ∈ D ↔ ∀ i, g₁ i z ≤ 0 := by
    intro z; rw [hDdef]; simp
  obtain ⟨w, hwC, hwD⟩ := hne
  have hwCm : w ∈ C := (hmemC w).2 hwC
  have hwDm : w ∈ D := (hmemD w).2 hwD
  have hC0conv : ∀ i, Convex ℝ {z : Rn n | g₀ i z ≤ ((0 : ℝ) : EReal)} := fun i =>
    (hg₀ i).convexFn.convex_le _
  have hC0closed : ∀ i, IsClosed {z : Rn n | g₀ i z ≤ ((0 : ℝ) : EReal)} := fun i =>
    (polyhedral_setOf_le_zero (hg₀ i)).isClosed
  have hD1conv : ∀ i, Convex ℝ {z : Rn n | g₁ i z ≤ ((0 : ℝ) : EReal)} := fun i =>
    (hg₁ i).convex.convex_le _
  have hD1closed : ∀ i, IsClosed {z : Rn n | g₁ i z ≤ ((0 : ℝ) : EReal)} := fun i =>
    lowerSemicontinuous_iff_isClosed_le.1 (hg₁ i).lowerSemicontinuous 0
  have hCpoly : Polyhedral C := by
    rw [hCdef]; exact polyhedral_iInter fun i => polyhedral_setOf_le_zero (hg₀ i)
  have hDconv : Convex ℝ D := by rw [hDdef]; exact convex_iInter hD1conv
  have hDclosed : IsClosed D := by rw [hDdef]; exact isClosed_iInter hD1closed
  have hCrec : recessionCone C = ⋂ i, recessionConeFn (g₀ i) := by
    have hwCm' : w ∈ ⋂ i, {z : Rn n | g₀ i z ≤ ((0 : ℝ) : EReal)} := hCdef ▸ hwCm
    rw [hCdef, recessionCone_iInter hC0conv hC0closed ⟨w, hwCm'⟩]
    exact Set.iInter_congr fun i => recessionCone_setOf_le (hg₀ i).convexFn (hg₀ i).isClosed_epi
      ⟨w, Set.mem_iInter.1 hwCm' i⟩
  have hDrec : recessionCone D = ⋂ i, recessionConeFn (g₁ i) := by
    have hwDm' : w ∈ ⋂ i, {z : Rn n | g₁ i z ≤ ((0 : ℝ) : EReal)} := hDdef ▸ hwDm
    rw [hDdef, recessionCone_iInter hD1conv hD1closed ⟨w, hwDm'⟩]
    exact Set.iInter_congr fun i => recessionCone_setOf_le (hg₁ i).convex (hg₁ i).isClosed_epi
      ⟨w, Set.mem_iInter.1 hwDm' i⟩
  by_cases hfin : ∃ v : Rn n, ((∀ i, g₀ i v ≤ 0) ∧ ∀ i, g₁ i v ≤ 0) ∧ f₀ v ≠ ⊤
  · obtain ⟨v, ⟨hvC, hvD⟩, hvtop⟩ := hfin
    have hvCm : v ∈ C := (hmemC v).2 hvC
    have hvDm : v ∈ D := (hmemD v).2 hvD
    have hval : ∀ z : Rn n, z ∈ D → (f₀ + indicatorFn D) z = f₀ z := fun z hz => by
      rw [Pi.add_apply, indicatorFn_of_mem hz, add_zero]
    have hdom : (dom (f₀ + indicatorFn D)).Nonempty :=
      ⟨v, mem_dom.2 (by rw [hval v hvDm]; exact lt_top_iff_ne_top.2 hvtop)⟩
    have hh : ClosedProperConvexFn (f₀ + indicatorFn D) :=
      hf₀.add (closedProperConvexFn_indicatorFn hDconv hDclosed ⟨w, hwDm⟩) hdom
    have hhrec : recessionConeFn (f₀ + indicatorFn D) = recessionConeFn f₀ ∩ recessionCone D :=
      recessionConeFn_add_indicatorFn hf₀ hDconv hDclosed ⟨w, hwDm⟩ hdom
    have hkey : recessionConeFn (f₀ + indicatorFn D) ∩ recessionCone C
        ⊆ constancySpace (f₀ + indicatorFn D) := by
      rintro y ⟨hy1, hy2⟩
      rw [hhrec] at hy1
      have hy : y ∈ recessionConeFn f₀ ∩ (⋂ i, recessionConeFn (g₀ i))
          ∩ (⋂ i, recessionConeFn (g₁ i)) :=
        ⟨⟨hy1.1, hCrec ▸ hy2⟩, hDrec ▸ hy1.2⟩
      obtain ⟨hyf, hyg⟩ := hrec hy
      have hyD : ∀ b : Rn n, (b ∈ recessionConeFn f₀ ∧ ∀ i, b ∈ recessionConeFn (g₁ i)) →
          b ∈ recessionConeFn (f₀ + indicatorFn D) := by
        intro b hb
        rw [hhrec]
        exact ⟨hb.1, hDrec ▸ Set.mem_iInter.2 hb.2⟩
      refine mem_constancySpace.2 ⟨hyD y ⟨(mem_constancySpace.1 hyf).1, fun i =>
        (mem_constancySpace.1 (Set.mem_iInter.1 hyg i)).1⟩,
        hyD (-y) ⟨(mem_constancySpace.1 hyf).2, fun i =>
          (mem_constancySpace.1 (Set.mem_iInter.1 hyg i)).2⟩⟩
    obtain ⟨x, hxC, hxmin⟩ :=
      exists_forall_le_of_polyhedral_of_inter_subset_constancySpace hh hCpoly ⟨w, hwCm⟩ hkey
    have hxlt : (f₀ + indicatorFn D) x < ⊤ :=
      lt_of_le_of_lt (hxmin v hvCm) (by rw [hval v hvDm]; exact lt_top_iff_ne_top.2 hvtop)
    have hxD : x ∈ D := by
      by_contra hcon
      rw [Pi.add_apply, indicatorFn_of_notMem hcon,
        _root_.EReal.add_top_of_ne_bot (hf₀.proper.ne_bot x)] at hxlt
      exact absurd hxlt (lt_irrefl ⊤)
    refine ⟨x, ⟨(hmemC x).1 hxC, (hmemD x).1 hxD⟩, fun z hz => ?_⟩
    have hstep := hxmin z ((hmemC z).2 hz.1)
    rwa [hval x hxD, hval z ((hmemD z).2 hz.2)] at hstep
  · push Not at hfin
    exact ⟨w, ⟨hwC, hwD⟩, fun z hz => by rw [hfin w ⟨hwC, hwD⟩, hfin z hz]⟩

end Corollary2733

/-! ### Theorem 27.4: the subdifferential optimality condition -/

section Theorem274

variable {h : Rn n → EReal} {C : Set (Rn n)} {x : Rn n}

/-- **Rockafellar, Theorem 27.4** (book, line 10651), sufficiency: if some `x* ∈ ∂h(x)` has `-x*`
normal to `C` at `x`, then `h` attains its infimum relative to `C` at `x`.

Specialises `le_of_mem_subgradient_of_neg_mem_normalCone`, which **needs no hypothesis at all** —
not properness of `h`, not convexity of `C`, not even that `x ∈ C`. The subgradient inequality
`h x + ⟨z - x, x*⟩ ≤ h z` and the normality inequality `⟨z - x, -x*⟩ ≤ 0` simply add. -/
theorem theorem_27_4_sufficient {y : Rn n} (hy : y ∈ subgradient (pairing n) h x)
    (hn : -y ∈ normalCone (pairing n) C x) {z : Rn n} (hz : z ∈ C) : h x ≤ h z :=
  le_of_mem_subgradient_of_neg_mem_normalCone hy hn hz

/-- **Rockafellar, Theorem 27.4**, necessity under the book's first constraint qualification:
`ri (dom h)` meets `ri C`.

Specialises `exists_mem_subgradient_neg_mem_normalCone` against
`IsExactSum (pairing n) h (δ(· | C))`, supplied by `IsExactSum.of_relint` — Theorem 16.4, whose
`ri (dom δ(· | C)) = ri C` is `dom_indicatorFn`. Rockafellar's proof cites Theorem 23.8 for the
same step. -/
theorem theorem_27_4_necessary (hh : ConvexFn h) (hp : Proper h) (hC : Convex ℝ C)
    (hCne : C.Nonempty) {x₀ : Rn n} (hx₀h : x₀ ∈ ri (dom h)) (hx₀C : x₀ ∈ ri C)
    (hx : x ∈ C) (hmin : ∀ z ∈ C, h x ≤ h z) :
    ∃ y ∈ subgradient (pairing n) h x, -y ∈ normalCone (pairing n) C x :=
  exists_mem_subgradient_neg_mem_normalCone
    (IsExactSum.of_relint (B := pairing n) hh hp (convexFn_indicatorFn.2 hC)
      (proper_indicatorFn.2 hCne) hx₀h (by rw [dom_indicatorFn]; exact hx₀C)) hx hmin

/-- **Rockafellar, Theorem 27.4**, necessity under the book's second constraint qualification: `C`
polyhedral and `ri (dom h)` meets `C` — merely `C`, not `ri C`.

The `IsExactSum` now comes from `IsExactSum.of_polyhedral` (Theorem 20.1) applied to
`δ(· | C) + h`, whose asymmetry is exactly the asymmetry of the qualification: the polyhedral
summand needs only a point of its effective domain, the other needs a relative interior point.
`IsExactSum.symm` puts the summands back in the book's order. -/
theorem theorem_27_4_necessary_polyhedral (hh : ConvexFn h) (hp : Proper h) (hC : Polyhedral C)
    {x₀ : Rn n} (hx₀h : x₀ ∈ ri (dom h)) (hx₀C : x₀ ∈ C)
    (hx : x ∈ C) (hmin : ∀ z ∈ C, h x ≤ h z) :
    ∃ y ∈ subgradient (pairing n) h x, -y ∈ normalCone (pairing n) C x :=
  exists_mem_subgradient_neg_mem_normalCone
    (IsExactSum.symm (IsExactSum.of_polyhedral (B := pairing n) (polyhedralFn_indicatorFn hC)
      (proper_indicatorFn.2 ⟨x₀, hx₀C⟩) hh hp (by rw [dom_indicatorFn]; exact hx₀C) hx₀h))
    hx hmin

/-- The quadratic `w(z) = ½⟨z, z⟩` compares two vectors exactly as their norms do. -/
private theorem quadFn_le_quadFn_iff (u v : Rn n) :
    quadFn (pairing n) u ≤ quadFn (pairing n) v ↔ ‖u‖ ≤ ‖v‖ := by
  rw [quadFn_apply, quadFn_apply, _root_.EReal.coe_le_coe_iff, pairing_apply, pairing_apply,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, div_le_div_iff_of_pos_right two_pos]
  exact pow_le_pow_iff_left₀ (norm_nonneg u) (norm_nonneg v) two_ne_zero

/-- **Book, line 10673**, the headline application of Theorem 27.4 — and the projection theorem:
`x` is the point of a nonempty convex set `C` nearest to `a` exactly when `a - x` is normal to `C`
at `x`.

Minimising the distance to `a` over `C` is minimising the differentiable convex function
`h(u) = ½|u - a|²`, whose subdifferential is the single vector `x - a`
(`subgradient_quadFn_sub`). "The intersection hypothesis of Theorem 27.4 is satisfied trivially",
as the book says: `dom h` is everything, so `ri (dom h)` is everything, and `ri C` is non-empty by
Theorem 6.2 (`Convex.relint_nonempty`). Closedness of `C` is not needed for the
*characterisation* — only for the existence of a nearest point, which is Theorem 27.2. -/
theorem nearest_iff_sub_mem_normalCone (hC : Convex ℝ C) (hCne : C.Nonempty) {a : Rn n}
    (hx : x ∈ C) :
    (∀ z ∈ C, dist a x ≤ dist a z) ↔ a - x ∈ normalCone (pairing n) C x := by
  have hdist : ∀ u : Rn n, dist a u = ‖a - u‖ := fun u => dist_eq_norm a u
  have hdom : dom (fun u => quadFn (pairing n) (a - u)) = Set.univ :=
    Set.eq_univ_iff_forall.2 fun u => mem_dom.2 (lt_top_iff_ne_top.2 (quadFn_ne_top _))
  have hmin : (∀ z ∈ C, dist a x ≤ dist a z) ↔
      ∀ z ∈ C, quadFn (pairing n) (a - x) ≤ quadFn (pairing n) (a - z) := by
    refine forall_congr' fun z => forall_congr' fun _ => ?_
    rw [quadFn_le_quadFn_iff, hdist, hdist]
  rw [hmin]
  constructor
  · intro hmin'
    obtain ⟨x₀, hx₀⟩ := Convex.relint_nonempty hC hCne
    obtain ⟨y, hy, hny⟩ := theorem_27_4_necessary (convexFn_quadFn_sub a) (proper_quadFn_sub a) hC
      hCne (x₀ := x₀) (by rw [hdom, intrinsicInterior_univ]; trivial) hx₀ hx hmin'
    rw [subgradient_quadFn_sub, Set.mem_singleton_iff] at hy
    rwa [hy, neg_sub] at hny
  · intro hn z hz
    refine theorem_27_4_sufficient (h := fun u => quadFn (pairing n) (a - u)) (y := x - a)
      ?_ ?_ hz
    · rw [subgradient_quadFn_sub]
      exact Set.mem_singleton _
    · rwa [neg_sub]

end Theorem274

end Rockafellar
