/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Tdaf.Analysis.Convex.Homogeneous
import Tdaf.Analysis.Convex.Indicator
import Tdaf.Analysis.Convex.Operations.Epi
import Tdaf.Analysis.Convex.Separation

/-!
# Closures of convex functions

Rockafellar's §7, over a real topological vector space `E`. Two operations are introduced: the
lower semicontinuous hull `lscHull f`, whose epigraph is `closure (epi f)`, and the *closure*
`clFn f` of a convex function, which is the hull except that it is flattened to the constant `⊥`
when the hull takes the value `⊥` anywhere.

## Main definitions

* `lscHull f` — the lower semicontinuous hull, `ofEpi (closure (epi f))`.
* `clFn f` — the closure of a convex function.
* `ClosedFn f` — `f` is closed, i.e. `clFn f = f`.
* `ClosedProperConvexFn f` — closed, proper *and* convex, bundled. This is Rockafellar's
  standing hypothesis from §12 onwards and the class `conjEquiv` and `supportEquiv` are
  bijections between.
* `lscHullClosure`, `clFnClosure` — both operations packaged as `ClosureOperator`s on
  `(E → EReal)ᵒᵈ`, with `LowerSemicontinuous` and `ClosedFn` as their closedness predicates.

## Main results

* `lowerSemicontinuous_iff_isClosed_epi`, `lowerSemicontinuous_iff_isClosed_le` —
  **Theorem 7.1**: lower semicontinuity, closed sublevel sets, and a closed epigraph coincide.
* `epi_lscHull` — `epi (lscHull f) = closure (epi f)`, unconditionally. This is the workhorse
  of the file, and it is where `IsEpiLike.closure` is used.
* `isGreatest_lscHull` — the universal property: `lscHull f` is the greatest lower
  semicontinuous minorant of `f`.
* `closedFn_iff` — a function is closed exactly when it is the constant `⊥` or is lower
  semicontinuous and never `⊥`; `closedFn_iff_lowerSemicontinuous` is the proper case.
* `iInf_clFn_eq_iInf` — `f` and `cl f` have the same infimum.
* `ConvexFn.eq_bot_or_eq_top` — **Corollary 7.2.1**, and with it
  `ConvexFn.eq_bot_of_mem_dom`: a lower semicontinuous improper convex function has no finite
  values. This is what replaces Theorem 7.2 outside finite dimensions.
* `exists_affine_le_of_closed_proper` — a **closed** proper convex function on a locally
  convex space has a continuous affine minorant. This is the keystone of Fenchel–Moreau.
* `tendsto_lscHull_along_segment`, `tendsto_along_segment_of_closed_proper` —
  **Theorem 7.5** and **Corollary 7.5.1**, with `interior (epi f)` in place of `ri (epi f)`.
* `lscHull_le_setOf` — the level sets of the hull, `{x | (cl f) x ≤ α} = ⋂_{μ > α} cl {f ≤ μ}`;
  this is the part of **Theorem 7.6** that does not need relative interiors.
* `posHomogeneous_lscHull`, `posHomogeneous_clFn` — both hulls preserve positive homogeneity,
  because the epigraph of the hull is the closure of a cone. Neither needs convexity.
* `closedFn_coe_mul` — a non-negative real multiple of a closed function is closed. The convexity,
  domain and properness halves of the same statement are in `Convex/Epigraph.lean`.
* `closedProperConvexFn_coe_affineMap` — a *continuous* affine function, read into `EReal`, is
  closed proper convex.

## Design notes

**Why `clFn` branches on `lscHull f` and not on `f`.** Rockafellar defines `cl f` to be the lower
semicontinuous hull when `f` nowhere takes `−∞`, and the constant `−∞` otherwise. On `ℝⁿ` the two
branchings agree, by his Theorems 7.2 and 7.4. In general they do **not**, and branching on `f`
would make Fenchel–Moreau false: let `g : E →ₗ[ℝ] ℝ` be a discontinuous linear functional on an
infinite-dimensional space. Its kernel is dense, so `closure (epi g) = univ` and `lscHull g ≡ ⊥`,
while `g` itself is convex, finite everywhere and proper. With Rockafellar's branching,
`clFn g = lscHull g ≡ ⊥`, whereas `g` has no continuous affine minorant at all, so the biconjugate
of `g` is `≡ ⊥` too — and for `g + δ(· | closedBall 0 1)` the same phenomenon breaks
`f** = cl f` for a function with bounded effective domain. Branching on the hull, as here, is the
standard Γ-regularization and makes `f** = clFn f` unconditional. The price is that
`Proper f → Proper (clFn f)` (Theorem 7.4) is unavailable at this layer; it is finite-dimensional,
and is `ConvexFn.proper_clFn` in `Tdaf/Analysis/Convex/RelativeInterior.lean`.

**What is deliberately absent.** Theorem 7.2, Theorem 7.4, Lemma 7.3, and the `ri`-flavoured halves
of Theorems 7.5 and 7.6 all rest on relative interiors and on Theorem 6.1, and are
finite-dimensional. They are not stated here, not even in weakened form;
`Tdaf/Analysis/Convex/RelativeInterior.lean` supplies Lemma 7.3 and Theorems 7.2 and 7.4.

**The dichotomy.** The layer-B replacement for Theorem 7.2 is Corollary 7.2.1, and it must be
stated as "no finite values", not as "identically `⊥`": the function on `ℝ` that is `⊥` at the
origin and `⊤` elsewhere is convex and lower semicontinuous (its epigraph is a vertical line) and
takes `⊥`, but is not the constant `⊥`. An `example` in this file pins that down, and
`eq_bot_of_lsc_of_eq_bot` therefore carries the hypothesis `∀ x, f x < ⊤`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §7 (Theorem 7.1 through
  Theorem 7.6).
-/

open Set Filter Topology

namespace Tdaf.ConvexAnalysis

/-! ### Lower semicontinuity: Theorem 7.1 -/

section Semicontinuity

variable {E : Type*} [TopologicalSpace E] {f g : E → EReal}

/-- **Rockafellar, Theorem 7.1**, (a) ↔ (c). -/
theorem lowerSemicontinuous_iff_isClosed_epi : LowerSemicontinuous f ↔ IsClosed (epi f) := by
  constructor
  · intro hf
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    rintro ⟨x, μ⟩ hp
    obtain ⟨r, hμr, hrf⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 (not_le.1 hp)
    refine mem_of_superset
      (prod_mem_nhds (hf x (r : EReal) hrf) (Iio_mem_nhds (by exact_mod_cast hμr))) ?_
    rintro ⟨z, ν⟩ ⟨hz, hν⟩
    have hz' : (r : EReal) < f z := hz
    have hν' : ν < r := hν
    exact not_le.2 (lt_trans (by exact_mod_cast hν') hz')
  · intro hF x y hy
    obtain ⟨r, hyr, hrf⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hy
    have hclosed : IsClosed {z : E | f z ≤ (r : EReal)} := by
      have hpre : {z : E | f z ≤ (r : EReal)} = (fun z : E => (z, r)) ⁻¹' epi f := rfl
      rw [hpre]
      exact hF.preimage (continuous_id.prodMk continuous_const)
    filter_upwards [hclosed.isOpen_compl.mem_nhds (not_le.2 hrf)] with z hz
    exact hyr.trans (not_le.1 hz)

/-- **Rockafellar, Theorem 7.1**, (a) ↔ (b). -/
theorem lowerSemicontinuous_iff_isClosed_le :
    LowerSemicontinuous f ↔ ∀ α : ℝ, IsClosed {x | f x ≤ (α : EReal)} := by
  constructor
  · intro hf α
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [hf x (α : EReal) (not_le.1 hx)] with z hz using not_le.2 hz
  · intro h x y hy
    obtain ⟨r, hyr, hrf⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hy
    filter_upwards [(h r).isOpen_compl.mem_nhds (not_le.2 hrf)] with z hz
    exact hyr.trans (not_le.1 hz)

end Semicontinuity

/-! ### The lower semicontinuous hull and the closure of a convex function -/

section Defs

variable {E : Type*} [TopologicalSpace E] {f g : E → EReal}

/-- The **lower semicontinuous hull** of `f`: the function whose epigraph is the closure of the
epigraph of `f` (Rockafellar §7). It is the greatest lower semicontinuous function majorized by
`f`; see `isGreatest_lscHull`. -/
noncomputable def lscHull (f : E → EReal) : E → EReal := ofEpi (closure (epi f))

open Classical in
/-- The **closure** of a convex function: its lower semicontinuous hull, except that if the hull
takes the value `⊥` anywhere then the closure is the constant function `⊥` (Rockafellar §7).

Rockafellar branches on whether `f` itself takes `⊥`. That is equivalent for convex `f` on `ℝⁿ`
(by his Theorems 7.2 and 7.4) but **not** in general, and branching on `f` would falsify
Fenchel–Moreau; see the module docstring. Branching on the hull is the standard
Γ-regularization. -/
noncomputable def clFn (f : E → EReal) : E → EReal :=
  if ∃ x, lscHull f x = ⊥ then (fun _ => ⊥) else lscHull f

/-- A function is **closed** when it equals its own closure (Rockafellar §7). -/
def ClosedFn (f : E → EReal) : Prop := clFn f = f

/-- The defining equation of `clFn` in the regular branch. -/
theorem clFn_of_forall_ne_bot (h : ∀ x, lscHull f x ≠ ⊥) : clFn f = lscHull f := by
  have hc : ¬ ∃ x, lscHull f x = ⊥ := by push Not; exact h
  simp [clFn, hc]

/-- The defining equation of `clFn` in the exceptional branch. -/
theorem clFn_of_exists_eq_bot (h : ∃ x, lscHull f x = ⊥) : clFn f = fun _ => ⊥ := by
  simp [clFn, h]

/-- The lower semicontinuous hull is a minorant: `lscHull f ≤ f`. -/
theorem lscHull_le (f : E → EReal) : lscHull f ≤ f := by
  have h := ofEpi_mono (subset_closure (s := epi f))
  rwa [ofEpi_epi] at h

/-- Taking the lower semicontinuous hull is monotone. -/
theorem lscHull_mono (h : f ≤ g) : lscHull f ≤ lscHull g :=
  ofEpi_mono (closure_mono (epi_anti h))

/-- **The universal property, easy half.** A lower semicontinuous minorant of `f` is a minorant of
`lscHull f`, because its epigraph is a closed set containing `epi f`. -/
theorem le_lscHull_of_le (hg : LowerSemicontinuous g) (hgf : g ≤ f) : g ≤ lscHull f :=
  subset_epi_iff_le_ofEpi.1
    (closure_minimal (epi_anti hgf) (lowerSemicontinuous_iff_isClosed_epi.1 hg))

/-- For a lower semicontinuous `g`, being a minorant of `lscHull f` is the same as being a minorant
of `f`. -/
theorem le_lscHull_iff (hg : LowerSemicontinuous g) : g ≤ lscHull f ↔ g ≤ f :=
  ⟨fun h => h.trans (lscHull_le f), le_lscHull_of_le hg⟩

/-- The closure of `f` is a minorant of its lower semicontinuous hull; the two differ only in the
exceptional branch. -/
theorem clFn_le_lscHull (f : E → EReal) : clFn f ≤ lscHull f := by
  by_cases h : ∃ x, lscHull f x = ⊥
  · rw [clFn_of_exists_eq_bot h]
    exact fun _ => bot_le
  · rw [clFn_of_forall_ne_bot (by push Not at h; exact h)]

/-- The closure of `f` is a minorant of `f` (Rockafellar §7: `cl f ≤ f`). -/
theorem clFn_le (f : E → EReal) : clFn f ≤ f := (clFn_le_lscHull f).trans (lscHull_le f)

/-- Taking the closure is monotone (Rockafellar §7: `f₁ ≤ f₂` implies `cl f₁ ≤ cl f₂`). -/
theorem clFn_mono (h : f ≤ g) : clFn f ≤ clFn g := by
  by_cases hg : ∃ x, lscHull g x = ⊥
  · obtain ⟨x, hx⟩ := hg
    have hf : ∃ z, lscHull f z = ⊥ := ⟨x, le_bot_iff.1 (by rw [← hx]; exact lscHull_mono h x)⟩
    rw [clFn_of_exists_eq_bot hf, clFn_of_exists_eq_bot ⟨x, hx⟩]
  · have hg' : ∀ x, lscHull g x ≠ ⊥ := by push Not at hg; exact hg
    rw [clFn_of_forall_ne_bot (f := g) hg']
    exact (clFn_le_lscHull f).trans (lscHull_mono h)

end Defs

/-! ### The hull is a hull: Theorem 7.1 applied to `closure (epi f)` -/

section Hull

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  {f g : E → EReal}

/-- **The workhorse of this file.** The epigraph of the lower semicontinuous hull is the closure of
the epigraph — with no hypothesis on `f`, because `IsEpiLike.closure` says that the closure of
an epigraph is again an epigraph. -/
@[simp] theorem epi_lscHull (f : E → EReal) : epi (lscHull f) = closure (epi f) :=
  epi_ofEpi (IsEpiLike.closure (isEpiLike_epi f))

/-- The lower semicontinuous hull is lower semicontinuous. -/
theorem lowerSemicontinuous_lscHull (f : E → EReal) : LowerSemicontinuous (lscHull f) :=
  lowerSemicontinuous_iff_isClosed_epi.2 (by rw [epi_lscHull]; exact isClosed_closure)

/-- **The universal property.** `lscHull f` is the greatest lower semicontinuous minorant of `f`
(Rockafellar §7, the sentence defining the lower semicontinuous hull). -/
theorem isGreatest_lscHull (f : E → EReal) :
    IsGreatest {g : E → EReal | LowerSemicontinuous g ∧ g ≤ f} (lscHull f) :=
  ⟨⟨lowerSemicontinuous_lscHull f, lscHull_le f⟩, fun _ hg => le_lscHull_of_le hg.1 hg.2⟩

/-- Taking the lower semicontinuous hull is idempotent. -/
theorem lscHull_idem (f : E → EReal) : lscHull (lscHull f) = lscHull f :=
  epi_injective (by rw [epi_lscHull, epi_lscHull, closure_closure])

/-- A function equals its lower semicontinuous hull exactly when it is lower semicontinuous. -/
theorem lscHull_eq_self_iff : lscHull f = f ↔ LowerSemicontinuous f :=
  ⟨fun h => h ▸ lowerSemicontinuous_lscHull f,
    fun h => le_antisymm (lscHull_le f) (le_lscHull_of_le h le_rfl)⟩

omit [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The epigraph of the constant function `⊥` is everything. -/
@[simp] theorem epi_const_bot : epi (fun _ : E => (⊥ : EReal)) = univ := by
  ext p; simp [epi]

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The constant function `⊥` is its own lower semicontinuous hull. -/
@[simp] theorem lscHull_const_bot : lscHull (fun _ : E => (⊥ : EReal)) = fun _ => ⊥ := by
  simp only [lscHull, epi_const_bot, closure_univ, ofEpi_univ]
  rfl

omit [IsTopologicalAddGroup E] in
/-- The constant function `⊥` is its own closure. -/
@[simp] theorem clFn_const_bot : clFn (fun _ : E => (⊥ : EReal)) = fun _ => ⊥ :=
  clFn_of_exists_eq_bot ⟨0, by rw [lscHull_const_bot]⟩

/-- Taking the closure is idempotent (Rockafellar §7). -/
theorem clFn_idem (f : E → EReal) : clFn (clFn f) = clFn f := by
  by_cases h : ∃ x, lscHull f x = ⊥
  · rw [clFn_of_exists_eq_bot h, clFn_const_bot]
  · have h' : ∀ x, lscHull f x ≠ ⊥ := by push Not at h; exact h
    have h'' : ∀ x, lscHull (lscHull f) x ≠ ⊥ := by rw [lscHull_idem]; exact h'
    rw [clFn_of_forall_ne_bot h', clFn_of_forall_ne_bot h'', lscHull_idem]

/-- The closure of a function is closed. -/
theorem closedFn_clFn (f : E → EReal) : ClosedFn (clFn f) := clFn_idem f

/-- **What closedness means.** A function is closed exactly when it is the constant `⊥`, or is
lower semicontinuous and never takes the value `⊥`. -/
theorem closedFn_iff :
    ClosedFn f ↔ f = (fun _ => ⊥) ∨ (LowerSemicontinuous f ∧ ∀ x, f x ≠ ⊥) := by
  constructor
  · intro hc
    by_cases h : ∃ x, lscHull f x = ⊥
    · exact Or.inl (by rw [← hc, clFn_of_exists_eq_bot h])
    · have h' : ∀ x, lscHull f x ≠ ⊥ := by push Not at h; exact h
      have hs : lscHull f = f := by rw [← clFn_of_forall_ne_bot h']; exact hc
      exact Or.inr ⟨lscHull_eq_self_iff.1 hs, fun x => by rw [← hs]; exact h' x⟩
  · rintro (rfl | ⟨hlsc, hne⟩)
    · exact clFn_const_bot
    · have hs : lscHull f = f := lscHull_eq_self_iff.2 hlsc
      have h' : ∀ x, lscHull f x ≠ ⊥ := fun x => by rw [hs]; exact hne x
      exact (clFn_of_forall_ne_bot h').trans hs

/-- **Rockafellar §7**: for a function that never takes the value `⊥` — in particular for a proper
convex function — closedness is exactly lower semicontinuity. -/
theorem closedFn_iff_lowerSemicontinuous (h : ∀ x, f x ≠ ⊥) :
    ClosedFn f ↔ LowerSemicontinuous f := by
  rw [closedFn_iff]
  refine ⟨?_, fun hl => Or.inr ⟨hl, h⟩⟩
  rintro (rfl | ⟨hl, -⟩)
  · exact absurd rfl (h 0)
  · exact hl

/-- A closed function is lower semicontinuous. -/
theorem ClosedFn.lowerSemicontinuous (hc : ClosedFn f) : LowerSemicontinuous f := by
  rcases closedFn_iff.1 hc with rfl | ⟨hl, -⟩
  · exact lowerSemicontinuous_const
  · exact hl

/-- **Rockafellar §7**: "the only closed improper convex functions are the constant functions `+∞`
and `−∞`". Convexity is not needed for this direction. -/
theorem eq_const_of_closedFn_of_not_proper (hc : ClosedFn f) (hp : ¬ Proper f) :
    f = (fun _ => ⊥) ∨ f = fun _ => ⊤ := by
  rcases closedFn_iff.1 hc with h | ⟨-, hne⟩
  · exact Or.inl h
  · exact Or.inr (funext fun x => top_le_iff.1 (not_lt.1 fun hx => hp ⟨⟨x, hx⟩, hne⟩))

/-- The constant function `⊤` is closed. -/
theorem closedFn_const_top : ClosedFn (fun _ : E => (⊤ : EReal)) :=
  closedFn_iff.2 (Or.inr ⟨lowerSemicontinuous_const, fun _ => by simp⟩)

omit [IsTopologicalAddGroup E] in
/-- The constant function `⊥` is closed. -/
theorem closedFn_const_bot : ClosedFn (fun _ : E => (⊥ : EReal)) := clFn_const_bot

/-! ### Infima, effective domains and level sets -/

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- **Rockafellar §7**: "`f` and `cl f` plainly have the same infimum". The hull step already does
it: a constant function is lower semicontinuous, so `⨅ x, f x` is a lower semicontinuous minorant
of `f` and therefore a minorant of `lscHull f`. -/
theorem iInf_lscHull_eq_iInf (f : E → EReal) : ⨅ x, lscHull f x = ⨅ x, f x :=
  le_antisymm (iInf_mono fun x => lscHull_le f x)
    (le_iInf fun x =>
      le_lscHull_of_le (g := fun _ => ⨅ y, f y) lowerSemicontinuous_const (fun y => iInf_le f y) x)

omit [IsTopologicalAddGroup E] in
/-- **Rockafellar §7**: `f` and `cl f` have the same infimum. -/
theorem iInf_clFn_eq_iInf (f : E → EReal) : ⨅ x, clFn f x = ⨅ x, f x := by
  have : Nonempty E := ⟨0⟩
  by_cases h : ∃ x, lscHull f x = ⊥
  · obtain ⟨x₀, hx₀⟩ := h
    have hb : ⨅ x, f x = ⊥ := by
      rw [← iInf_lscHull_eq_iInf]
      exact le_bot_iff.1 (by rw [← hx₀]; exact iInf_le (fun x => lscHull f x) x₀)
    rw [hb, clFn_of_exists_eq_bot ⟨x₀, hx₀⟩]
    simp
  · rw [clFn_of_forall_ne_bot (by push Not at h; exact h)]
    exact iInf_lscHull_eq_iInf f

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The hull only enlarges the effective domain. -/
theorem dom_subset_dom_lscHull (f : E → EReal) : dom f ⊆ dom (lscHull f) :=
  fun _ hx => lt_of_le_of_lt (lscHull_le f _) hx

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- **Rockafellar §7**: `dom f ⊆ dom (cl f) ⊆ cl (dom f)`; this is the second inclusion, which
holds for the hull with no hypothesis on `f`. It is `dom_eq_fst_image_epi` pushed through the
continuous projection `Prod.fst`. -/
theorem dom_lscHull_subset_closure_dom (f : E → EReal) : dom (lscHull f) ⊆ closure (dom f) := by
  intro x hx
  obtain ⟨μ, hμ, -⟩ := ofEpi_lt_iff.1 (hx : lscHull f x < ⊤)
  have h2 := image_closure_subset_closure_image (f := (Prod.fst : E × ℝ → E)) continuous_fst
    (mem_image_of_mem _ hμ)
  rwa [← dom_eq_fst_image_epi] at h2

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- **The closure of an improper function is improper.** Neither convexity nor finite dimension is
used: `clFn f ≤ f` transfers the value `−∞` upwards, and `dom (lscHull f) ⊆ cl (dom f)` transfers
emptiness of the effective domain. The converse — properness is preserved — needs both, and is
`ConvexFn.proper_clFn` in `RelativeInterior.lean`. -/
theorem not_proper_clFn (himp : ¬ Proper f) : ¬ Proper (clFn f) := by
  intro hpr
  refine himp ⟨?_, fun z hz => hpr.ne_bot z (le_bot_iff.1 (by rw [← hz]; exact clFn_le f z))⟩
  obtain ⟨y, hy⟩ := hpr.dom_nonempty
  have hb : ∀ x, lscHull f x ≠ ⊥ := fun x hx =>
    hpr.ne_bot x (le_bot_iff.1 (by rw [← hx]; exact clFn_le_lscHull f x))
  rw [clFn_of_forall_ne_bot hb] at hy
  have hyd : y ∈ closure (dom f) := dom_lscHull_subset_closure_dom f hy
  rcases Set.eq_empty_or_nonempty (dom f) with h | h
  · rw [h, closure_empty] at hyd
    exact absurd hyd (Set.notMem_empty y)
  · exact h

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- A point of `closure (epi f)` at height `μ` is a limit of points where `f` is below any `ν > μ`.
This is the pointwise content of Rockafellar's description of `cl f` as the infimum of the `μ` with
`x ∈ cl {z | f z ≤ μ}`. -/
theorem mem_closure_le_of_mem_closure_epi {x : E} {μ ν : ℝ}
    (h : ((x, μ) : E × ℝ) ∈ closure (epi f)) (hμν : μ < ν) :
    x ∈ closure {z | f z ≤ (ν : EReal)} := by
  rw [mem_closure_iff] at h ⊢
  intro U hU hxU
  obtain ⟨p, hp1, hp2⟩ := h (U ×ˢ Iio ν) (hU.prod isOpen_Iio) ⟨hxU, hμν⟩
  have hp2' : f p.1 ≤ (p.2 : EReal) := hp2
  have hp1' : p.2 < ν := hp1.2
  exact ⟨p.1, hp1.1, hp2'.trans (by exact_mod_cast hp1'.le)⟩

/-- The closure of a sublevel set of `f` is contained in the corresponding sublevel set of the
hull. -/
theorem closure_le_subset_lscHull_le (f : E → EReal) (α : ℝ) :
    closure {x | f x ≤ (α : EReal)} ⊆ {x | lscHull f x ≤ (α : EReal)} := by
  intro x hx
  have hsub : (fun z : E => (z, α)) '' {z | f z ≤ (α : EReal)} ⊆ epi f := by
    rintro _ ⟨z, hz, rfl⟩; exact hz
  have h1 := image_closure_subset_closure_image
    (f := fun z : E => (z, α)) (continuous_id.prodMk continuous_const) (mem_image_of_mem _ hx)
  have h2 := closure_mono hsub h1
  rw [← epi_lscHull] at h2
  exact h2

/-- **Rockafellar §7**, the displayed formula for the level sets of the closure:
`{x | (cl f) x ≤ α} = ⋂_{μ > α} cl {x | f x ≤ μ}`. Stated for the hull, which is where the content
is; the `ri`-flavoured half of Theorem 7.6 (that this equals `cl {x | f x ≤ α}` when
`α > inf f`) is finite-dimensional and is not proved here. -/
theorem lscHull_le_setOf (f : E → EReal) (α : ℝ) :
    {x | lscHull f x ≤ (α : EReal)} = ⋂ μ ∈ Ioi α, closure {x | f x ≤ (μ : EReal)} := by
  refine subset_antisymm (fun x hx => mem_iInter₂.2 fun μ hμ => ?_) fun x hx => ?_
  · have hlt : lscHull f x < (μ : EReal) :=
      lt_of_le_of_lt hx (by exact_mod_cast (hμ : α < μ))
    obtain ⟨ν, hν, hνμ⟩ := ofEpi_lt_iff.1 hlt
    exact mem_closure_le_of_mem_closure_epi hν (by exact_mod_cast hνμ)
  · refine Tdaf.EReal.le_coe_of_forall_lt fun q hq => ?_
    obtain ⟨μ, hαμ, hμq⟩ := exists_between hq
    exact lt_of_le_of_lt
      (closure_le_subset_lscHull_le f μ (mem_iInter₂.1 hx μ hαμ)) (by exact_mod_cast hμq)


/-! ### `lscHull` and `clFn` as closure operators

Both operations are monotone, idempotent and **de**creasing, so each is a closure operator on the
*order dual* of `E → EReal` — exactly as `epiClosure` is a closure operator on `Set (E × ℝ)`
whose closed elements are the epi-like sets. Recording that makes Mathlib's `ClosureOperator` API
available and identifies `LowerSemicontinuous` and `ClosedFn` as the two closedness
predicates. `ClosureOperator.ofPred` is the constructor whose hypotheses are literally the
universal property, so the instantiation *is* the statement "`lscHull f` is the greatest lower
semicontinuous minorant of `f`". -/

open OrderDual in
/-- `lscHull`, as a closure operator on `(E → EReal)ᵒᵈ`. Its closed elements are the lower
semicontinuous functions. -/
noncomputable def lscHullClosure : ClosureOperator (E → EReal)ᵒᵈ :=
  ClosureOperator.ofPred (fun g => toDual (lscHull (ofDual g)))
    (fun g => LowerSemicontinuous (ofDual g))
    (fun g => lscHull_le (ofDual g))
    (fun g => lowerSemicontinuous_lscHull (ofDual g))
    (fun _ _ hgh hh => le_lscHull_of_le hh hgh)

@[simp] theorem lscHullClosure_apply (f : E → EReal) :
    lscHullClosure (OrderDual.toDual f) = OrderDual.toDual (lscHull f) := rfl

/-- Lower semicontinuity is `lscHullClosure`-closedness. -/
theorem lowerSemicontinuous_iff_lscHullClosure_isClosed :
    LowerSemicontinuous f ↔ lscHullClosure.IsClosed (OrderDual.toDual f) := Iff.rfl

open OrderDual in
/-- `clFn`, as a closure operator on `(E → EReal)ᵒᵈ`. Its closed elements are exactly the closed
functions, so `ClosedFn` is the closedness predicate of a genuine closure operator. -/
noncomputable def clFnClosure : ClosureOperator (E → EReal)ᵒᵈ :=
  ClosureOperator.ofPred (fun g => toDual (clFn (ofDual g)))
    (fun g => ClosedFn (ofDual g))
    (fun g => clFn_le (ofDual g))
    (fun g => clFn_idem (ofDual g))
    (fun _ _ hgh hh => hh.symm.trans_le (clFn_mono hgh))

@[simp] theorem clFnClosure_apply (f : E → EReal) :
    clFnClosure (OrderDual.toDual f) = OrderDual.toDual (clFn f) := rfl

/-- `ClosedFn` is `clFnClosure`-closedness. -/
theorem closedFn_iff_clFnClosure_isClosed :
    ClosedFn f ↔ clFnClosure.IsClosed (OrderDual.toDual f) := Iff.rfl

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- **The universal property of the closure.** `clFn f` is the greatest closed minorant of `f`;
this is the `hmin` field of `clFnClosure`, restated without the `OrderDual` wrapping. -/
theorem le_clFn_of_le (hg : ClosedFn g) (hgf : g ≤ f) : g ≤ clFn f :=
  hg.symm.trans_le (clFn_mono hgf)


/-! ### Indicator functions -/

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The lower semicontinuous hull of an indicator function is the indicator of the closure. -/
@[simp] theorem lscHull_indicatorFn (s : Set E) :
    lscHull (indicatorFn s) = indicatorFn (closure s) := by
  have h : closure (epi (indicatorFn s)) = epi (indicatorFn (closure s)) := by
    rw [epi_indicatorFn, epi_indicatorFn, closure_prod_eq, isClosed_Ici.closure_eq]
  rw [lscHull, h, ofEpi_epi]

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- **`cl δ(· | s) = δ(· | cl s)`** (Rockafellar §7): closing an indicator function closes its
set. -/
@[simp] theorem clFn_indicatorFn (s : Set E) :
    clFn (indicatorFn s) = indicatorFn (closure s) := by
  rw [clFn_of_forall_ne_bot fun x => by
    rw [lscHull_indicatorFn]; exact indicatorFn_ne_bot _ _, lscHull_indicatorFn]

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The indicator of a closed set is a closed convex function. -/
theorem closedFn_indicatorFn {s : Set E} (hs : IsClosed s) : ClosedFn (indicatorFn s) := by
  change clFn (indicatorFn s) = indicatorFn s
  rw [clFn_indicatorFn, hs.closure_eq]

end Hull

/-! ### Approaching the endpoint of a segment

The three lemmas below package the filter `𝓝[<] (1 : ℝ)` bookkeeping shared by the dichotomy
(Corollary 7.2.1) and by the limit formulas of Theorem 7.5. -/

section Segment

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The segment `a ↦ (1 - a) • x + a • y` tends to `y` as `a ↑ 1`. -/
theorem tendsto_segment (x y : E) :
    Tendsto (fun a : ℝ => (1 - a) • x + a • y) (𝓝[<] (1 : ℝ)) (𝓝 y) := by
  have hcont : Continuous fun a : ℝ => (1 - a) • x + a • y :=
    ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have h : Tendsto (fun a : ℝ => (1 - a) • x + a • y) (𝓝[<] (1 : ℝ))
      (𝓝 ((1 - (1 : ℝ)) • x + (1 : ℝ) • y)) := (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  simpa using h

/-- Approaching `1` from below, one is eventually inside `[0, 1)`. -/
theorem eventually_mem_Ico_nhdsLT_one : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ a ∧ a < 1 := by
  filter_upwards [(eventually_ge_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with a ha ha1 using ⟨ha, ha1⟩

/-- An affine function of `a` tends to its value at `1` as `a ↑ 1`. -/
theorem tendsto_affine_nhdsLT_one (α β : ℝ) :
    Tendsto (fun a : ℝ => (1 - a) * α + a * β) (𝓝[<] (1 : ℝ)) (𝓝 β) := by
  have hcont : Continuous fun a : ℝ => (1 - a) * α + a * β :=
    ((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)
  have h : Tendsto (fun a : ℝ => (1 - a) * α + a * β) (𝓝[<] (1 : ℝ))
      (𝓝 ((1 - (1 : ℝ)) * α + (1 : ℝ) * β)) := (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  simpa using h

end Segment

/-! ### Convexity of the hull and of the closure -/

section Convex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f g : E → EReal}

/-- The lower semicontinuous hull of a convex function is convex: the closure of a convex set is
convex (`Convex.closure`), and `convexFn_ofEpi` is Rockafellar's Theorem 5.3. -/
theorem convexFn_lscHull (hf : ConvexFn f) : ConvexFn (lscHull f) :=
  convexFn_ofEpi hf.convex_epi.closure

/-- **Rockafellar §7**: "Either way, the closure of `f` is another convex function." -/
theorem convexFn_clFn (hf : ConvexFn f) : ConvexFn (clFn f) := by
  by_cases h : ∃ x, lscHull f x = ⊥
  · rw [clFn_of_exists_eq_bot h]
    exact ⟨by rw [epi_const_bot]; exact convex_univ⟩
  · rw [clFn_of_forall_ne_bot (by push Not at h; exact h)]
    exact convexFn_lscHull hf

/-! ### The dichotomy for improper convex functions

Rockafellar's Theorem 7.2 ("an improper convex function is `−∞` on `ri (dom f)`") is
finite-dimensional and out of scope here. Its lower-semicontinuous consequence, Corollary 7.2.1
("a lower semicontinuous improper convex function has no finite values"), is *not*: it holds in any
topological vector space, and it is the statement that replaces Theorem 7.2 at this layer.

Note that Corollary 7.2.1 is the sharp form. The stronger-sounding "a lower semicontinuous convex
function taking `⊥` anywhere is identically `⊥`" is **false**; see `eq_bot_of_lsc_of_eq_bot`
and the counterexample recorded just before it. -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The algebraic engine of Rockafellar's Theorem 7.2, valid in any real vector space: if `f` is
convex, `f x₀ = ⊥` and `y` is in the effective domain, then `f` is `⊥` on the half-open segment
`[x₀, y)`.

Note the hypothesis `y ∈ dom f`. Without it the conclusion is false: for
`f = restrict {x₀} (fun _ => ⊥)` the segment `[x₀, y)` meets `dom f` only at `x₀`. -/
theorem ConvexFn.eq_bot_of_lt_one (hf : ConvexFn f) {x₀ y : E} (h₀ : f x₀ = ⊥) (hy : y ∈ dom f)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) : f ((1 - a) • x₀ + a • y) = ⊥ := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simpa using h₀
  · obtain ⟨β, hβ, -⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 (hy : f y < ⊤)
    have hb : (0 : ℝ) < 1 - a := by linarith
    refine Tdaf.EReal.eq_bot_of_forall_le_coe fun r => ?_
    have hb' : (1 : ℝ) - a ≠ 0 := ne_of_gt hb
    have harith : (1 - a) * ((r - a * β) / (1 - a)) + a * β = r := by
      field_simp
      ring
    have hx₀ : f x₀ < (((r - a * β) / (1 - a) : ℝ) : EReal) := by rw [h₀]; simp
    have hkey := (convexFn_iff_forall_lt f).1 hf x₀ y (1 - a) a hb ha' (by ring) _ β hx₀ hβ
    rw [harith] at hkey
    exact hkey.le

/-- **Rockafellar, Corollary 7.2.1**, pointwise form: a lower semicontinuous convex function that
takes the value `⊥` somewhere takes the value `⊥` at every point of its effective domain.

Only lower semicontinuity at `y` is used, through the limit `λ ↑ 1` along the segment from `x₀`
to `y`; no relative interiors and no finite-dimensionality. -/
theorem ConvexFn.eq_bot_of_mem_dom (hf : ConvexFn f) (hl : LowerSemicontinuous f) {x₀ : E}
    (h₀ : f x₀ = ⊥) {y : E} (hy : y ∈ dom f) : f y = ⊥ := by
  by_contra hne
  have h1 : ∀ᶠ a in 𝓝[<] (1 : ℝ), (⊥ : EReal) < f ((1 - a) • x₀ + a • y) :=
    (tendsto_segment x₀ y).eventually (hl y ⊥ (bot_lt_iff_ne_bot.2 hne))
  have hbot : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), f ((1 - a) • x₀ + a • y) = ⊥ := by
    filter_upwards [eventually_mem_Ico_nhdsLT_one] with a ha
    exact hf.eq_bot_of_lt_one h₀ hy ha.1 ha.2
  obtain ⟨a, hlt, heq⟩ := (h1.and hbot).exists
  rw [heq] at hlt
  exact absurd hlt (lt_irrefl ⊥)

/-- **Rockafellar, Corollary 7.2.1.** A lower semicontinuous improper convex function has no finite
values: it is `⊥` on its effective domain and `⊤` off it. -/
theorem ConvexFn.eq_bot_or_eq_top (hf : ConvexFn f) (hl : LowerSemicontinuous f)
    (h : ∃ x₀, f x₀ = ⊥) (x : E) : f x = ⊥ ∨ f x = ⊤ := by
  obtain ⟨x₀, h₀⟩ := h
  rcases eq_top_or_lt_top (f x) with hx | hx
  · exact Or.inr hx
  · exact Or.inl (hf.eq_bot_of_mem_dom hl h₀ hx)

/-- A lower semicontinuous convex function taking the value `⊥` is `⊥` exactly on its effective
domain, which is therefore closed. -/
theorem ConvexFn.dom_eq_setOf_eq_bot (hf : ConvexFn f) (hl : LowerSemicontinuous f)
    (h : ∃ x₀, f x₀ = ⊥) : dom f = {x | f x = ⊥} := by
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨x₀, h₀⟩ := h
    exact hf.eq_bot_of_mem_dom hl h₀ hx
  · have hx' : f x = ⊥ := hx
    exact mem_dom.2 (lt_of_le_of_lt (le_of_eq hx') bot_lt_top)

/-- **The dichotomy, in the form that is actually true.** A lower semicontinuous convex function
that takes the value `⊥` somewhere and is nowhere `⊤` is identically `⊥`.

The hypothesis `hdom` is **not** removable: see the `example` below, which exhibits a lower
semicontinuous convex `f : ℝ → EReal` with `f 0 = ⊥` and `f 1 = ⊤`. Dropping it and concluding
`f = fun _ => ⊥` would be a false statement; the sharp unconditional form is
`ConvexFn.eq_bot_or_eq_top` (Rockafellar's Corollary 7.2.1). -/
theorem eq_bot_of_lsc_of_eq_bot (hf : ConvexFn f) (hl : LowerSemicontinuous f)
    (hdom : ∀ x, f x < ⊤) (h : ∃ x₀, f x₀ = ⊥) : f = fun _ => ⊥ := by
  obtain ⟨x₀, h₀⟩ := h
  exact funext fun x => hf.eq_bot_of_mem_dom hl h₀ (hdom x)

end Convex

/-! ### Positively homogeneous functions -/

section PosHomogeneous

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f : E → EReal}

/-- **The lower semicontinuous hull of a positively homogeneous function is positively
homogeneous.** Positive homogeneity is the epigraph being a cone
(`posHomogeneous_iff_isCone_epi`); `epi (lscHull f)` is the closure of `epi f` (`epi_lscHull`);
and the closure of a cone is a cone (`smul_closure_eq_of_isCone`).

Convexity is not used anywhere in that chain. -/
theorem posHomogeneous_lscHull (hf : PosHomogeneous f) : PosHomogeneous (lscHull f) := by
  rw [posHomogeneous_iff_isCone_epi] at hf ⊢
  intro a ha
  rw [epi_lscHull]
  exact smul_closure_eq_of_isCone hf a ha

/-- **The closure of a positively homogeneous function is positively homogeneous.**

The improper branch is not an exclusion but a case: there `cl f` is the constant `⊥`, and
`a * ⊥ = ⊥` for `a > 0`. Rockafellar's Corollary 13.2.1 gives the same conclusion for a *convex*
`f` by writing `cl f` as a support function; that route needs a pairing the statement does not
mention, and convexity it does not need either. -/
theorem posHomogeneous_clFn (hf : PosHomogeneous f) : PosHomogeneous (clFn f) := by
  by_cases h : ∃ x, lscHull f x = ⊥
  · rw [clFn_of_exists_eq_bot h]
    exact fun a ha _ => (_root_.EReal.coe_mul_bot_of_pos ha).symm
  · rw [clFn_of_forall_ne_bot (by push Not at h; exact h)]
    exact posHomogeneous_lscHull hf

end PosHomogeneous

/-! ### Non-negative scalar multiples -/

section ScalarMultiple

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] {f : E → EReal}

omit [IsTopologicalAddGroup E] in
/-- **`scaleSnd c` is continuous.** It scales only the real coordinate, so `E` contributes nothing
beyond its own topology — no `ContinuousSMul ℝ E` is needed. -/
theorem continuous_scaleSnd (c : ℝ) : Continuous (scaleSnd (E := E) c) := by
  have h : (scaleSnd (E := E) c : E × ℝ → E × ℝ) = fun p => (p.1, c * p.2) := rfl
  rw [h]
  exact continuous_fst.prodMk (continuous_const.mul continuous_snd)

/-- **A non-negative multiple of a closed function is closed**, provided the function never takes
`⊥`.

The `⊥`-freedom is not a technicality: closedness of `cf` is lower semicontinuity of `cf`
(`closedFn_iff_lowerSemicontinuous`), and that equivalence is what needs it. Given it, `epi (cf)`
is `epi f` pulled back along the continuous `scaleSnd c⁻¹` (`epi_coe_mul`); at `c = 0` the product
is the constant `0`, which is continuous. -/
theorem closedFn_coe_mul {c : ℝ} (hc : 0 ≤ c) (hf : ClosedFn f) (hb : ∀ x, f x ≠ ⊥) :
    ClosedFn (fun x => (c : EReal) * f x) := by
  have hb' : ∀ x, (c : EReal) * f x ≠ ⊥ := fun x => Tdaf.EReal.coe_mul_ne_bot hc (hb x)
  rw [closedFn_iff_lowerSemicontinuous hb', lowerSemicontinuous_iff_isClosed_epi]
  rcases eq_or_lt_of_le hc with h | h
  · have hz : (fun x => (c : EReal) * f x) = fun _ : E => (0 : EReal) := by
      funext x; rw [← h]; simp
    rw [hz, ← lowerSemicontinuous_iff_isClosed_epi]
    exact lowerSemicontinuous_const
  · rw [epi_coe_mul h f]
    refine IsClosed.preimage (continuous_scaleSnd _) ?_
    rw [← lowerSemicontinuous_iff_isClosed_epi]
    exact (closedFn_iff_lowerSemicontinuous hb).1 hf

end ScalarMultiple

/-! ### Closed proper convex functions -/

section ClosedProperConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] {f : E → EReal}

/-- A **closed proper convex function**: Rockafellar's standing hypothesis from §12 onwards, and
the class `conjEquiv` and `supportEquiv` are bijections between.

The three conditions travel together everywhere in the duality theory — a conjugate is proper only
when its argument is closed and proper, an affine minorant exists only then, and the biconjugate
returns `f` only then — so they are bundled rather than repeated. Individual side conditions such
as `∀ x, f x ≠ ⊥` stay inline, per the house convention. -/
structure ClosedProperConvexFn (f : E → EReal) : Prop where
  /-- The epigraph is convex. -/
  convex : ConvexFn f
  /-- `f` equals its own closure. -/
  closed : ClosedFn f
  /-- `f` is finite somewhere and never `-∞`. -/
  proper : Proper f

/-- A closed proper convex function is lower semicontinuous. -/
theorem ClosedProperConvexFn.lowerSemicontinuous (hf : ClosedProperConvexFn f) :
    LowerSemicontinuous f :=
  hf.closed.lowerSemicontinuous

/-- The epigraph of a closed proper convex function is closed. -/
theorem ClosedProperConvexFn.isClosed_epi (hf : ClosedProperConvexFn f) : IsClosed (epi f) :=
  lowerSemicontinuous_iff_isClosed_epi.1 hf.lowerSemicontinuous

/-- For a proper function, closedness of the epigraph is closedness of the function, so this is the
form of the constructor that §8 uses. -/
theorem ClosedProperConvexFn.of_isClosed_epi (hconv : ConvexFn f) (hc : IsClosed (epi f))
    (hp : Proper f) : ClosedProperConvexFn f :=
  ⟨hconv, (closedFn_iff_lowerSemicontinuous hp.ne_bot).2
    (lowerSemicontinuous_iff_isClosed_epi.2 hc), hp⟩

/-- `ClosedProperConvexFn` in the `IsClosed (epi f)` spelling. -/
theorem closedProperConvexFn_iff_isClosed_epi (hp : Proper f) :
    ClosedProperConvexFn f ↔ ConvexFn f ∧ IsClosed (epi f) :=
  ⟨fun hf => ⟨hf.convex, hf.isClosed_epi⟩,
    fun ⟨hconv, hc⟩ => ClosedProperConvexFn.of_isClosed_epi hconv hc hp⟩

/-- **A continuous affine function, read into `EReal`, is closed proper convex.**

This is what every section with affine constraints asks for: an equality constraint `a x = 0`
enters the theory as the pair of convex functions `a` and `-a`, and `ClosedProperConvexFn` is the
hypothesis the sum and conjugacy rules take.

Continuity is a hypothesis rather than a consequence, and that is not slack: on an
infinite-dimensional space a *discontinuous* linear functional is convex, finite everywhere and
proper, and is not closed — its lower semicontinuous hull is the constant `⊥`, which is the
counterexample the module docstring is built around. In finite dimensions
`AffineMap.continuous_of_finiteDimensional` discharges it. -/
theorem closedProperConvexFn_coe_affineMap {g : E →ᵃ[ℝ] ℝ} (hg : Continuous g) :
    ClosedProperConvexFn (fun x => ((g x : ℝ) : EReal)) := by
  have hcont : Continuous fun x : E => ((g x : ℝ) : EReal) := _root_.EReal.continuous_coe_iff.2 hg
  refine ⟨?_, ?_, ⟨⟨0, mem_dom.2 (_root_.EReal.coe_lt_top _)⟩,
    fun _ => _root_.EReal.coe_ne_bot _⟩⟩
  · refine convexFn_of_epi_combo fun x y p q hx hy s t hs ht hst => ?_
    rw [_root_.EReal.coe_le_coe_iff] at hx hy ⊢
    rw [Convex.combo_affine_apply hst]
    simp only [smul_eq_mul]
    nlinarith
  · exact (closedFn_iff_lowerSemicontinuous fun _ => _root_.EReal.coe_ne_bot _).2
      hcont.lowerSemicontinuous

end ClosedProperConvex

/-! ### Why the dichotomy needs a hypothesis

The following `example` records the counterexample referred to above, and is the reason
`eq_bot_of_lsc_of_eq_bot` carries the hypothesis `∀ x, f x < ⊤`. The function is `⊥` at the
origin of `ℝ` and `⊤` elsewhere; its epigraph is the vertical line `{0} × ℝ`, a closed convex set,
so the function is convex and lower semicontinuous. It takes the value `⊥`, and it is not the
constant `⊥`. -/

example : ∃ f : ℝ → EReal,
    ConvexFn f ∧ LowerSemicontinuous f ∧ (∃ x, f x = ⊥) ∧ f ≠ fun _ => ⊥ := by
  have hepi : epi (Tdaf.ConvexAnalysis.restrict ({0} : Set ℝ) fun _ => (⊥ : EReal))
      = (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' {0} := by
    ext p
    by_cases h : p.1 ∈ ({0} : Set ℝ) <;> simp [epi, h]
  refine ⟨Tdaf.ConvexAnalysis.restrict ({0} : Set ℝ) fun _ => ⊥, ⟨?_⟩, ?_, ⟨0, by simp⟩, ?_⟩
  · rw [hepi]
    exact (convex_singleton (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  · refine lowerSemicontinuous_iff_isClosed_epi.2 ?_
    rw [hepi]
    exact isClosed_singleton.preimage continuous_fst
  · intro hcontra
    have h1 := congrFun hcontra 1
    rw [Tdaf.ConvexAnalysis.restrict_of_notMem (by norm_num : (1 : ℝ) ∉ ({0} : Set ℝ))] at h1
    exact absurd h1 (by simp)


/-! ### Affine minorants of closed proper convex functions -/

section LocallyConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {f : E → EReal}

/-- **A closed proper convex function has a continuous affine minorant.**

This is the layer-B replacement for the affine-minorant step of Rockafellar's Theorem 7.4, and it
is the keystone of Fenchel–Moreau. Closedness is essential: for a *merely* proper convex `f` the
statement is false in infinite dimensions — a discontinuous linear functional `g` has dense kernel,
so `closure (epi g) = univ` and `lscHull g ≡ ⊥`, while `g` is convex, finite everywhere and proper.

The proof separates the closed convex set `epi f` from the point `(x₀, f x₀ - 1)` in `E × ℝ` by
`geometric_hahn_banach_closed_point`. The separating functional cannot be "vertical": a functional
of the form `(y, 0)` takes the same value at `(x₀, f x₀ - 1)` and at `(x₀, f x₀)`, and the latter
lies in `epi f` because `x₀ ∈ dom f`. -/
theorem exists_affine_le_of_closed_proper (hf : ClosedProperConvexFn f) :
    ∃ (y : E →L[ℝ] ℝ) (c : ℝ), ∀ x, ((y x : ℝ) : EReal) - c ≤ f x := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.dom_nonempty
  obtain ⟨t, ht⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x₀) hx₀
  obtain ⟨y, b, hy, _⟩ :=
    exists_affine_le_of_isClosed_epi hf.convex hf.isClosed_epi (ν := t) (μ := t - 1) (le_of_eq ht)
      (by rw [ht]; exact_mod_cast (by linarith : t - 1 < t))
  exact ⟨y, b, hy⟩

end LocallyConvex

/-! ### Limits along a segment: Theorem 7.5 and Corollary 7.5.1 -/

section SegmentLimit

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f : E → EReal}

/-- **Rockafellar, Theorem 7.5**, at layer B: the lower semicontinuous hull of `f` at `y` is the
limit of `f` along the segment running from `x` to `y`, provided the segment starts at an
*interior* point of `epi f`.

Rockafellar's hypothesis is `x ∈ ri (dom f)`, which by his Lemma 7.3 says exactly that the
vertical line over `x` meets `ri (epi f)`. Relative interiors are finite-dimensional, so the
honest generalisation replaces `ri (epi f)` by `interior (epi f)`; Mathlib's
`Convex.combo_interior_closure_mem_interior` then supplies the step Rockafellar takes from his
Theorem 6.1. In finite dimensions `interior (epi f)` may of course be empty when
`ri (epi f)` is not, so this is a genuine restriction as well as a generalisation. -/
theorem tendsto_lscHull_along_segment (hf : ConvexFn f) {x : E} {α : ℝ}
    (hx : (x, α) ∈ interior (epi f)) (y : E) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (lscHull f y)) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [(tendsto_segment x y).eventually (lowerSemicontinuous_lscHull f y b hb)]
      with a ha
    exact lt_of_lt_of_le ha (lscHull_le f _)
  · intro b hb
    obtain ⟨β, hβ1, hβ2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hb
    obtain ⟨γ, hγ1, hγ2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hβ2
    have hβγ : β < γ := by exact_mod_cast hγ1
    have hyβ : ((y, β) : E × ℝ) ∈ closure (epi f) := by
      rw [← epi_lscHull]; exact hβ1.le
    filter_upwards [(tendsto_affine_nhdsLT_one α β).eventually_lt_const hβγ,
      eventually_mem_Ico_nhdsLT_one] with a hlt ha
    have hcombo := hf.convex_epi.combo_interior_closure_mem_interior hx hyβ
      (by linarith [ha.2] : (0 : ℝ) < 1 - a) ha.1 (by ring)
    have hpair : (1 - a) • ((x, α) : E × ℝ) + a • (y, β)
        = ((1 - a) • x + a • y, (1 - a) * α + a * β) := by
      simp [smul_eq_mul]
    rw [hpair] at hcombo
    have hle : f ((1 - a) • x + a • y) ≤ (((1 - a) * α + a * β : ℝ) : EReal) :=
      mk_mem_epi.1 (interior_subset hcombo)
    exact lt_of_le_of_lt hle (lt_trans (by exact_mod_cast hlt) hγ2)

/-- **Rockafellar, Theorem 7.5** stated for `clFn`. The exceptional branch of `clFn` has to be
ruled out by hand, and it genuinely can occur: for `f` the indicator-like function that is `⊥` on a
closed ball and `⊤` outside it, `clFn f ≡ ⊥` while the limit along a segment ending outside the
ball is `⊤`. Rockafellar's own statement carries the matching restriction "`y ∈ cl (dom f)`" in
the improper case. -/
theorem clFn_eq_limit_along_segment (hf : ConvexFn f) (hne : ∀ z, lscHull f z ≠ ⊥) {x : E} {α : ℝ}
    (hx : (x, α) ∈ interior (epi f)) (y : E) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (clFn f y)) := by
  rw [clFn_of_forall_ne_bot hne]
  exact tendsto_lscHull_along_segment hf hx y

/-- **Rockafellar, Corollary 7.5.1**, with no relative interiors at all: for a closed proper convex
`f`, every `x ∈ dom f` and every `y`, `f y = lim_{a ↑ 1} f ((1 - a) • x + a • y)`.

Rockafellar deduces this from Theorem 7.5 by restricting to a line and using relative interiors of
intervals. The direct argument needs neither: lower semicontinuity gives the `liminf` half for
every `y`, including `f y = ⊤`, and convexity applied to the two finite values `f x` and `f y`
gives the `limsup` half. -/
theorem tendsto_along_segment_of_closed_proper (hf : ClosedProperConvexFn f)
    {x : E} (hx : x ∈ dom f) (y : E) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (f y)) := by
  have hlsc : LowerSemicontinuous f := hf.lowerSemicontinuous
  rw [tendsto_order]
  refine ⟨fun b hb => (tendsto_segment x y).eventually (hlsc y b hb), fun b hb => ?_⟩
  obtain ⟨s, hs⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x) hx
  obtain ⟨r, hr⟩ :=
    Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot y) (lt_of_lt_of_le hb le_top)
  obtain ⟨γ, hγ1, hγ2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hb
  have hrγ : r < γ := by rw [hr] at hγ1; exact_mod_cast hγ1
  filter_upwards [(tendsto_affine_nhdsLT_one s r).eventually_lt_const hrγ,
    eventually_mem_Ico_nhdsLT_one] with a hlt ha
  have hle := hf.convex.epi_combo hs.le hr.le (by linarith [ha.2] : (0 : ℝ) ≤ 1 - a) ha.1 (by ring)
  exact lt_of_le_of_lt hle (lt_trans (by exact_mod_cast hlt) hγ2)

end SegmentLimit

/-! ### The lower semicontinuous hull as a `liminf`

Rockafellar writes `(cl f)(x) = liminf_{y → x} f(y)` and uses it whenever the closure has to be
computed at a single point (Corollary 30.2.3, for instance). In a complete lattice
`liminf f (𝓝 x) = ⨆ s ∈ 𝓝 x, ⨅ y ∈ s, f y`, which is exactly the value of `lscHull` at `x`; the
identity therefore needs no convexity and no hypothesis on `f`. -/

section Liminf

variable {E : Type*} [TopologicalSpace E] {f : E → EReal}

/-- The pointwise `liminf` of `f` along the neighbourhood filter is a minorant of `f`: the
neighbourhood filter contains the point itself. -/
theorem liminf_nhds_le (f : E → EReal) (x : E) : liminf f (𝓝 x) ≤ f x := by
  rw [liminf_eq_iSup_iInf]
  exact iSup₂_le fun s hs => iInf₂_le x (mem_of_mem_nhds hs)

/-- `x ↦ liminf_{y → x} f(y)` is lower semicontinuous: a neighbourhood witnessing the bound at `x`
witnesses it, through its interior, at every nearby point. -/
theorem lowerSemicontinuous_liminf_nhds (f : E → EReal) :
    LowerSemicontinuous fun x => liminf f (𝓝 x) := by
  intro x c hc
  have hc' : c < liminf f (𝓝 x) := hc
  rw [liminf_eq_iSup_iInf] at hc'
  obtain ⟨s, hs⟩ := lt_iSup_iff.1 hc'
  obtain ⟨hsmem, hlt⟩ := lt_iSup_iff.1 hs
  filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hsmem)] with z hz
  change c < liminf f (𝓝 z)
  refine lt_of_lt_of_le hlt ?_
  rw [liminf_eq_iSup_iInf]
  refine le_trans ?_
    (le_iSup₂ (f := fun t (_ : t ∈ 𝓝 z) => ⨅ a ∈ t, f a) (interior s)
      (isOpen_interior.mem_nhds hz))
  exact le_iInf₂ fun a ha => iInf₂_le a (interior_subset ha)

end Liminf

section LiminfHull

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  {f : E → EReal}

/-- **The lower semicontinuous hull is a `liminf`**: `(lsc f)(x) = liminf_{y → x} f(y)`.

`lscHull f` is the greatest lower semicontinuous minorant of `f`; the `liminf` function is a lower
semicontinuous minorant, and conversely a lower semicontinuous function is at most its own
`liminf`. -/
theorem lscHull_eq_liminf (f : E → EReal) (x : E) : lscHull f x = liminf f (𝓝 x) := by
  refine le_antisymm ?_ (le_lscHull_of_le (lowerSemicontinuous_liminf_nhds f) (liminf_nhds_le f) x)
  refine le_trans (LowerSemicontinuous.le_liminf (lowerSemicontinuous_lscHull f) x) ?_
  rw [liminf_eq_iSup_iInf, liminf_eq_iSup_iInf]
  exact iSup₂_mono fun s _ => iInf₂_mono fun a _ => lscHull_le f a

/-- **Rockafellar's `cl f = liminf f`**, in the regular branch: as soon as the lower semicontinuous
hull is nowhere `-∞`, the closure of `f` at `x` is the `liminf` of `f` at `x`. -/
theorem clFn_eq_liminf (h : ∀ z, lscHull f z ≠ ⊥) (x : E) : clFn f x = liminf f (𝓝 x) := by
  rw [clFn_of_forall_ne_bot h, lscHull_eq_liminf]

end LiminfHull

section LiminfConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f : E → EReal}

/-- **Rockafellar's `cl f = liminf f`, in full.** For a *convex* `f` the closure at `x` is the
`liminf` of `f` at `x`, except in the single degenerate case where the left side is `-∞` and the
right side is `+∞`.

The two can only differ in the exceptional branch of `clFn`, where `cl f` is the constant `-∞`;
and there `lscHull f` is a lower semicontinuous improper convex function, so by Corollary 7.2.1 it
takes only the values `-∞` and `+∞`. -/
theorem clFn_eq_liminf_or (hf : ConvexFn f) (x : E) :
    clFn f x = liminf f (𝓝 x) ∨ (clFn f x = ⊥ ∧ liminf f (𝓝 x) = ⊤) := by
  by_cases h : ∃ z, lscHull f z = ⊥
  · have hcl : clFn f x = ⊥ := by rw [clFn_of_exists_eq_bot h]
    rcases ConvexFn.eq_bot_or_eq_top (convexFn_lscHull hf) (lowerSemicontinuous_lscHull f) h x with
      hb | ht
    · exact Or.inl (by rw [hcl, ← lscHull_eq_liminf, hb])
    · exact Or.inr ⟨hcl, by rw [← lscHull_eq_liminf]; exact ht⟩
  · push Not at h
    exact Or.inl (by rw [clFn_of_forall_ne_bot h, lscHull_eq_liminf])

end LiminfConvex

end Tdaf.ConvexAnalysis
