/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Bifunction.Algebra
import Tdaf.Analysis.Convex.Duality.Relint
import Tdaf.Analysis.Convex.Saddle.Kernel

/-!
# Co-finite bifunctions

A convex bifunction is **co-finite** when every slice `Fu` is a co-finite convex function, that is,
a closed proper convex function whose epigraph contains no non-vertical half-line. Co-finiteness is
the condition under which the whole algebra of bifunctions loses its side conditions: the
relative-interior hypotheses of §38 become vacuous, because a co-finite bifunction has all of `U`
as its effective domain and an everywhere-finite inner product `⟨Fu, y⟩`.

This module also holds the half of Corollary 38.7.2 that needs a relative interior, for the same
reason that it needs a topology and a finite dimension: it is Corollary 33.2.1.

## Main definitions

* `CofiniteBifun F` — a convex bifunction all of whose slices are co-finite convex functions.

## Main results

* `CofiniteBifun.domBifun_eq_univ`, `CofiniteBifun.proper` — a co-finite bifunction has full
  effective domain and is proper.
* `CofiniteBifun.bracket_lt_top`, `CofiniteBifun.bracket_ne_bot`,
  `cofiniteBifun_of_forall_bracket_lt_top` — a closed convex bifunction is co-finite exactly when
  the inner product `⟨Fu, y⟩` is finite for every `u` and `y`. This is Corollary 13.3.1, slice by
  slice.
* `cofinite_infConv` — the infimal convolution of two co-finite convex *functions* is co-finite.
  A relocation candidate for `Duality/Level.lean`: it has nothing to do with bifunctions.
* `cofiniteBifun_infConvBifun`, `adjointBifun_infConvBifun_of_cofinite` — Rockafellar's remark at
  the end of §38: `F₁ □ F₂` is co-finite and `(F₁ □ F₂)* = F₁* □ F₂*`, with no hypothesis beyond
  co-finiteness.
* `cofinite_smulRight`, `cofiniteBifun_smulRightBifun` — Rockafellar's next sentence (16711): the
  operation `F ↦ Fλ`, `λ > 0`, likewise preserves co-finiteness. The closedness of `fa` that this
  needs — the half of Theorem 38.3 the library did not have — comes from exhibiting `fa` as the
  conjugate of `a f*`, which is Theorem 16.1's other row `conj_smul`.
* `CofiniteBifun.domConcaveBifun_adjointBifun_eq_univ`, `cofiniteBifun_of_domBifun_eq_univ`,
  `cofiniteBifun_iff_domBifun_eq_univ` — Rockafellar's criterion (16701): a closed proper convex
  bifunction is co-finite **iff** `dom F = U` and `dom F* = Y`. He cites Theorem 34.2; the proof
  here is Corollary 13.3.1 slice by slice and does not go through the saddle-function
  correspondence.
* `CofiniteBifun.bracket_eq_concaveBracket_adjointBifun` — `⟨Fu, y⟩ = ⟨u, F* y⟩` for *every* `u`,
  the co-finite form of Corollary 33.2.1.
* `bracket_compBifun_eq_concaveBracket_concaveCompBifun` — **Corollary 38.7.2**, the second
  equality `⟨GFu, z⟩ = ⟨u, F* G* z⟩`.

## Design notes

**Co-finiteness is a property of a convex bifunction, not of an arbitrary one.** Rockafellar
defines it for convex bifunctions only, and the convexity is genuinely extra data: the graph
function of a bifunction all of whose slices are convex need not be convex on `U × X`. So
`CofiniteBifun` carries `ConvexBifun` as a field.

**The exactness hypotheses of §38 are discharged, not assumed, in this file.** Everywhere else in
§38 the relative-interior conditions are carried as `IsExactSum` (design decision D5); for
co-finite bifunctions the functions being added are finite on the whole space, so
`IsExactSum.of_relint` applies at the origin and the hypothesis disappears. That is the content of
Rockafellar's closing remark, and it is why this module is the one place in §38 that is
finite-dimensional.

## What is not here

Of the three facts in Rockafellar's closing discussion (16693–16729), two are now here in full —
`□` and `Fλ` preserve co-finiteness, and the `dom F = U ∧ dom F* = Y` criterion — and what is left
is the third:

* **That `GF` is co-finite for co-finite `F` and `G`.** It needs the co-finite specialisation of
  Theorem 38.5 and Corollary 38.5.1, whose hypotheses are `IsExactSum` instances over four
  different spaces (`U`, `V`, `X`, `W`, `Y`, `Z` in `Bifunction/Algebra.lean`'s phrasing): the
  discharge that `Cofinite.isExactSum_conj` performs for `□` has to be repeated once for
  `concaveBracket Bu.flip (inverseBifun F) v` against `-(bracket By G · z)`, and co-finiteness of
  `F` bounds only the *second* variable of `F`, not `dom F⁎`. The wanted declaration is
  `theorem cofiniteBifun_compBifun (hF : CofiniteBifun F) (hG : CofiniteBifun G) :
  CofiniteBifun (compBifun G F)`, with `adjointBifun_compBifun_of_cofinite` beside it.
* **That `F*` is co-finite.** This one is blocked on *vocabulary*, not on a proof: `CofiniteBifun`
  is a predicate on *convex* bifunctions, `F*` is concave, and `lowerAdjointBifun Bu Bx F` is the
  wrong reindexing — for the indicator bifunction of a linear map `A` it is
  `(v, y) ↦ δ(v | A*y)`, which is not co-finite. What is wanted first is
  `def CofiniteConcaveBifun (G : Bifun Y V) : Prop := CofiniteBifun fun y v => -(G y v)`, and then
  `theorem cofiniteConcaveBifun_adjointBifun (hF : CofiniteBifun F) :
  CofiniteConcaveBifun (adjointBifun Bu Bx F)`, whose proof is
  `CofiniteBifun.bracket_eq_concaveBracket_adjointBifun` together with the concave mirror of
  `cofinite_iff_forall_conj_lt_top`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §38 (the closing remark
  on co-finiteness) and §13 (Corollary 13.3.1).
-/

open Set

namespace Tdaf.ConvexAnalysis

/-! ### Co-finite bifunctions -/

section Defs

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace X] {F : Bifun U X}

/-- A **co-finite convex bifunction** (Rockafellar, §38): a convex bifunction every slice of which
is a co-finite convex function.

Rockafellar notes at once that this forces `dom F = U` and makes `F` closed and proper; the first
of these is `CofiniteBifun.domBifun_eq_univ` and the last is `CofiniteBifun.proper`. -/
structure CofiniteBifun (F : Bifun U X) : Prop where
  /-- The bifunction is convex. -/
  convexBifun : ConvexBifun F
  /-- Every slice is a co-finite convex function. -/
  cofinite_apply : ∀ u, Cofinite (F u)

/-- Every slice of a co-finite bifunction is a closed proper convex function. -/
theorem CofiniteBifun.closedProperConvexFn_apply (hF : CofiniteBifun F) (u : U) :
    ClosedProperConvexFn (F u) := (hF.cofinite_apply u).toClosedProperConvexFn

/-- **Co-finiteness forces a full effective domain**: every slice is proper, so no `u` is missing
from `dom F`. -/
theorem CofiniteBifun.domBifun_eq_univ (hF : CofiniteBifun F) : domBifun F = univ :=
  eq_univ_of_forall fun u =>
    mem_domBifun_iff_dom_nonempty.2 (hF.cofinite_apply u).proper.dom_nonempty

/-- A co-finite bifunction is proper. -/
theorem CofiniteBifun.proper (hF : CofiniteBifun F) : Proper (graphFn F) := by
  obtain ⟨x, hx⟩ := (hF.cofinite_apply (0 : U)).proper.dom_nonempty
  exact ⟨⟨((0 : U), x), hx⟩, fun p => (hF.cofinite_apply p.1).proper.ne_bot p.2⟩

/-- A co-finite bifunction is nowhere `⊥`. -/
theorem CofiniteBifun.ne_bot (hF : CofiniteBifun F) (u : U) (x : X) : F u x ≠ ⊥ :=
  (hF.cofinite_apply u).proper.ne_bot x

end Defs

/-! ### Corollary 13.3.1, slice by slice -/

section BracketNeBot

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace X] [AddCommGroup Y] [Module ℝ Y] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  {F : Bifun U X}

/-- The companion of `CofiniteBifun.bracket_lt_top`: the inner product is never `-∞` either, since
every slice is proper. Together they say that `⟨Fu, y⟩` is finite. -/
theorem CofiniteBifun.bracket_ne_bot (hF : CofiniteBifun F) (u : U) (y : Y) :
    bracket Bx F u y ≠ ⊥ :=
  conj_ne_bot (hF.cofinite_apply u).proper.dom_nonempty y

end BracketNeBot

section Bracket

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
  {F : Bifun U X}

/-- **Rockafellar, §38**: for a co-finite bifunction the inner product `⟨Fu, y⟩` is never `+∞`.
This is Corollary 13.3.1 read at the slice `Fu`. -/
theorem CofiniteBifun.bracket_lt_top (hF : CofiniteBifun F) (u : U) (y : Y) :
    bracket Bx F u y < ⊤ :=
  (cofinite_iff_forall_conj_lt_top (B := Bx) (hF.closedProperConvexFn_apply u)).1
    (hF.cofinite_apply u) y

/-- **Rockafellar, §38**, the converse: a convex bifunction with closed proper convex slices is
co-finite as soon as `⟨Fu, y⟩` is finite for every `u` and `y`. -/
theorem cofiniteBifun_of_forall_bracket_lt_top (hF : ConvexBifun F)
    (hcl : ∀ u, ClosedProperConvexFn (F u)) (h : ∀ (u : U) (y : Y), bracket Bx F u y < ⊤) :
    CofiniteBifun F :=
  ⟨hF, fun u => (cofinite_iff_forall_conj_lt_top (B := Bx) (hcl u)).2 (h u)⟩

end Bracket

/-! ### Infimal convolution of co-finite functions -/

section CofiniteInfConv

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
  {f g : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- **Corollary 13.3.1**, forward: the conjugate of a co-finite function is finite everywhere. -/
theorem Cofinite.conj_lt_top (hf : Cofinite f) (y : F) : conj B f y < ⊤ :=
  (cofinite_iff_forall_conj_lt_top (B := B) hf.toClosedProperConvexFn).1 hf y

omit [FiniteDimensional ℝ E] in
/-- **Corollary 13.3.1**, forward, in the effective-domain phrasing. -/
theorem Cofinite.dom_conj_eq_univ (hf : Cofinite f) : dom (conj B f) = univ :=
  (cofinite_iff_dom_conj_eq_univ (B := B) hf.toClosedProperConvexFn).1 hf

/-- **The conjugates of two co-finite functions add exactly.** Their effective domains are the
whole space, so Rockafellar's relative-interior condition in Theorem 16.4 is satisfied at the
origin and `IsExactSum.of_relint` applies with no work. -/
theorem Cofinite.isExactSum_conj (hf : Cofinite f) (hg : Cofinite g) :
    IsExactSum B.flip (conj B f) (conj B g) := by
  have hdf : (0 : F) ∈ ri (dom (conj B f)) := by
    rw [Cofinite.dom_conj_eq_univ (B := B) hf, intrinsicInterior_univ]; trivial
  have hdg : (0 : F) ∈ ri (dom (conj B g)) := by
    rw [Cofinite.dom_conj_eq_univ (B := B) hg, intrinsicInterior_univ]; trivial
  exact IsExactSum.of_relint (convexFn_conj B f) (proper_conj hf.toClosedProperConvexFn)
    (convexFn_conj B g) (proper_conj hg.toClosedProperConvexFn) hdf hdg

/-- **The infimal convolution of two co-finite functions is a conjugate**, namely the conjugate of
`f* + g*`. This is what makes it closed. -/
theorem Cofinite.infConv_eq_conj_add (hf : Cofinite f) (hg : Cofinite g) :
    infConv f g = conj B.flip (conj B f + conj B g) := by
  have hbf : conj B.flip (conj B f) = f := biconj_eq_self hf.convex hf.closed
  have hbg : conj B.flip (conj B g) = g := biconj_eq_self hg.convex hg.closed
  rw [(Cofinite.isExactSum_conj (B := B) hf hg).conj_add, hbf, hbg]

omit [FiniteDimensional ℝ E] in
/-- The sum of the two conjugates is finite everywhere, hence proper. -/
theorem Cofinite.proper_conj_add (hf : Cofinite f) (hg : Cofinite g) :
    Proper (conj B f + conj B g) := by
  refine ⟨⟨0, ?_⟩, fun y => ?_⟩
  · rw [mem_dom, Pi.add_apply]
    exact _root_.EReal.add_lt_top (Cofinite.conj_lt_top (B := B) hf 0).ne
      (Cofinite.conj_lt_top (B := B) hg 0).ne
  · rw [Pi.add_apply, ne_eq, _root_.EReal.add_eq_bot_iff]
    push Not
    exact ⟨conj_ne_bot hf.proper.dom_nonempty y, conj_ne_bot hg.proper.dom_nonempty y⟩

/-- **The infimal convolution of two co-finite convex functions is co-finite.**

`f □ g` is the conjugate of `f* + g*` (`Cofinite.infConv_eq_conj_add`), hence closed proper convex,
and its own conjugate is `f* + g*` (`conj_infConv`, unconditional), which is finite everywhere. -/
theorem cofinite_infConv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] (hf : Cofinite f) (hg : Cofinite g) :
    Cofinite (infConv f g) := by
  have heq : infConv f g = conj B.flip (conj B f + conj B g) :=
    Cofinite.infConv_eq_conj_add (B := B) hf hg
  have hproper : Proper (infConv f g) := by
    refine ⟨?_, fun x => ?_⟩
    · obtain ⟨x, hx⟩ := hf.proper.dom_nonempty
      obtain ⟨z, hz⟩ := hg.proper.dom_nonempty
      exact ⟨x + z, by rw [dom_infConv]; exact ⟨x, hx, z, hz, rfl⟩⟩
    · rw [heq]
      exact conj_ne_bot (Cofinite.proper_conj_add (B := B) hf hg).dom_nonempty x
  have hclosed : ClosedFn (infConv f g) := by rw [heq]; exact closedFn_conj
  have hcpc : ClosedProperConvexFn (infConv f g) :=
    ⟨convexFn_infConv hf.convex hg.convex, hclosed, hproper⟩
  refine (cofinite_iff_forall_conj_lt_top (B := B) hcpc).2 fun y => ?_
  rw [conj_infConv, Pi.add_apply]
  exact _root_.EReal.add_lt_top (Cofinite.conj_lt_top (B := B) hf y).ne
    (Cofinite.conj_lt_top (B := B) hg y).ne

end CofiniteInfConv

/-! ### Rockafellar's closing remark: `F₁ □ F₂` -/

section CofiniteAlgebra

variable {U V X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
  {F F₁ F₂ : Bifun U X}

omit [FiniteDimensional ℝ U] in
/-- **Rockafellar, §38**: the infimal convolution of two co-finite convex bifunctions is
co-finite. Slice by slice this is `cofinite_infConv`; the convexity of `F₁ □ F₂` is Theorem
38.1. -/
theorem cofiniteBifun_infConvBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF₁ : CofiniteBifun F₁)
    (hF₂ : CofiniteBifun F₂) : CofiniteBifun (infConvBifun F₁ F₂) :=
  ⟨convexBifun_infConvBifun hF₁.ne_bot hF₂.ne_bot hF₁.convexBifun hF₂.convexBifun,
    fun u => cofinite_infConv Bx (hF₁.cofinite_apply u) (hF₂.cofinite_apply u)⟩

omit [FiniteDimensional ℝ X] in
/-- The two brackets of co-finite bifunctions add exactly: both are finite everywhere, so
`IsExactSum.of_relint` applies at the origin. This is what makes Theorem 38.2 unconditional for
co-finite bifunctions. -/
theorem isExactSum_neg_bracket_of_cofinite (hF₁ : CofiniteBifun F₁) (hF₂ : CofiniteBifun F₂)
    (y : Y) : IsExactSum Bu (fun u => -(bracket Bx F₁ u y)) (fun u => -(bracket Bx F₂ u y)) := by
  have hp : ∀ G : Bifun U X, CofiniteBifun G → Proper (fun u => -(bracket Bx G u y)) := by
    intro G hG
    refine ⟨⟨0, ?_⟩, fun u => ?_⟩
    · rw [mem_dom, lt_top_iff_ne_top, ne_eq, _root_.EReal.neg_eq_top_iff]
      exact CofiniteBifun.bracket_ne_bot (Bx := Bx) hG 0 y
    · rw [ne_eq, _root_.EReal.neg_eq_bot_iff]
      exact (CofiniteBifun.bracket_lt_top (Bx := Bx) hG u y).ne
  have hd : ∀ G : Bifun U X, CofiniteBifun G →
      (0 : U) ∈ ri (dom fun u => -(bracket Bx G u y)) := by
    intro G hG
    have hdom : (dom fun u => -(bracket Bx G u y)) = univ :=
      eq_univ_of_forall fun u => by
        rw [mem_dom, lt_top_iff_ne_top, ne_eq, _root_.EReal.neg_eq_top_iff]
        exact CofiniteBifun.bracket_ne_bot (Bx := Bx) hG u y
    rw [hdom, intrinsicInterior_univ]; trivial
  exact IsExactSum.of_relint (concaveFn_iff_convexFn_neg.1 (concaveFn_bracket hF₁.convexBifun Bx y))
    (hp F₁ hF₁) (concaveFn_iff_convexFn_neg.1 (concaveFn_bracket hF₂.convexBifun Bx y))
    (hp F₂ hF₂) (hd F₁ hF₁) (hd F₂ hF₂)

omit [FiniteDimensional ℝ X] in
/-- **Rockafellar, §38**: `(F₁ □ F₂)* = F₁* □ F₂*` for co-finite bifunctions, with the exactness
hypothesis of Theorem 38.2 discharged. -/
theorem adjointBifun_infConvBifun_of_cofinite (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF₁ : CofiniteBifun F₁) (hF₂ : CofiniteBifun F₂) :
    adjointBifun Bu Bx (infConvBifun F₁ F₂)
      = supConvBifun (adjointBifun Bu Bx F₁) (adjointBifun Bu Bx F₂) :=
  adjointBifun_infConvBifun_eq_supConvBifun Bu Bx F₁ F₂
    (isExactSum_neg_bracket_of_cofinite hF₁ hF₂)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- **Rockafellar, §38**: for a co-finite bifunction the two inner products agree *everywhere*,
`⟨Fu, y⟩ = ⟨u, F* y⟩`. This is Corollary 33.2.1 with `ri (dom F) = U`. -/
theorem CofiniteBifun.bracket_eq_concaveBracket_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : CofiniteBifun F) (u : U) (y : Y) :
    bracket Bx F u y = concaveBracket Bu (adjointBifun Bu Bx F) u y :=
  bracket_eq_concaveBracket_adjointBifun_of_mem_relint Bu Bx hF.convexBifun
    (by rw [hF.domBifun_eq_univ, intrinsicInterior_univ]; trivial) y

end CofiniteAlgebra

/-! ### Rockafellar's closing remark: `Fλ` -/

section CofiniteSmulRight

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : E → EReal} {a : ℝ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **`fa` is a conjugate**, for `a > 0` and a closed convex `f`: it is the conjugate of `a f*`.

This is Theorem 16.1's row `conj_smul` — `(a g)* = (g*)a` — read at `g = f*`, with Fenchel–Moreau
turning `f**` back into `f`. It is what supplies the closedness half of Rockafellar's Theorem 38.3,
"`Fλ` is closed or proper according as `F` itself is closed or proper", which the library
otherwise lacks: `smulRight` is defined by an epigraph image (`Homogenize.lean`) and nothing there
sees a topology. -/
theorem smulRight_eq_conj_smul (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] (hc : ConvexFn f) (hcl : ClosedFn f)
    (ha : 0 < a) : smulRight f a = conj B.flip (fun y => (a : EReal) * conj B f y) := by
  have hbi : conj B.flip (conj B f) = f := biconj_eq_self hc hcl
  rw [conj_smul ha B.flip (conj B f), hbi]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Rockafellar, Theorem 38.3**, closedness: `fa` is closed when `f` is closed convex and
`a > 0`. It is a conjugate (`smulRight_eq_conj_smul`). -/
theorem closedFn_smulRight (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] (hc : ConvexFn f) (hcl : ClosedFn f)
    (ha : 0 < a) : ClosedFn (smulRight f a) := by
  rw [smulRight_eq_conj_smul B hc hcl ha]
  exact closedFn_conj

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- A positive real multiple of an `EReal` is `-∞` only where the `EReal` is. -/
theorem coe_mul_ne_bot (ha : 0 < a) {u : EReal} (hu : u ≠ ⊥) : (a : EReal) * u ≠ ⊥ := by
  intro h
  refine Tdaf.EReal.coe_mul_ne_top ha (u := -u) (by rwa [Ne, _root_.EReal.neg_eq_top_iff]) ?_
  rw [mul_neg, h, _root_.EReal.neg_bot]

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- **Rockafellar, Theorem 38.3**, properness: `fa` is proper when `f` is and `a > 0`. -/
theorem proper_smulRight (hf : Proper f) (ha : 0 < a) : Proper (smulRight f a) := by
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨x₀, hx₀⟩ := hf.dom_nonempty
    refine ⟨a • x₀, mem_dom.2 (lt_top_iff_ne_top.2 ?_)⟩
    rw [smulRight_apply_pos ha, inv_smul_smul₀ ha.ne']
    exact Tdaf.EReal.coe_mul_ne_top ha (mem_dom.1 hx₀).ne
  · rw [smulRight_apply_pos ha]
    exact coe_mul_ne_bot ha (hf.ne_bot _)

omit [FiniteDimensional ℝ E] in
/-- **Right scalar multiplication preserves co-finiteness**, for `a > 0`: Rockafellar's remark
that "the operation `F → Fλ`, `λ > 0`, likewise preserves co-finiteness" (§38, 16711), one slice
at a time.

The closedness half of Theorem 38.3 is `closedFn_smulRight` and the properness half is
`proper_smulRight`; what is left is `conj_smulRight` — `(fa)* = a f*` — together with Corollary
13.3.1. -/
theorem cofinite_smulRight (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] (hf : Cofinite f) (ha : 0 < a) :
    Cofinite (smulRight f a) := by
  have hne : ∀ y : F, (a : EReal) * conj B f y ≠ ⊤ :=
    fun y => Tdaf.EReal.coe_mul_ne_top ha (Cofinite.conj_lt_top (B := B) hf y).ne
  have hcpc : ClosedProperConvexFn (smulRight f a) :=
    ⟨convexFn_smulRight a hf.convex, closedFn_smulRight B hf.convex hf.closed ha,
      proper_smulRight hf.proper ha⟩
  refine (cofinite_iff_forall_conj_lt_top (B := B) hcpc).2 fun y => ?_
  rw [conj_smulRight ha B f]
  exact lt_top_iff_ne_top.2 (hne y)

end CofiniteSmulRight

/-! ### Rockafellar's closing remark: `Fλ` and Theorem 34.2 for bifunctions -/

section Cofinite342

variable {U V X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
  {F : Bifun U X} {l : ℝ}

omit [FiniteDimensional ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [FiniteDimensional ℝ X] in
/-- **Rockafellar, §38 (16711)**: `F → Fλ` preserves co-finiteness for `λ > 0`.

Slice by slice this is `cofinite_smulRight`; the convexity of `Fλ` is Theorem 38.3. -/
theorem cofiniteBifun_smulRightBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : CofiniteBifun F) (hl : 0 < l) :
    CofiniteBifun (smulRightBifun F l) :=
  ⟨convexBifun_smulRightBifun hl hF.convexBifun,
    fun u => cofinite_smulRight Bx (hF.cofinite_apply u) hl⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ X] in
/-- **The adjoint of a co-finite bifunction has full effective domain**: `dom F* = Y`.

This is the half of Rockafellar's co-finiteness criterion (16701) that needs no closedness. The
bracket `⟨F·, y⟩` is a finite concave function on `U`, so its negative is proper convex and
`proper_conj_of_proper` (Theorem 12.1 in finite dimensions) makes the conjugate proper; the sign
dictionary `neg_concaveConj` carries that back to `F* y`, which is therefore somewhere `> -∞`. -/
theorem CofiniteBifun.domConcaveBifun_adjointBifun_eq_univ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : CofiniteBifun F) :
    domConcaveBifun (adjointBifun Bu Bx F) = univ := by
  refine eq_univ_of_forall fun y => ?_
  have hgc : ConvexFn (fun u => -(bracket Bx F u y)) :=
    concaveFn_iff_convexFn_neg.1 (concaveFn_bracket hF.convexBifun Bx y)
  have hgp : Proper (fun u => -(bracket Bx F u y)) := by
    refine ⟨⟨0, mem_dom.2 (lt_top_iff_ne_top.2 ?_)⟩, fun u => ?_⟩
    · rw [ne_eq, _root_.EReal.neg_eq_top_iff]
      exact CofiniteBifun.bracket_ne_bot (Bx := Bx) hF 0 y
    · rw [ne_eq, _root_.EReal.neg_eq_bot_iff]
      exact (CofiniteBifun.bracket_lt_top (Bx := Bx) hF u y).ne
  obtain ⟨w, hw⟩ := (proper_conj_of_proper (B := Bu) hgc hgp).dom_nonempty
  refine ⟨-w, ?_⟩
  have hneg : -(concaveConj Bu (fun u => bracket Bx F u y) (-w))
      = conj Bu (fun u => -(bracket Bx F u y)) w := by
    rw [neg_concaveConj, neg_neg]
  rw [adjointBifun_eq_concaveConj_bracket, ne_eq, ← _root_.EReal.neg_eq_top_iff, hneg]
  exact (mem_dom.1 hw).ne

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [FiniteDimensional ℝ X]
  [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] in
/-- **Rockafellar, §38 (16701)**, the substantial direction of his Theorem 34.2 criterion: a
closed proper convex bifunction with `dom F = U` and `dom F* = Y` is co-finite.

`dom F = U` makes every bracket `⟨Fu, y⟩` finite below (`domConcave_bracket`), and `dom F* = Y`
makes it finite above: if `⟨Fu₀, y⟩ = +∞` for a single `u₀`, then `F* y` is identically `-∞`
(`concaveConj_of_eq_top`) and `y` is outside `dom F*`. Corollary 13.3.1, slice by slice
(`cofiniteBifun_of_forall_bracket_lt_top`), does the rest. -/
theorem cofiniteBifun_of_domBifun_eq_univ (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hp : Proper (graphFn F)) (hdom : domBifun F = univ)
    (hadj : domConcaveBifun (adjointBifun Bu Bx F) = univ) : CofiniteBifun F := by
  refine cofiniteBifun_of_forall_bracket_lt_top (Bx := Bx) hF (fun u => ?_) (fun u y => ?_)
  · refine ⟨hF.convexFn_apply u, hcl.imageClosedBifun u, ⟨?_, fun x => hp.ne_bot (u, x)⟩⟩
    exact mem_domBifun_iff_dom_nonempty.1 (by rw [hdom]; trivial)
  · rcases lt_or_eq_of_le (le_top : bracket Bx F u y ≤ ⊤) with h | htop
    · exact h
    · exfalso
      obtain ⟨v, hv⟩ : y ∈ domConcaveBifun (adjointBifun Bu Bx F) := by rw [hadj]; trivial
      refine hv ?_
      rw [adjointBifun_eq_concaveConj_bracket]
      exact congrFun (concaveConj_of_eq_top (B := Bu)
        (g := fun u' => bracket Bx F u' y) htop) v

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ X] [IsCompatiblePairing Bu.flip] in
/-- **Rockafellar, §38 (16701)**: a closed proper convex bifunction is co-finite **if and only
if** `dom F = U` and `dom F* = Y`. Rockafellar cites Theorem 34.2 for this; the proof here is
Corollary 13.3.1 slice by slice, and does not go through the saddle-function correspondence. -/
theorem cofiniteBifun_iff_domBifun_eq_univ (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hp : Proper (graphFn F)) :
    CofiniteBifun F ↔
      domBifun F = univ ∧ domConcaveBifun (adjointBifun Bu Bx F) = univ :=
  ⟨fun h => ⟨h.domBifun_eq_univ,
      CofiniteBifun.domConcaveBifun_adjointBifun_eq_univ Bu Bx h⟩,
    fun h => cofiniteBifun_of_domBifun_eq_univ hF hcl hp h.1 h.2⟩

end Cofinite342

/-! ### Corollary 38.7.2, the second equality -/

section Cor3872

variable {U V X W Y Z : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  {F : Bifun U X} {G : Bifun X Y}

/-- **Rockafellar, Corollary 38.7.2**, the second equality: `⟨GFu, z⟩ = ⟨u, F* G* z⟩`.

Corollary 33.2.1 puts the two brackets of `GF` together at a relative interior point of
`dom (GF)`, and Theorem 38.5 (`adjointBifun_compBifun`) rewrites `(GF)*` as the concave product
`F* G*`. The first equality, `⟨GFu, z⟩ = ⟨Fu, G* z⟩`, needs no relative interior and is
`bracket_compBifun_eq_fenchelPairing` in `Bifunction/Algebra.lean`. -/
theorem bracket_compBifun_eq_concaveBracket_concaveCompBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ) (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ)
    (hbF : ∀ u x, F u x ≠ ⊥) (hGF : ConvexBifun (compBifun G F)) {u : U}
    (hu : u ∈ ri (domBifun (compBifun G F))) {z : Z}
    (hex : ∀ v : V, IsExactSum Bx (concaveBracket Bu.flip (inverseBifun F) v)
      (fun x => -(bracket By G x z))) :
    bracket By (compBifun G F) u z
      = concaveBracket Bu (concaveCompBifun (adjointBifun Bx By G) (adjointBifun Bu Bx F)) u z := by
  rw [bracket_eq_concaveBracket_adjointBifun_of_mem_relint Bu By hGF hu z, concaveBracket_apply,
    concaveBracket_apply]
  exact iInf_congr fun v => by rw [adjointBifun_compBifun Bu Bx By hbF (hex v)]

end Cor3872

end Tdaf.ConvexAnalysis
