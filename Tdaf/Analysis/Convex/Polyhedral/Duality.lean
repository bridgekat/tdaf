/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Polyhedral.Conjugate
import Tdaf.Analysis.Convex.Duality.Relint
import Tdaf.Analysis.Convex.Indicator

/-!
# Polyhedral constraint qualifications

Rockafellar's §20: the constraint qualifications of §16 weaken when one of the two functions is
polyhedral. `Duality/Relint.lean` asks for a *common relative interior point* of the two effective
domains; here the polyhedral side contributes only a point of its effective domain.

## Main results

* `IsExactSum.of_polyhedral_pair` — the case where *both* functions are polyhedral: no relative
  interiors are involved at all, only `dom f ∩ dom g ≠ ∅`.
* `IsExactSum.of_polyhedral` — **Theorem 20.1**: a polyhedral `f` and a closed proper convex `g`
  add exactly as soon as `dom f` meets `ri (dom g)`.
* `relint_inter_relint_nonempty_of_subset_affineSpan` — the relative-interior step the proof of
  Theorem 20.1 turns on.

## Design notes

**The pair case is `of_relint`'s proof with Corollary 9.1.1 replaced by polyhedrality.** Both
proofs need the same one fact, that `epi f* + epi g*` is closed; `of_relint` gets it from the
recession-cone criterion, and here it is free, because a sum of polyhedral sets is polyhedral
(**Corollary 19.3.2**) and a polyhedral set is closed. Everything downstream —
`epi_infConv_of_polyhedralFn` (**Corollary 19.3.4**), properness of `f* □ g*`, and the splitting
that `IsExactSum.exact_le` asks for — is then identical.

**`ClosedFn` is not a hypothesis on the polyhedral side.** A polyhedral convex function that is
proper is automatically closed (`PolyhedralFn.closedFn`), so where `of_relint` takes
`ClosedProperConvexFn` this file takes `PolyhedralFn` plus `Proper`. On the *non*-polyhedral side
closedness is still asked for, exactly as in `of_relint` and for the same reason: Theorem 12.2 is
what makes `g*` proper.

**The general case is Rockafellar's own reduction, and it runs on an indicator.** With
`M = aff (dom g)` and `δ = δ(· | M)`, the function `δ + f` is again polyhedral — `M` is polyhedral
by `polyhedral_coe_affineSubspace` — and its effective domain `M ∩ dom f` *does* have a relative
interior point in common with `dom g`, so `of_relint` applies to `δ + f` and `g`. Since `δ` is
absorbed by anything whose effective domain lies in `M`, both `δ + g = g` and `δ + (f + g) = f + g`;
splitting `(δ + f)*` with the pair case and re-absorbing the leftover `δ*` into `g*` with the first
identity turns the exact splitting for `δ + f` into one for `f`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §20.
-/

open Set
open scoped Pointwise

namespace Tdaf.ConvexAnalysis

section Sum

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

omit [FiniteDimensional ℝ F] in
/-- A proper polyhedral convex function is a closed proper convex function. -/
theorem PolyhedralFn.closedProperConvexFn (hf : PolyhedralFn f) (hpf : Proper f) :
    ClosedProperConvexFn f :=
  ⟨hf.convexFn, hf.closedFn hpf.ne_bot, hpf⟩

/-- **The polyhedral case of Rockafellar's Theorem 20.1**, for two polyhedral functions: proper
polyhedral convex functions add exactly as soon as their effective domains meet — no relative
interior is needed on either side.

This is the case `k = m` of the theorem, and it is the base case its general form is reduced to. -/
theorem IsExactSum.of_polyhedral_pair [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : PolyhedralFn f) (hpf : Proper f) (hg : PolyhedralFn g) (hpg : Proper g)
    {x₀ : E} (hxf : x₀ ∈ dom f) (hxg : x₀ ∈ dom g) : IsExactSum B f g := by
  have hfc : ClosedProperConvexFn f := hf.closedProperConvexFn hpf
  have hgc : ClosedProperConvexFn g := hg.closedProperConvexFn hpg
  have hup : Proper (conj B f) := proper_conj hfc
  have hvp : Proper (conj B g) := proper_conj hgc
  -- **Corollary 19.3.2**: the sum of the two dual epigraphs is polyhedral, hence closed
  have hclosed : IsClosed (epi (conj B f) + epi (conj B g)) :=
    Polyhedral.isClosed (Polyhedral.add (PolyhedralFn.conj hf) (PolyhedralFn.conj hg))
  -- **Corollary 19.3.4**: so that sum *is* the epigraph of the infimal convolute
  have hepiEq : epi (infConv (conj B f) (conj B g)) = epi (conj B f) + epi (conj B g) :=
    epi_infConv_of_polyhedralFn (PolyhedralFn.conj hf) (PolyhedralFn.conj hg)
  have hdomne : (dom (f + g)).Nonempty :=
    ⟨x₀, by
      rw [mem_dom, Pi.add_apply]
      exact _root_.EReal.add_lt_top (mem_dom.1 hxf).ne (mem_dom.1 hxg).ne⟩
  have hproper : Proper (infConv (conj B f) (conj B g)) := by
    refine ⟨?_, fun y hy => ?_⟩
    · obtain ⟨p, hp⟩ := hup.dom_nonempty
      obtain ⟨q, hq⟩ := hvp.dom_nonempty
      exact ⟨p + q, by rw [dom_infConv]; exact Set.add_mem_add hp hq⟩
    · have hle := conj_add_le_infConv B f g y
      rw [hy, le_bot_iff] at hle
      exact conj_ne_bot hdomne y hle
  have hclosedFn : ClosedFn (infConv (conj B f) (conj B g)) :=
    (ClosedProperConvexFn.of_isClosed_epi
      (convexFn_infConv (convexFn_conj B f) (convexFn_conj B g))
      (by rw [hepiEq]; exact hclosed) hproper).closed
  have hconjadd : conj B (f + g) = infConv (conj B f) (conj B g) := by
    rw [conj_add_eq_clFn_infConv hfc.convex hfc.closed hgc.convex hgc.closed]
    exact hclosedFn
  refine ⟨hpf, hpg, fun y => ?_⟩
  rw [hconjadd]
  rcases eq_top_or_lt_top (infConv (conj B f) (conj B g) y) with htop | htop
  · exact ⟨y, 0, add_zero y, by rw [htop]; exact le_top⟩
  obtain ⟨μ, hμ⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hproper.ne_bot y) htop
  have hmem : ((y, μ) : F × ℝ) ∈ epi (conj B f) + epi (conj B g) := by
    rw [← hepiEq]; exact mk_mem_epi.2 hμ.le
  obtain ⟨⟨y₁, a⟩, h₁, ⟨y₂, b⟩, h₂, heq⟩ := hmem
  refine ⟨y₁, y₂, congrArg Prod.fst heq, ?_⟩
  have hab : a + b = μ := congrArg Prod.snd heq
  rw [hμ]
  calc conj B f y₁ + conj B g y₂ ≤ ((a : ℝ) : EReal) + ((b : ℝ) : EReal) :=
        add_le_add (mk_mem_epi.1 h₁) (mk_mem_epi.1 h₂)
    _ = ((μ : ℝ) : EReal) := by rw [← _root_.EReal.coe_add, hab]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- An indicator function is absorbed by any function whose effective domain it contains. This is
the algebraic device the proof of Theorem 20.1 runs on: with `M = aff (dom g)` both
`indicatorFn M + g` and `indicatorFn M + (f + g)` collapse. No properness is needed — off `C` the
sum is `⊤ + ⊤`. -/
theorem indicatorFn_add_eq_self {C : Set E} {k : E → EReal}
    (hsub : dom k ⊆ C) : indicatorFn C + k = k := by
  funext x
  by_cases hx : x ∈ C
  · rw [Pi.add_apply, indicatorFn_of_mem hx, zero_add]
  · have hxk : k x = ⊤ := by
      by_contra hcon
      exact hx (hsub (mem_dom.2 (lt_top_iff_ne_top.2 hcon)))
    rw [Pi.add_apply, indicatorFn_of_notMem hx, hxk]
    simp

omit [FiniteDimensional ℝ F] in
/-- **The relative-interior step in Rockafellar's proof of Theorem 20.1.** If a convex set `D₁`
lies in the affine hull of a convex set `D₂` and the two share a point of `ri D₂`, then `ri D₁`
and `ri D₂` already share a point.

The shared point `x₀` need not itself be in `ri D₁`. But `ri D₂` is a relatively open
neighbourhood of `x₀` inside `aff D₂`, which contains `aff D₁`, so a small push from `x₀` towards
any point of `ri D₁` — nonempty by Theorem 6.2 — lands in both. Both pushes are the line segment
principle (Theorem 6.1); the prolongation principle (Theorem 6.4), applied to the reflection of
that point in `x₀`, is what produces a point of `D₂` beyond `x₀` for the second one to start
from. -/
theorem relint_inter_relint_nonempty_of_subset_affineSpan {D₁ D₂ : Set E}
    (h₁ : Convex ℝ D₁) (h₂ : Convex ℝ D₂) (hsub : D₁ ⊆ (affineSpan ℝ D₂ : Set E))
    {x₀ : E} (hx₁ : x₀ ∈ D₁) (hx₂ : x₀ ∈ ri D₂) : (ri D₁ ∩ ri D₂).Nonempty := by
  obtain ⟨z, hz⟩ := Convex.relint_nonempty h₁ ⟨x₀, hx₁⟩
  have hzD₁ : z ∈ D₁ := intrinsicInterior_subset hz
  have hzM : z ∈ affineSpan ℝ D₂ := hsub hzD₁
  have hx₀D₂ : x₀ ∈ D₂ := intrinsicInterior_subset hx₂
  have hx₀M : x₀ ∈ affineSpan ℝ D₂ := subset_affineSpan ℝ D₂ hx₀D₂
  -- the reflection of `z` in `x₀` still lies in the affine hull of `D₂`
  have hyM : (1 : ℝ) • (x₀ -ᵥ z) +ᵥ x₀ ∈ affineSpan ℝ D₂ :=
    AffineSubspace.smul_vsub_vadd_mem _ 1 hx₀M hzM hx₀M
  obtain ⟨μ, hμ, hmem⟩ := exists_one_lt_smul_mem_of_mem_relint hx₂ hyM
  set t : ℝ := μ - 1 with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  have hxt : (1 - t) • x₀ + t • z ∈ D₂ := by
    have heq : (1 - μ) • ((1 : ℝ) • (x₀ -ᵥ z) +ᵥ x₀) + μ • x₀ = (1 - t) • x₀ + t • z := by
      simp only [vsub_eq_sub, vadd_eq_add, one_smul, ht]
      module
    rwa [heq] at hmem
  set s : ℝ := min (t / 2) 1 with hs
  have hs0 : 0 < s := lt_min (by linarith) one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hst : s < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨(1 - s) • x₀ + s • z, ?_, ?_⟩
  · have hseg := Convex.segment_mem_relint h₁ hz (subset_closure hx₁)
      (a := 1 - s) (by linarith) (by linarith)
    have heq : (1 - (1 - s)) • z + (1 - s) • x₀ = (1 - s) • x₀ + s • z := by module
    rwa [heq] at hseg
  · have hseg := Convex.segment_mem_relint h₂ hx₂ (subset_closure hxt)
      (a := s / t) (by positivity) ((div_lt_one ht0).2 hst)
    have heq : (1 - s / t) • x₀ + (s / t) • ((1 - t) • x₀ + t • z) = (1 - s) • x₀ + s • z := by
      match_scalars <;> (field_simp; try ring)
    rwa [heq] at hseg

/-- **Rockafellar, Theorem 20.1.** A proper polyhedral convex function and a closed proper convex
function add exactly as soon as `dom f` meets `ri (dom g)`: the polyhedral side contributes only a
point of its effective domain, not of its relative interior.

The proof is Rockafellar's. Let `M = aff (dom g)` and `δ = δ(· | M)`, and put `h = δ + f`. Then
`ri (dom h)` does meet `ri (dom g)`, so `of_relint` splits `(h + g)* = (f + g)*` exactly; the pair
case splits `h*` as `δ* □ f*`; and `δ* □ g* = (δ + g)* = g*` re-absorbs the `δ*` that the first
split left over. -/
theorem IsExactSum.of_polyhedral [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : PolyhedralFn f) (hpf : Proper f) (hg : ClosedProperConvexFn g)
    {x₀ : E} (hxf : x₀ ∈ dom f) (hxg : x₀ ∈ ri (dom g)) : IsExactSum B f g := by
  classical
  have hx₀g : x₀ ∈ dom g := intrinsicInterior_subset hxg
  set MA : AffineSubspace ℝ E := affineSpan ℝ (dom g) with hMA
  have hx₀M : x₀ ∈ MA := subset_affineSpan ℝ (dom g) hx₀g
  have hdomgM : dom g ⊆ (MA : Set E) := subset_affineSpan ℝ (dom g)
  set δ : E → EReal := indicatorFn (MA : Set E) with hδdef
  have hδbot : ∀ x, δ x ≠ ⊥ := fun x => indicatorFn_ne_bot _ x
  have hδdom : dom δ = (MA : Set E) := dom_indicatorFn _
  have hδpoly : PolyhedralFn δ :=
    polyhedralFn_indicatorFn (polyhedral_coe_affineSubspace hx₀M)
  have hδproper : Proper δ := ⟨⟨x₀, by rw [hδdom]; exact hx₀M⟩, hδbot⟩
  have hδcpc : ClosedProperConvexFn δ := hδpoly.closedProperConvexFn hδproper
  have hx₀δ : x₀ ∈ dom δ := by rw [hδdom]; exact hx₀M
  -- `h = δ + f` is polyhedral and proper, with `dom h = M ∩ dom f`
  have hhpoly : PolyhedralFn (δ + f) := PolyhedralFn.add hδpoly hf hδbot hpf.ne_bot
  have hhbot : ∀ x, (δ + f) x ≠ ⊥ := fun x =>
    _root_.EReal.add_ne_bot_iff.2 ⟨hδbot x, hpf.ne_bot x⟩
  have hhdom : dom (δ + f) = (MA : Set E) ∩ dom f := by
    rw [dom_add hδbot hpf.ne_bot, hδdom]
  have hx₀h : x₀ ∈ dom (δ + f) := by rw [hhdom]; exact ⟨hx₀M, hxf⟩
  have hhproper : Proper (δ + f) := ⟨⟨x₀, hx₀h⟩, hhbot⟩
  have hhcpc : ClosedProperConvexFn (δ + f) := hhpoly.closedProperConvexFn hhproper
  -- the relative-interior step
  obtain ⟨x₁, hx₁h, hx₁g⟩ :=
    relint_inter_relint_nonempty_of_subset_affineSpan
      (PolyhedralFn.convexFn hhpoly).convex_dom hg.convex.convex_dom
      (by rw [hhdom]; exact fun x hx => hx.1) hx₀h hxg
  -- the three exact splittings
  have hAg : IsExactSum B (δ + f) g := IsExactSum.of_relint hhcpc hg hx₁h hx₁g
  have hδf : IsExactSum B δ f := IsExactSum.of_polyhedral_pair hδpoly hδproper hf hpf hx₀δ hxf
  have hx₀riδ : x₀ ∈ ri (dom δ) := by
    rw [hδdom, AffineSubspace.intrinsicInterior_coe]; exact hx₀M
  have hδg : IsExactSum B δ g := IsExactSum.of_relint hδcpc hg hx₀riδ hxg
  -- `δ` is absorbed on both sides
  have hsumδg : δ + g = g := indicatorFn_add_eq_self hdomgM
  have hsum : δ + f + g = f + g := by
    rw [add_assoc]
    exact indicatorFn_add_eq_self
      (by rw [dom_add hpf.ne_bot hg.proper.ne_bot]; exact fun x hx => hdomgM hx.2)
  have hδne : ∀ y : F, conj B δ y ≠ ⊥ := fun y => conj_ne_bot hδproper.dom_nonempty y
  have hgne : ∀ y : F, conj B g y ≠ ⊥ := fun y => conj_ne_bot hg.proper.dom_nonempty y
  have hgconj : conj B g = infConv (conj B δ) (conj B g) := by
    have h0 := hδg.conj_add
    rwa [hsumδg] at h0
  refine ⟨hpf, hg.proper, fun y => ?_⟩
  obtain ⟨z₁, z₂, hz, hzle⟩ := hAg.exact_le y
  obtain ⟨u, v, huv, huvle⟩ := hδf.exact_le z₁
  have habs : conj B g (u + z₂) ≤ conj B δ u + conj B g z₂ := by
    have hle := infConv_le_add (f := conj B δ) (g := conj B g) hδne hgne (u + z₂) z₂
    rw [add_sub_cancel_right] at hle
    calc conj B g (u + z₂) = infConv (conj B δ) (conj B g) (u + z₂) := by rw [← hgconj]
      _ ≤ conj B δ u + conj B g z₂ := hle
  refine ⟨v, u + z₂, ?_, ?_⟩
  · rw [← hz, ← huv]; abel
  · calc conj B f v + conj B g (u + z₂)
        ≤ conj B f v + (conj B δ u + conj B g z₂) := add_le_add le_rfl habs
      _ = conj B δ u + conj B f v + conj B g z₂ := by
          rw [← add_assoc, add_comm (conj B f v)]
      _ ≤ conj B (δ + f) z₁ + conj B g z₂ := add_le_add huvle le_rfl
      _ ≤ conj B (δ + f + g) y := hzle
      _ = conj B (f + g) y := by rw [hsum]

end Sum

end Tdaf.ConvexAnalysis
