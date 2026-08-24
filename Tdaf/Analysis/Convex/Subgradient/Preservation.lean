/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Ops
import Tdaf.Analysis.Convex.Operations.Closed
import Tdaf.Analysis.Convex.Duality.Relint
import Tdaf.Analysis.Convex.Recession.Closedness
import Tdaf.Analysis.Convex.Subgradient.StrictlyConvex

/-!
# Preservation of essential smoothness

Rockafellar's **Corollaries 26.3.2 and 26.3.3**: essential smoothness survives infimal convolution
and the image under a linear map, under the exactness hypotheses of §16.

Both are the same argument, run through Theorem 26.3. Essential smoothness of `f` is essential
*strict* convexity of `f*`; the dual operation on the conjugate side is a sum (for `□`) or a
composition with the transpose (for the image); Theorems 23.8 and 23.9 shrink the domain of the
subdifferential of that dual object into `dom ∂f*`; and essential strict convexity of `f*` then
transfers, because adding a convex function or precomposing with an injective linear map preserves
strict convexity on a set. Theorem 26.3 read backwards returns essential smoothness.

## Main results

* `StrictConvexOnFn.add_convexFn` — a strictly convex summand makes the sum strictly convex, on a
  set where both summands are finite.
* `StrictConvexOnFn.compLin` — strict convexity pulls back along an injective linear map.
* `IsExactSum.essentiallyStrictlyConvex_add` — the conjugate-side statement of Corollary 26.3.2.
* `IsExactSum.essentiallySmooth_infConv`, `essentiallySmooth_infConv_of_relint` —
  **Rockafellar, Corollary 26.3.2**.
* `injective_of_isAdjointPair_of_surjective` — an onto `A` has an injective transpose.
* `IsExactImage.essentiallyStrictlyConvex_compLin` — the conjugate-side statement of
  Corollary 26.3.3.
* `IsExactImage.essentiallySmooth_mapLin`, `essentiallySmooth_mapLin_of_relint` —
  **Rockafellar, Corollary 26.3.3**.

## Design notes

**The `ri` hypotheses are carried by the D5 interfaces.** Rockafellar's hypotheses are
`ri (dom f₁*) ∩ ri (dom f₂*) ≠ ∅` and `∃ y*, A' y* ∈ ri (dom f*)`. Both are *sufficient conditions*
for `IsExactSum` and `IsExactImage` (`IsExactSum.of_relint`, `IsExactImage.of_relint`), and both
theorems are stated against the interfaces, with the book's form as a corollary. That is what makes
the polyhedral (§20) and continuity (§10) qualifications applicable to the same two theorems
without restating them.

**The transpose is on the left in Corollary 26.3.3.** The identity being used is
`A f = (f* A')*`, so the *interface* instance is `IsExactImage` for the map `A'` from the dual of
the target to the dual of the source, paired the other way round: `IsExactImage (innerₗ G)
(innerₗ E) A' A hA f*`. The theorem's `hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A` is exactly
`⟪y, A x⟫ = ⟪A' y, x⟫`, so it is the ordinary adjointness relation read with the arguments in the
order the interface wants.

**"`A` onto" is used only through `Function.Injective A'`.** The interface-level theorem asks for
the injectivity, which is the property the strict-convexity transfer consumes;
`injective_of_isAdjointPair_of_surjective` derives it from Rockafellar's hypothesis and is what the
`ri` corollary applies.

**Finiteness is a hypothesis of `StrictConvexOnFn.add_convexFn`, not a consequence.** On a set where
`f` is `+∞` the strict inequality is vacuous but the sum's is not, so the two summands must be known
finite on `C`. At the use site `C ⊆ dom ∂(f₁* + f₂*) ⊆ dom (f₁* + f₂*)`, and `dom_add` splits that.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §26 (Corollary 26.3.2,
  Corollary 26.3.3).
-/

open Pointwise

namespace Tdaf.ConvexAnalysis

/-! ### Strict convexity under addition and under precomposition -/

section StrictConvexOps

variable {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]
  {f g : E → EReal} {C : Set E}

/-- **A strictly convex summand makes the sum strictly convex.** The other summand contributes its
own convexity inequality, which is not strict, and the two add.

Both functions must be finite on `C`: the strict inequality for `f` is vacuous where `f x = ⊤`,
while the one being proved for `f + g` is not. -/
theorem StrictConvexOnFn.add_convexFn (hC : Convex ℝ C) (hsc : StrictConvexOnFn f C)
    (hg : ConvexFn g) (hpf : Proper f) (hpg : Proper g) (hCf : C ⊆ dom f) (hCg : C ⊆ dom g) :
    StrictConvexOnFn (f + g) C := by
  intro x hx y hy hne a b ha hb hab
  have hz : a • x + b • y ∈ C := hC hx hy ha.le hb.le hab
  have hstrict := hsc hx hy hne ha hb hab
  have hconv := (convexFn_iff_le hpg.ne_bot).1 hg x y a b ha hb hab
  have hcf : ∀ ⦃z : E⦄, z ∈ C → f z = ((f z).toReal : EReal) := fun z hzC =>
    (_root_.EReal.coe_toReal (mem_dom.1 (hCf hzC)).ne (hpf.ne_bot z)).symm
  have hcg : ∀ ⦃z : E⦄, z ∈ C → g z = ((g z).toReal : EReal) := fun z hzC =>
    (_root_.EReal.coe_toReal (mem_dom.1 (hCg hzC)).ne (hpg.ne_bot z)).symm
  rw [hcf hx, hcf hy, hcf hz] at hstrict
  rw [hcg hx, hcg hy, hcg hz] at hconv
  rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, hcf hx, hcf hy, hcf hz, hcg hx, hcg hy, hcg hz]
  simp only [Tdaf.EReal.coe_mul_coe, ← _root_.EReal.coe_add, _root_.EReal.coe_lt_coe_iff,
    _root_.EReal.coe_le_coe_iff] at hstrict hconv ⊢
  linarith

/-- **Strict convexity pulls back along an injective linear map.** The image of two distinct points
is two distinct points, and the map carries convex combinations to convex combinations. -/
theorem StrictConvexOnFn.compLin {A : G →ₗ[ℝ] E} {D : Set G} (h : StrictConvexOnFn f (A '' D))
    (hinj : Function.Injective A) : StrictConvexOnFn (compLin f A) D := by
  intro x hx y hy hne a b ha hb hab
  have hlt := h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ (fun hc => hne (hinj hc)) ha hb hab
  simpa only [compLin_apply, map_add, map_smul] using hlt

end StrictConvexOps

/-! ### Corollary 26.3.2: infimal convolution -/

section InfConv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f₁ f₂ : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- **The conjugate-side content of Corollary 26.3.2**: if `g₁` is essentially strictly convex and
`g₁ + g₂` adds exactly, then `g₁ + g₂` is essentially strictly convex.

Theorem 23.8 puts `dom ∂(g₁ + g₂)` inside `dom ∂g₁`, so a convex subset of the former is one of the
latter, and `StrictConvexOnFn.add_convexFn` finishes. -/
theorem IsExactSum.essentiallyStrictlyConvex_add {g₁ g₂ : E → EReal}
    (h : IsExactSum (innerₗ E) g₁ g₂) (hg₂ : ConvexFn g₂)
    (hesc : EssentiallyStrictlyConvex (B := innerₗ E) g₁) :
    EssentiallyStrictlyConvex (B := innerₗ E) (g₁ + g₂) := by
  intro C hC hCsub
  have hCdom : C ⊆ dom (g₁ + g₂) := hCsub.trans (domSubgradient_subset_dom h.proper_add)
  rw [dom_add h.proper_left.ne_bot h.proper_right.ne_bot] at hCdom
  refine StrictConvexOnFn.add_convexFn hC (hesc hC fun z hz => ?_) hg₂ h.proper_left
    h.proper_right (fun z hz => (hCdom hz).1) fun z hz => (hCdom hz).2
  obtain ⟨v, hv⟩ := hCsub hz
  rw [h.subgradient_add z] at hv
  obtain ⟨v₁, hv₁, -, -, -⟩ := hv
  exact ⟨v₁, hv₁⟩

/-- **Rockafellar, Corollary 26.3.2**, against the D5 interface: if `f₁` is essentially smooth and
the conjugates `f₁*` and `f₂*` add exactly, then `f₁ □ f₂` is essentially smooth.

`f₁ □ f₂` is `(f₁* + f₂*)*` by Theorem 16.4, `f₁*` is essentially strictly convex by Theorem 26.3,
`f₁* + f₂*` inherits that by `IsExactSum.essentiallyStrictlyConvex_add`, and Theorem 26.3 read
backwards returns essential smoothness. -/
theorem IsExactSum.essentiallySmooth_infConv
    (h : IsExactSum (innerₗ E) (conj (innerₗ E) f₁) (conj (innerₗ E) f₂))
    (h₁ : ClosedProperConvexFn f₁) (h₂ : ClosedProperConvexFn f₂)
    (hes : EssentiallySmooth f₁) : EssentiallySmooth (infConv f₁ f₂) := by
  have hsum : ClosedProperConvexFn (conj (innerₗ E) f₁ + conj (innerₗ E) f₂) :=
    ClosedProperConvexFn.add ⟨convexFn_conj _ f₁, closedFn_conj, proper_conj h₁⟩
      ⟨convexFn_conj _ f₂, closedFn_conj, proper_conj h₂⟩ h.proper_add.dom_nonempty
  have hinf : conj (innerₗ E) (conj (innerₗ E) f₁ + conj (innerₗ E) f₂) = infConv f₁ f₂ := by
    rw [h.conj_add, conj_conj_innerL h₁.convex h₁.closed, conj_conj_innerL h₂.convex h₂.closed]
  rw [← hinf]
  refine (essentiallySmooth_conj_iff_essentiallyStrictlyConvex hsum.convex hsum.proper
    hsum.closed).2 (h.essentiallyStrictlyConvex_add (convexFn_conj _ f₂) ?_)
  exact (essentiallyStrictlyConvex_conj_iff_essentiallySmooth h₁.convex h₁.proper h₁.closed).2 hes

/-- **Rockafellar, Corollary 26.3.2**, with the book's hypothesis: a common relative interior point
of `dom f₁*` and `dom f₂*` supplies the exactness (`IsExactSum.of_relint`). -/
theorem essentiallySmooth_infConv_of_relint (h₁ : ClosedProperConvexFn f₁)
    (h₂ : ClosedProperConvexFn f₂) (hes : EssentiallySmooth f₁) {y₀ : E}
    (hy₁ : y₀ ∈ ri (dom (conj (innerₗ E) f₁))) (hy₂ : y₀ ∈ ri (dom (conj (innerₗ E) f₂))) :
    EssentiallySmooth (infConv f₁ f₂) :=
  IsExactSum.essentiallySmooth_infConv
    (IsExactSum.of_relint (convexFn_conj _ f₁) (proper_conj h₁) (convexFn_conj _ f₂)
      (proper_conj h₂) hy₁ hy₂) h₁ h₂ hes

end InfConv

/-! ### Corollary 26.3.3: linear images -/

section Image

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {f : E → EReal} {A : E →ₗ[ℝ] G} {A' : G →ₗ[ℝ] E}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- **An onto linear map has an injective transpose.** If `A' y = 0` then `⟪y, A x⟫ = 0` for every
`x`, hence `⟪y, ·⟫ = 0` on all of `G` by surjectivity, hence `y = 0`. -/
theorem injective_of_isAdjointPair_of_surjective (hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A)
    (hsurj : Function.Surjective A) : Function.Injective A' := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨x, hx⟩ := hsurj y
  have h := hA y x
  rw [LinearMap.mem_ker.1 hy, map_zero, LinearMap.zero_apply, hx] at h
  have h2 : ‖y‖ ^ 2 = 0 := by simpa using h.symm
  exact norm_eq_zero.1 (by nlinarith [norm_nonneg y])

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- **The conjugate-side content of Corollary 26.3.3**: if `g` is essentially strictly convex, `A'`
is injective and `g` pulls back exactly along `A'`, then `g A'` is essentially strictly convex.

Theorem 23.9 makes `dom ∂(g A')` the preimage of `dom ∂g`, so the image of a convex subset of it is
a convex subset of `dom ∂g`, on which `g` is strictly convex; `StrictConvexOnFn.compLin` pulls that
back. -/
theorem IsExactImage.essentiallyStrictlyConvex_compLin {g : E → EReal}
    {hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A}
    (h : IsExactImage (innerₗ G) (innerₗ E) A' A hA g) (hinj : Function.Injective A')
    (hesc : EssentiallyStrictlyConvex (B := innerₗ E) g) :
    EssentiallyStrictlyConvex (B := innerₗ G) (compLin g A') := by
  intro C hC hCsub
  refine StrictConvexOnFn.compLin (hesc (hC.linear_image A') fun z hz => ?_) hinj
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨v, hv⟩ := hCsub hy
  rw [h.subgradient_compLin y] at hv
  obtain ⟨w, hw, -⟩ := hv
  exact ⟨w, hw⟩

/-- **Rockafellar, Corollary 26.3.3**, against the D5 interface: if `f` is essentially smooth, `A'`
is injective, and `f*` pulls back exactly along `A'`, then the image `A f` is essentially smooth.

`A f` is `(f* A')*` by Theorem 16.3, `f*` is essentially strictly convex by Theorem 26.3, `f* A'`
inherits that by `IsExactImage.essentiallyStrictlyConvex_compLin`, and Theorem 26.3 read backwards
returns essential smoothness. -/
theorem IsExactImage.essentiallySmooth_mapLin {hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A}
    (h : IsExactImage (innerₗ G) (innerₗ E) A' A hA (conj (innerₗ E) f))
    (hf : ClosedProperConvexFn f) (hes : EssentiallySmooth f) (hinj : Function.Injective A') :
    EssentiallySmooth (mapLin A f) := by
  have hk : ClosedProperConvexFn (compLin (conj (innerₗ E) f) A') :=
    ⟨convexFn_compLin A' (convexFn_conj _ f),
      closedFn_compLin closedFn_conj A'.continuous_of_finiteDimensional, h.proper_compLin⟩
  have himg : conj (innerₗ G) (compLin (conj (innerₗ E) f) A') = mapLin A f := by
    rw [h.conj_compLin, conj_conj_innerL hf.convex hf.closed]
  rw [← himg]
  refine (essentiallySmooth_conj_iff_essentiallyStrictlyConvex hk.convex hk.proper hk.closed).2
    (h.essentiallyStrictlyConvex_compLin hinj ?_)
  exact (essentiallyStrictlyConvex_conj_iff_essentiallySmooth hf.convex hf.proper hf.closed).2 hes

/-- **Rockafellar, Corollary 26.3.3**, with the book's hypotheses: `A` onto and some `y₀` with
`A' y₀ ∈ ri (dom f*)`. The first gives injectivity of the transpose, the second the exactness
(`IsExactImage.of_relint`). -/
theorem essentiallySmooth_mapLin_of_relint (hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A)
    (hf : ClosedProperConvexFn f) (hes : EssentiallySmooth f) (hsurj : Function.Surjective A)
    {y₀ : G} (hy₀ : A' y₀ ∈ ri (dom (conj (innerₗ E) f))) :
    EssentiallySmooth (mapLin A f) :=
  IsExactImage.essentiallySmooth_mapLin
    (IsExactImage.of_relint hA ⟨convexFn_conj _ f, closedFn_conj, proper_conj hf⟩ hy₀) hf hes
    (injective_of_isAdjointPair_of_surjective hA hsurj)

end Image

end Tdaf.ConvexAnalysis
