/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Polar
import Tdaf.Analysis.Convex.Duality.Support
import Tdaf.Analysis.Convex.Recession.ConeHull
import Tdaf.Analysis.Convex.Recession.Function

/-!
# Recession functions, conjugates and polar cones

Two dual dictionaries between a function's recession data and its conjugate's effective domain.
The first is at the level of functions: the recession function of a conjugate is the support
function of the effective domain. The second is at the level of cones: the recession *cone* of a
conjugate is the *polar* of the effective domain, which is the level `0` of the first.

`Duality/Support.lean` deliberately leaves §13.3–§13.5 unstated — it cannot name `f 0⁺`, which
lives in `Recession/Function.lean`. This file is the join of those two together with
`Duality/Polar.lean`, and it is where the statements that need both belong.

## Main results

* `recessionFn_conj_le_supportFn_dom` — the unconditional half.
* `recessionFn_conj` — **Theorem 13.3**. Its dual form, `f 0⁺ = δ*(· | dom f*)`, is
  `recessionFn_eq_supportFn_dom_conj` in `Duality/Level.lean`, where Corollary 13.3.1 needs it.
* `constancySpace_conj` — the constancy space of `f*` is the annihilator of `dom f`. This is the
  form Theorems 9.2 and 16.3 consume: it turns "`f*` is constant along `z`" into "`z` annihilates
  `dom f`", which a relative-interior hypothesis can discharge.
* `recessionConeFn_conj`, `recessionConeFn_conj_hull`,
  `recessionConeFn_eq_polarCone_dom_conj`, `polarCone_recessionConeFn` — **Theorem 14.2**, both
  assertions, each in the direct form and in the book's cone-generated phrasing.
* `zero_mem_interior_iff_polarCone_eq_zero`, `isBounded_setOf_le_iff_zero_mem_interior_dom_conj` —
  **Corollary 14.2.2**, and the interior/polar dictionary it runs on.

## Design notes

**One direction is free, the other needs Theorem 12.2.** `(f*)0⁺ y ≤ ν` unfolds, through
`recessionFn_le_coe_iff` and `mk_mem_recessionCone_epi_iff`, to `f*(z + a • y) ≤ f* z + a ν` for
all `z` and `a ≥ 0`, and `δ*(y | dom f) ≤ ν` unfolds to `⟨x, y⟩ ≤ ν` for all `x ∈ dom f`. Bounding
the supremum that defines `f*` termwise gives `(f*)0⁺ ≤ δ*(· | dom f)` with no hypothesis at all.

The reverse needs a `z` at which `f*` is *finite*: only then can the resulting inequality
`⟨x, z⟩ + a⟨x, y⟩ - f x ≤ f* z + a ν` be pushed to `a → ∞` to give `⟨x, y⟩ ≤ ν`. That is why the
hypothesis is `Proper (conj B f)`, which `proper_conj` supplies for closed proper convex `f` — i.e.
exactly Theorem 12.2.

**The file is layer A up to Theorem 13.3.** Neither half of that theorem needs a topology:
properness of `f*` is taken as a hypothesis rather than derived, so callers at layer C supply it
from `proper_conj` and everyone else can still use the statement. Theorem 14.2's first assertion
is layer A for the same reason; its second assertion needs Fenchel–Moreau and the bipolar theorem,
and Corollary 14.2.2 needs finite dimension on both sides.

**Theorem 14.2 is stated against `dom f`, not against the cone it generates.** That is the form the
proof produces — `(f*)0⁺ y ≤ 0` says `⟨x, y⟩ ≤ 0` for every `x ∈ dom f` — and the form Theorem
27.1(f) consumes; `polarCone_hull` (`Duality/Polar.lean`) recovers the book's phrasing, since a
polar cone cannot tell a set from the cone it generates.

**Corollary 14.2.2 factors through a dictionary that has nothing to do with conjugates.**
`zero_mem_interior_iff_polarCone_eq_zero` says that a nonempty convex set has the origin in its
interior exactly when its polar cone is trivial; Corollary 14.2.2 is that fact composed with
Theorems 14.2, 8.7 and 8.4. Nonemptiness is genuinely needed — for `D = ∅` between two trivial
spaces the polar is `{0}` while the interior is empty.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §13 (Theorem 13.3,
  Corollary 13.3.4) and §14 (Theorem 14.2, Corollary 14.2.2).
-/

open scoped Pointwise

namespace Tdaf.ConvexAnalysis

section Thm133

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **Theorem 13.3**, the unconditional half: `(f*) 0⁺ ≤ δ*(· | dom f)`.

Bounding the supremum that defines `f*` termwise: off `dom f` the term is `⊥`, and on `dom f` the
bound `⟨x, y⟩ ≤ ν` moves `a⟨x, y⟩` past the supremum. -/
theorem recessionFn_conj_le_supportFn_dom (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    recessionFn (conj B f) ≤ supportFn B (dom f) := by
  intro y
  refine Tdaf.EReal.le_of_forall_coe_le fun ν hν => ?_
  rw [supportFn_le_coe_iff] at hν
  rw [recessionFn_le_coe_iff, mk_mem_recessionCone_epi_iff]
  intro z a ha
  rw [conj_apply]
  refine iSup_le fun x => ?_
  by_cases hx : x ∈ dom f
  · have hBx : B x (z + a • y) = B x z + a * B x y := by rw [map_add, map_smul, smul_eq_mul]
    have hmul : a * B x y ≤ a * ν := mul_le_mul_of_nonneg_left (hν x hx) ha
    have hle : B x (z + a • y) ≤ B x z + a * ν := by rw [hBx]; linarith
    calc ((B x (z + a • y) : ℝ) : EReal) - f x
        ≤ ((B x z + a * ν : ℝ) : EReal) - f x :=
          _root_.EReal.sub_le_sub (_root_.EReal.coe_le_coe_iff.2 hle) le_rfl
      _ = (((B x z : ℝ) : EReal) - f x) + ((a * ν : ℝ) : EReal) :=
          Tdaf.EReal.coe_add_sub _ _ _
      _ ≤ conj B f z + ((a * ν : ℝ) : EReal) :=
          add_le_add (sub_le_conj B f x z) le_rfl
  · rw [mem_dom, not_lt, top_le_iff] at hx
    rw [hx, _root_.EReal.sub_top]
    exact bot_le

/-- **Theorem 13.3**, the half that needs Theorem 12.2: `δ*(· | dom f) ≤ (f*) 0⁺`.

`Proper (conj B f)` supplies a `z` at which `f*` is finite; Fenchel's inequality at `z + a • y`
then reads `⟨x, z⟩ + a⟨x, y⟩ - f x ≤ f* z + a ν`, and letting `a → ∞` forces `⟨x, y⟩ ≤ ν`. -/
theorem supportFn_dom_le_recessionFn_conj (hp : Proper f) (hc : Proper (conj B f)) :
    supportFn B (dom f) ≤ recessionFn (conj B f) := by
  intro y
  refine Tdaf.EReal.le_of_forall_coe_le fun ν hν => ?_
  rw [supportFn_le_coe_iff]
  intro x hx
  obtain ⟨z, hz⟩ := hc.dom_nonempty
  obtain ⟨c, hcz⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hc.ne_bot z) hz
  obtain ⟨r, hrx⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
  have hrec : ∀ a : ℝ, 0 ≤ a → conj B f (z + a • y) ≤ conj B f z + ((a * ν : ℝ) : EReal) :=
    fun a ha => mk_mem_recessionCone_epi_iff.1 (recessionFn_le_coe_iff.1 hν) z a ha
  have hbound : ∀ a : ℝ, 0 ≤ a → B x z + a * B x y - r ≤ c + a * ν := by
    intro a ha
    have hsub := sub_le_conj B f x (z + a • y)
    rw [hrx] at hsub
    have hle := hsub.trans (hrec a ha)
    rw [hcz, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at hle
    have hBx : B x (z + a • y) = B x z + a * B x y := by rw [map_add, map_smul, smul_eq_mul]
    rw [hBx] at hle
    linarith
  by_contra hcon
  push Not at hcon
  have hd : 0 < B x y - ν := by linarith
  set q : ℝ := (c + r - B x z) / (B x y - ν) with hq
  set a : ℝ := max (q + 1) 0 with ha
  have ha0 : 0 ≤ a := le_max_right _ _
  have haq : q < a := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hqmul : q * (B x y - ν) = c + r - B x z := by rw [hq, div_mul_cancel₀ _ hd.ne']
  have hb := hbound a ha0
  have hexp : a * (B x y - ν) = a * B x y - a * ν := by ring
  have hstep : a * (B x y - ν) ≤ q * (B x y - ν) := by rw [hqmul, hexp]; linarith
  exact absurd (le_of_mul_le_mul_right hstep hd) (not_le.2 haq)

/-- **Rockafellar, Theorem 13.3**: the recession function of a conjugate is the support function of
the effective domain, `(f*) 0⁺ = δ*(· | dom f)`. -/
theorem recessionFn_conj (hp : Proper f) (hc : Proper (conj B f)) :
    recessionFn (conj B f) = supportFn B (dom f) :=
  le_antisymm (recessionFn_conj_le_supportFn_dom B f) (supportFn_dom_le_recessionFn_conj hp hc)

/-- **The constancy space of a conjugate is the annihilator of the effective domain.**

This is what Theorem 9.2's hypothesis becomes when it is applied to `f*`: "`f*` is constant along
`y`" says exactly that `y` pairs to zero with every point of `dom f`. -/
theorem constancySpace_conj (hp : Proper f) (hc : Proper (conj B f)) :
    constancySpace (conj B f) = {y : F | ∀ x ∈ dom f, B x y = 0} := by
  ext y
  rw [mem_constancySpace, recessionFn_conj hp hc, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [supportFn_le_zero_iff] at h₁ h₂
    intro x hx
    have hneg := h₂ x hx
    rw [map_neg] at hneg
    linarith [h₁ x hx]
  · intro h
    constructor <;> rw [supportFn_le_zero_iff] <;> intro x hx
    · exact le_of_eq (h x hx)
    · rw [map_neg, h x hx, neg_zero]

end Thm133

/-! ### Recession cones and polars of effective domains -/

section RecessionPolar

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **Rockafellar, Theorem 14.2**, first assertion: the recession cone of a conjugate is the polar
of the effective domain.

Stated against `dom f` rather than the cone it generates — that is the form the proof produces and
the form consumers use; `recessionConeFn_conj_hull` is the book's phrasing, and the two agree
because a polar cone sees only the cone a set generates. The proof is Theorem 13.3 read at the
level `0`: `(f*)0⁺ y ≤ 0` says `⟨x, y⟩ ≤ 0` for every `x ∈ dom f`. -/
theorem recessionConeFn_conj (hp : Proper f) (hc : Proper (conj B f)) :
    recessionConeFn (conj B f) = polarCone B (dom f) := by
  ext y
  rw [mem_recessionConeFn, recessionFn_conj hp hc, supportFn_le_zero_iff]
  exact Iff.rfl

/-- **Rockafellar, Theorem 14.2**, first assertion in the book's phrasing: the polar of the convex
cone generated by `dom f` is the recession cone of `f*`. -/
theorem recessionConeFn_conj_hull (hp : Proper f) (hc : Proper (conj B f)) :
    polarCone B (PointedCone.hull ℝ (dom f) : Set E) = recessionConeFn (conj B f) := by
  rw [polarCone_hull, recessionConeFn_conj hp hc]

end RecessionPolar

section RecessionPolarDual

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- **Rockafellar, Theorem 14.2**, second assertion, before polars are taken: the recession cone of
a closed proper convex function is the polar of the effective domain of its conjugate.

This is the first assertion applied to `f*`, using `f** = f`. It is the form Theorem 27.1(f)
consumes. -/
theorem recessionConeFn_eq_polarCone_dom_conj (hf : ConvexFn f) (hcl : ClosedFn f) (hp : Proper f) :
    recessionConeFn f = polarCone B.flip (dom (conj B f)) := by
  have hbi : biconj B f = f := biconj_eq_self hf hcl
  have h := recessionConeFn_conj (B := B.flip) (f := conj B f) (proper_conj ⟨hf, hcl, hp⟩)
    (by rw [show conj B.flip (conj B f) = f from hbi]; exact hp)
  rwa [show conj B.flip (conj B f) = f from hbi] at h

end RecessionPolarDual

section RecessionPolarBipolar

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {f : E → EReal}

/-- **Rockafellar, Theorem 14.2**, second assertion: the polar of the recession cone of a closed
proper convex function is the closure of the convex cone generated by `dom f*`.

Taking polars in `recessionConeFn_eq_polarCone_dom_conj` and applying the bipolar theorem to the
cone generated by `dom f*`. -/
theorem polarCone_recessionConeFn (hf : ConvexFn f) (hcl : ClosedFn f) (hp : Proper f) :
    polarCone B (recessionConeFn f)
      = closure (PointedCone.hull ℝ (dom (conj B f)) : Set F) := by
  set K : PointedCone ℝ F := PointedCone.hull ℝ (dom (conj B f)) with hK
  rw [recessionConeFn_eq_polarCone_dom_conj (B := B) hf hcl hp, ← polarCone_hull B.flip,
    ← hK]
  exact polarCone_polarCone (B := B.flip) (K : ConvexCone ℝ F).convex
    (smul_coe_pointedCone K) ⟨0, K.zero_mem⟩

end RecessionPolarBipolar

/-! ### Layer D: bounded level sets -/

section BoundedLevel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip]

omit [FiniteDimensional ℝ E] in
/-- **The origin is interior to a convex set exactly when its polar cone is trivial.**

Both directions run on Corollary 6.4.1. Forwards, absorbency at the origin makes every value of
the pairing vanish, and the pairing separates points. Backwards, the bipolar theorem turns a
trivial polar into "the cone generated by `D` is dense", Theorem 6.3 upgrades dense to everything,
and that is absorbency again.

Nonemptiness is not decorative: for `D = ∅` between two trivial spaces the polar is `{0}` while the
interior is empty. -/
theorem zero_mem_interior_iff_polarCone_eq_zero {D : Set F} (hD : Convex ℝ D) (hne : D.Nonempty) :
    (0 : F) ∈ interior D ↔ polarCone B.flip D = {(0 : E)} := by
  have hconv : Convex ℝ ((PointedCone.hull ℝ D : PointedCone ℝ F) : Set F) :=
    ((PointedCone.hull ℝ D : PointedCone ℝ F) : ConvexCone ℝ F).convex
  constructor
  · intro hint
    have habs := (Convex.mem_interior_iff_absorbs hD).1 hint
    refine subset_antisymm (fun x hx => ?_) ?_
    · have key : ∀ w : F, B x w ≤ 0 := by
        intro w
        obtain ⟨ε, hε, hmem⟩ := habs w
        have hx' := hx _ (show ε • w ∈ D by simpa using hmem)
        rw [LinearMap.flip_apply, map_smul, smul_eq_mul] at hx'
        nlinarith
      have hall : ∀ y : F, B x y = 0 := by
        intro y
        have h1 := key y
        have h2 := key (-y)
        rw [map_neg] at h2
        linarith
      have hx0 : x = 0 := SeparatingDual.eq_zero_of_forall_dual_eq_zero fun g => by
        obtain ⟨y, hy⟩ := exists_pairing_eq B g
        rw [hy x]
        exact hall y
      simpa using hx0
    · rintro x rfl
      intro y _
      simp
  · intro hpol
    have hbip : closure ((PointedCone.hull ℝ D : PointedCone ℝ F) : Set F) = Set.univ := by
      have h := polarCone_polarCone (B := B.flip)
        (K := ((PointedCone.hull ℝ D : PointedCone ℝ F) : Set F))
        hconv (smul_coe_pointedCone _) ⟨0, Submodule.zero_mem _⟩
      rw [polarCone_hull, hpol] at h
      rw [← h]
      ext x'
      simp [polarCone]
    have hfull : ((PointedCone.hull ℝ D : PointedCone ℝ F) : Set F) = Set.univ := by
      have hri : ri ((PointedCone.hull ℝ D : PointedCone ℝ F) : Set F) = Set.univ := by
        rw [← Convex.relint_closure hconv, hbip,
          intrinsicInterior_eq_interior (s := (Set.univ : Set F)) (by simp), interior_univ]
      exact subset_antisymm (Set.subset_univ _) (hri ▸ intrinsicInterior_subset)
    have hmemhull : ∀ y : F, y = 0 ∨ ∃ t : ℝ, 0 < t ∧ y ∈ t • D := fun y =>
      (mem_coe_hull_iff_of_convex hD).1 (hfull ▸ Set.mem_univ y)
    have hzero : (0 : F) ∈ D := by
      obtain ⟨d, hd⟩ := hne
      rcases hmemhull (-d) with h0 | ⟨t, ht, e, he, hed⟩
      · rwa [show d = 0 from by simpa using congrArg Neg.neg h0] at hd
      · have hcomb := hD hd he (by positivity : (0 : ℝ) ≤ 1 / (1 + t))
          (by positivity : (0 : ℝ) ≤ t / (1 + t)) (by field_simp)
        have hval : (1 / (1 + t)) • d + (t / (1 + t)) • e = (0 : F) := by
          have h1 : (t / (1 + t)) • e = (1 / (1 + t)) • (t • e) := by
            rw [smul_smul]
            congr 1
            field_simp
          have hed' : t • e = -d := hed
          rw [h1, hed', smul_neg, add_neg_cancel]
        rwa [hval] at hcomb
    rw [Convex.mem_interior_iff_absorbs hD]
    intro y
    rcases hmemhull y with rfl | ⟨t, ht, e, he, hey⟩
    · exact ⟨1, one_pos, by simpa using hzero⟩
    · refine ⟨t⁻¹, by positivity, ?_⟩
      have hey' : t • e = y := hey
      rw [zero_add, ← hey', smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      exact he

/-- **Rockafellar, Corollary 14.2.2**: every level set of a closed proper convex function is
bounded exactly when the origin is interior to the effective domain of the conjugate.

Theorem 14.2 turns the recession cone of `f` into the polar of `dom f*`, Theorem 8.7 says every
nonempty level set has that same recession cone, and Theorem 8.4 turns "trivial recession cone"
into "bounded". -/
theorem isBounded_setOf_le_iff_zero_mem_interior_dom_conj {f : E → EReal}
    (hf : ConvexFn f) (hcl : ClosedFn f) (hp : Proper f) :
    (∀ α : ℝ, Bornology.IsBounded {z : E | f z ≤ (α : EReal)})
      ↔ (0 : F) ∈ interior (dom (conj B f)) := by
  have hpc : Proper (conj B f) := proper_conj ⟨hf, hcl, hp⟩
  have hepi : IsClosed (epi f) := ClosedProperConvexFn.isClosed_epi ⟨hf, hcl, hp⟩
  have hlev : ∀ α : ℝ, IsClosed {z : E | f z ≤ (α : EReal)} := fun α =>
    lowerSemicontinuous_iff_isClosed_le.1 (lowerSemicontinuous_iff_isClosed_epi.2 hepi) α
  rw [zero_mem_interior_iff_polarCone_eq_zero (B := B) (convexFn_conj B f).convex_dom
      hpc.dom_nonempty,
    ← recessionConeFn_eq_polarCone_dom_conj (B := B) hf hcl hp]
  constructor
  · intro hbd
    obtain ⟨x, hx⟩ := hp.dom_nonempty
    obtain ⟨α, hα⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
    have hlevne : {z : E | f z ≤ (α : EReal)}.Nonempty := ⟨x, le_of_eq hα⟩
    rw [← recessionCone_setOf_le hf hepi hlevne]
    exact (isBounded_iff_recessionCone_eq_zero (hf.convex_le _) (hlev α) hlevne).1 (hbd α)
  · intro hrec α
    rcases Set.eq_empty_or_nonempty {z : E | f z ≤ (α : EReal)} with hem | hlevne
    · rw [hem]
      exact Bornology.isBounded_empty
    · refine (isBounded_iff_recessionCone_eq_zero (hf.convex_le _) (hlev α) hlevne).2 ?_
      rw [recessionCone_setOf_le hf hepi hlevne]
      exact hrec

end BoundedLevel

end Tdaf.ConvexAnalysis
