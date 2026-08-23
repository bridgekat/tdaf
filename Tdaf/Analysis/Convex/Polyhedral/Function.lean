/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Polyhedral.Ops
import Tdaf.Analysis.Convex.Closure
import Tdaf.Analysis.Convex.Indicator
import Tdaf.Analysis.Convex.Operations.InfConv

/-!
# Polyhedral convex functions

Rockafellar's §19 for functions. A convex function is **polyhedral** when its epigraph is a
polyhedral convex set; equivalently — by Theorem 19.1 — when it is the pointwise maximum of
finitely many affine functions on a polyhedral effective domain.

Everything here is read off the epigraph through the polyhedral calculus of `Polyhedral/Ops.lean`:
the effective domain is a linear image of the epigraph, a sublevel set is an affine preimage of it,
and the indicator of a polyhedral set has a polyhedral "half-cylinder" epigraph.

## Main definitions

* `PolyhedralFn f` — `Polyhedral (epi f)`.

## Main results

* `PolyhedralFn.convexFn`, `PolyhedralFn.lowerSemicontinuous`, `PolyhedralFn.closedFn` — a
  polyhedral convex function is convex and closed.
* `PolyhedralFn.polyhedral_dom` — **Theorem 19.1** applied to the epigraph: `dom f` is polyhedral.
* `PolyhedralFn.polyhedral_sublevel` — every sublevel set is polyhedral.
* `polyhedralFn_indicatorFn` — the indicator of a polyhedral set is a polyhedral function; this is
  what makes the polyhedral constraint qualifications apply to constraint *sets*.
* `PolyhedralFn.add` — **Theorem 19.4**: a sum of polyhedral convex functions is polyhedral.
* `PolyhedralFn.infConv` and `epi_infConv_of_polyhedralFn` — **Corollary 19.3.4**: an infimal
  convolute of polyhedral convex functions is polyhedral, and the infimum defining it is attained.

## Design notes

**`ClosedFn` needs `f ≠ ⊥`.** `PolyhedralFn` does not by itself exclude `f x = ⊥`: the epigraph of
`f ≡ ⊥` is all of `E × ℝ`, which is polyhedral (the empty system). Lower semicontinuity holds
regardless — it is exactly closedness of the epigraph — but `ClosedFn`, being `clFn f = f`, has a
separate `⊥` branch, so `PolyhedralFn.closedFn` carries the hypothesis. Rockafellar's own
convention makes polyhedral convex functions proper, and every downstream use supplies properness.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §19.
-/

open Set
open scoped Pointwise

namespace Tdaf.ConvexAnalysis

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- A **polyhedral convex function**: one whose epigraph is a polyhedral convex set. -/
def PolyhedralFn (f : E → EReal) : Prop := Polyhedral (epi f)

omit [FiniteDimensional ℝ E] in
theorem PolyhedralFn.convexFn (hf : PolyhedralFn f) : ConvexFn f :=
  convexFn_iff_convex_epi.2 (Polyhedral.convex hf)

theorem PolyhedralFn.isClosed_epi (hf : PolyhedralFn f) : IsClosed (epi f) :=
  Polyhedral.isClosed hf

theorem PolyhedralFn.lowerSemicontinuous (hf : PolyhedralFn f) : LowerSemicontinuous f :=
  lowerSemicontinuous_iff_isClosed_epi.2 hf.isClosed_epi

theorem PolyhedralFn.closedFn (hf : PolyhedralFn f) (h : ∀ x, f x ≠ ⊥) : ClosedFn f :=
  (closedFn_iff_lowerSemicontinuous h).2 hf.lowerSemicontinuous

/-- **Theorem 19.1 for functions**: the effective domain of a polyhedral convex function is a
polyhedral convex set — it is the image of the epigraph under `Prod.fst`. -/
theorem PolyhedralFn.polyhedral_dom (hf : PolyhedralFn f) : Polyhedral (dom f) := by
  rw [dom_eq_fst_image_epi]
  exact Polyhedral.image hf (LinearMap.fst ℝ E ℝ)

omit [FiniteDimensional ℝ E] in
/-- Every sublevel set of a polyhedral convex function is polyhedral: it is the preimage of the
epigraph under the affine map `x ↦ (x, c)`. -/
theorem PolyhedralFn.polyhedral_sublevel (hf : PolyhedralFn f) (c : ℝ) :
    Polyhedral {x : E | f x ≤ (c : EReal)} := by
  have hpre : {x : E | f x ≤ (c : EReal)}
      = (fun x => LinearMap.inl ℝ E ℝ x + ((0 : E), c)) ⁻¹' epi f := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_epi]
    constructor
    · intro hx
      have hfst : (LinearMap.inl ℝ E ℝ x + ((0 : E), c)).1 = x := by simp
      have hsnd : (LinearMap.inl ℝ E ℝ x + ((0 : E), c)).2 = c := by simp
      rw [hfst, hsnd]
      exact hx
    · intro hx
      have hfst : (LinearMap.inl ℝ E ℝ x + ((0 : E), c)).1 = x := by simp
      have hsnd : (LinearMap.inl ℝ E ℝ x + ((0 : E), c)).2 = c := by simp
      rw [hfst, hsnd] at hx
      exact hx
  rw [hpre]
  exact Polyhedral.comap_affine hf _ _

omit [FiniteDimensional ℝ E] in
/-- **The indicator of a polyhedral convex set is a polyhedral convex function.** Its epigraph is
the half-cylinder `C ×ˢ [0, ∞)`, an intersection of the preimage of `C` with a half-space. -/
theorem polyhedralFn_indicatorFn {C : Set E} (hC : Polyhedral C) :
    PolyhedralFn (indicatorFn C) := by
  have hepi : epi (indicatorFn C)
      = (LinearMap.fst ℝ E ℝ) ⁻¹' C ∩ {p : E × ℝ | (-LinearMap.snd ℝ E ℝ) p ≤ 0} := by
    rw [epi_indicatorFn]
    ext p
    simp only [Set.mem_prod, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ici]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₁, by change -p.2 ≤ 0; linarith⟩
    · rintro ⟨h₁, h₂⟩
      have h₂' : -p.2 ≤ 0 := h₂
      exact ⟨h₁, by linarith⟩
  rw [PolyhedralFn, hepi]
  exact Polyhedral.inter (hC.comap _) (polyhedral_halfSpace _ _)

/-- The linear map `((x, α), (y, β)) ↦ (x, α + β)` used to build the epigraph of a sum. -/
def addEpiMap : ((E × ℝ) × (E × ℝ)) →ₗ[ℝ] E × ℝ where
  toFun p := (p.1.1, p.1.2 + p.2.2)
  map_add' p q := by
    refine Prod.ext rfl ?_
    change p.1.2 + q.1.2 + (p.2.2 + q.2.2) = p.1.2 + p.2.2 + (q.1.2 + q.2.2)
    ring
  map_smul' a p := by
    refine Prod.ext rfl ?_
    change a * p.1.2 + a * p.2.2 = a * (p.1.2 + p.2.2)
    ring

/-- The linear map `((x, α), (y, β)) ↦ x - y`, whose kernel is the "same first coordinate"
condition. -/
def diagMap : ((E × ℝ) × (E × ℝ)) →ₗ[ℝ] E where
  toFun p := p.1.1 - p.2.1
  map_add' p q := by
    change p.1.1 + q.1.1 - (p.2.1 + q.2.1) = p.1.1 - p.2.1 + (q.1.1 - q.2.1)
    abel
  map_smul' a p := by
    change a • p.1.1 - a • p.2.1 = a • (p.1.1 - p.2.1)
    rw [smul_sub]

/-- **Rockafellar, Theorem 19.4.** A sum of polyhedral convex functions is polyhedral.

The epigraph of the sum is the image, under `((x, α), (y, β)) ↦ (x, α + β)`, of the polyhedral set
`(epi f ×ˢ epi g) ∩ ker (x, y) ↦ x - y`. The `⊥`-freeness hypotheses are what make the splitting
`f x + g x ≤ μ ↔ ∃ α β, f x ≤ α ∧ g x ≤ β ∧ α + β = μ` correct in `EReal`. -/
theorem PolyhedralFn.add {g : E → EReal} (hf : PolyhedralFn f) (hg : PolyhedralFn g)
    (hf' : ∀ x, f x ≠ ⊥) (hg' : ∀ x, g x ≠ ⊥) : PolyhedralFn (f + g) := by
  have hS : Polyhedral (((epi f) ×ˢ (epi g)) ∩ (diagMap ⁻¹' ({0} : Set E))) :=
    Polyhedral.inter (Polyhedral.prod hf hg) (Polyhedral.comap polyhedral_zero _)
  have himg : epi (f + g) = (addEpiMap : ((E × ℝ) × (E × ℝ)) →ₗ[ℝ] E × ℝ) ''
      (((epi f) ×ˢ (epi g)) ∩ (diagMap ⁻¹' ({0} : Set E))) := by
    ext p
    constructor
    · intro hp
      have hle : f p.1 + g p.1 ≤ ((p.2 : ℝ) : EReal) := hp
      have hftop : f p.1 ≠ ⊤ := by
        intro h
        rw [h, EReal.top_add_of_ne_bot (hg' p.1)] at hle
        exact absurd hle (not_le.2 (EReal.coe_lt_top p.2))
      have hgtop : g p.1 ≠ ⊤ := by
        intro h
        rw [h, EReal.add_top_of_ne_bot (hf' p.1)] at hle
        exact absurd hle (not_le.2 (EReal.coe_lt_top p.2))
      obtain ⟨a, ha⟩ :=
        Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf' p.1) (lt_top_iff_ne_top.2 hftop)
      obtain ⟨b, hb⟩ :=
        Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hg' p.1) (lt_top_iff_ne_top.2 hgtop)
      rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
      refine ⟨((p.1, a), (p.1, p.2 - a)), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · change f p.1 ≤ ((a : ℝ) : EReal)
        rw [ha]
      · change g p.1 ≤ ((p.2 - a : ℝ) : EReal)
        rw [hb, EReal.coe_le_coe_iff]
        linarith
      · change p.1 - p.1 ∈ ({0} : Set E)
        rw [sub_self]
        rfl
      · refine Prod.ext rfl ?_
        change a + (p.2 - a) = p.2
        ring
    · rintro ⟨q, ⟨⟨hq₁, hq₂⟩, hq₃⟩, rfl⟩
      have hdiag : q.1.1 = q.2.1 := by
        have : q.1.1 - q.2.1 ∈ ({0} : Set E) := hq₃
        rw [Set.mem_singleton_iff, sub_eq_zero] at this
        exact this
      have h₁ : f q.1.1 ≤ ((q.1.2 : ℝ) : EReal) := hq₁
      have h₂ : g q.2.1 ≤ ((q.2.2 : ℝ) : EReal) := hq₂
      rw [← hdiag] at h₂
      change f q.1.1 + g q.1.1 ≤ ((q.1.2 + q.2.2 : ℝ) : EReal)
      rw [EReal.coe_add]
      exact add_le_add h₁ h₂
  rw [PolyhedralFn, himg]
  exact Polyhedral.image hS _

/-- **Rockafellar, Corollary 19.3.4**, the attainment half: for polyhedral `f` and `g` the sum of
the epigraphs *is* the epigraph of the infimal convolute, so the infimum defining `(f □ g) x` is
attained whenever it is finite.

The sum of two epigraphs is always upward closed in the vertical direction
(`mem_epi_add_epi_of_le`) and here it is also closed, being polyhedral; those are exactly the two
halves of `IsEpiLike`. -/
theorem epi_infConv_of_polyhedralFn (hf : PolyhedralFn f) {g : E → EReal} (hg : PolyhedralFn g) :
    epi (infConv f g) = epi f + epi g :=
  epi_infConv (IsEpiLike.of_isClosed (fun _ _ _ h hle => mem_epi_add_epi_of_le h hle)
    (Polyhedral.isClosed (Polyhedral.add hf hg)))

/-- **Rockafellar, Corollary 19.3.4.** An infimal convolute of polyhedral convex functions is
polyhedral: its epigraph is the sum of the two epigraphs. -/
theorem PolyhedralFn.infConv (hf : PolyhedralFn f) {g : E → EReal} (hg : PolyhedralFn g) :
    PolyhedralFn (_root_.Tdaf.ConvexAnalysis.infConv f g) := by
  have h : Polyhedral (epi (_root_.Tdaf.ConvexAnalysis.infConv f g)) := by
    rw [epi_infConv_of_polyhedralFn hf hg]
    exact Polyhedral.add hf hg
  exact h

end Defs

end Tdaf.ConvexAnalysis
