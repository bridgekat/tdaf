/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Gauge

/-!
# Monotone conjugacy on the half-line, and gauge-like convex functions

Two correspondences that fit together. The first is conjugacy for nondecreasing convex functions
of one nonnegative variable: on that class the ordinary conjugate, cut back to the half-line, is
again such a function, and the operation is an involution. The second builds an involution on the
convex functions of many variables whose sublevel sets are all dilates of one another, by
composing a closed gauge with a function of the first kind.

## Main definitions

* `MonotoneHalfLineFn g` — `g : ℝ → EReal` is `+∞` on the negative axis, nondecreasing on the
  half-line, convex, closed, and finite at the origin.
* `monotoneConj g` — the **monotone conjugate** `g⁺(s) = sup {t s - g t ∣ t ≥ 0}`, itself taken to
  be `+∞` for `s < 0`.

## Main results

* `monotoneHalfLineFn_monotoneConj` — the class is stable under `monotoneConj`.
* `monotoneConj_monotoneConj` — `g⁺⁺ = g`.

## References

Rockafellar, *Convex Analysis*, Theorem 12.4 and Theorem 15.3 with its corollaries.
-/

open scoped Pointwise

namespace Tdaf.ConvexAnalysis

/-! ### Restriction to a closed set

`ConvexFn.restrict` has no closedness companion yet; this is it. Both belong together in
`Operations/Basic.lean`. -/

section RestrictClosed

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- Cutting a closed function down to a closed set leaves it closed. -/
theorem ClosedFn.restrict {f : E → EReal} {s : Set E} (hf : ClosedFn f) (hne : ∀ x, f x ≠ ⊥)
    (hs : IsClosed s) : ClosedFn (ConvexAnalysis.restrict s f) := by
  have hne' : ∀ x, ConvexAnalysis.restrict s f x ≠ ⊥ := fun x => by
    by_cases hx : x ∈ s
    · rw [restrict_of_mem hx]; exact hne x
    · rw [restrict_of_notMem hx]; exact top_ne_bot
  have hepi : IsClosed (epi f) := lowerSemicontinuous_iff_isClosed_epi.1 hf.lowerSemicontinuous
  refine (closedFn_iff_lowerSemicontinuous hne').2 ?_
  rw [lowerSemicontinuous_iff_isClosed_epi, epi_restrict]
  exact hepi.inter (hs.prod isClosed_univ)

end RestrictClosed

/-! ### The self-pairing of the line, flipped

`mulPairing` is its own flip, but only propositionally, so the instances of `Duality/Conjugate.lean`
that mention `B.flip` — closedness of the conjugate, and the whole of Fenchel–Moreau — need the
flipped copy to be found by instance search as well. Both instances belong beside `mulPairing`. -/

instance : IsContinuousPairing mulPairing.flip := by rw [mulPairing_flip]; infer_instance

instance : IsCompatiblePairing mulPairing.flip := by rw [mulPairing_flip]; infer_instance

/-! ### Nondecreasing convex functions on the half-line -/

section MonotoneHalfLine

variable {g : ℝ → EReal} {s t : ℝ}

/-- A **nondecreasing closed convex function on the half-line**: `+∞` on the negative axis,
nondecreasing on `[0, ∞)`, convex, closed, and finite at the origin.

Convexity and closedness are asked of `g` as a function on all of `ℝ`; because `g` is `+∞` to the
left of the origin, that is the same as asking them on the half-line. This is exactly the class on
which monotone conjugacy is an involution — **Rockafellar, Theorem 12.4**, in one dimension. -/
structure MonotoneHalfLineFn (g : ℝ → EReal) : Prop where
  /-- `g` is `+∞` to the left of the origin. -/
  top_of_neg : ∀ ⦃t : ℝ⦄, t < 0 → g t = ⊤
  /-- `g` is nondecreasing on the half-line. -/
  monotoneOn : MonotoneOn g (Set.Ici 0)
  /-- `g` is convex. -/
  convex : ConvexFn g
  /-- `g` is closed. -/
  closed : ClosedFn g
  /-- `g` is finite at the origin. -/
  zero_ne_top : g 0 ≠ ⊤

namespace MonotoneHalfLineFn

/-- A function of this class never takes the value `-∞`: it is `+∞` somewhere, so the exceptional
branch of `clFn` is excluded. -/
theorem ne_bot (hg : MonotoneHalfLineFn g) (t : ℝ) : g t ≠ ⊥ := by
  by_cases hb : ∃ x, lscHull g x = ⊥
  · have h : clFn g = g := hg.closed
    rw [clFn_of_exists_eq_bot hb] at h
    have hcon : (⊤ : EReal) = ⊥ := by
      rw [← hg.top_of_neg (t := -1) (by norm_num), ← h]
    exact absurd hcon top_ne_bot
  · push Not at hb
    exact fun hbt => hb t (le_bot_iff.1 (hbt ▸ lscHull_le g t))

/-- The infimum of `g` is attained at the origin. -/
theorem iInf_eq_zero (hg : MonotoneHalfLineFn g) : ⨅ t : ℝ, g t = g 0 :=
  le_antisymm (iInf_le _ 0) <| le_iInf fun t => by
    rcases le_or_gt 0 t with ht | ht
    · exact hg.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
    · rw [hg.top_of_neg ht]; exact le_top

/-- `g 0` is the least value of `g`. -/
theorem zero_le (hg : MonotoneHalfLineFn g) (t : ℝ) : g 0 ≤ g t :=
  hg.iInf_eq_zero ▸ iInf_le _ t

/-- A function of this class is proper. -/
theorem proper (hg : MonotoneHalfLineFn g) : Proper g :=
  ⟨⟨0, lt_top_iff_ne_top.2 hg.zero_ne_top⟩, hg.ne_bot⟩

end MonotoneHalfLineFn

/-! ### The monotone conjugate -/

/-- The **monotone conjugate** `g⁺(s) = sup {t s - g t ∣ t ≥ 0}` of a function on the half-line.
Like `g` itself it is taken to be `+∞` to the left of the origin, which is what makes the
operation an involution rather than a bijection onto a smaller class. -/
noncomputable def monotoneConj (g : ℝ → EReal) : ℝ → EReal :=
  ConvexAnalysis.restrict (Set.Ici 0) fun s =>
    ⨆ t : ℝ, ⨆ _ : (0 : ℝ) ≤ t, ((t * s : ℝ) : EReal) - g t

theorem monotoneConj_of_nonneg (g : ℝ → EReal) (hs : 0 ≤ s) :
    monotoneConj g s = ⨆ t : ℝ, ⨆ _ : (0 : ℝ) ≤ t, ((t * s : ℝ) : EReal) - g t :=
  restrict_of_mem hs

theorem monotoneConj_of_neg (g : ℝ → EReal) (hs : s < 0) : monotoneConj g s = ⊤ :=
  restrict_of_notMem (by simpa using hs)

/-- On a function that is `+∞` to the left of the origin, the supremum over the half-line and the
supremum over the whole line agree, so the monotone conjugate is the ordinary conjugate for
`mulPairing`, cut back to the half-line. -/
theorem conj_mulPairing_apply (hg : ∀ ⦃t : ℝ⦄, t < 0 → g t = ⊤) (s : ℝ) :
    conj mulPairing g s = ⨆ t : ℝ, ⨆ _ : (0 : ℝ) ≤ t, ((t * s : ℝ) : EReal) - g t := by
  rw [conj_apply]
  refine le_antisymm (iSup_le fun t => ?_) (iSup_le fun t => iSup_le fun ht => ?_)
  · rcases le_or_gt 0 t with ht | ht
    · exact le_trans (le_iSup (fun _ : (0 : ℝ) ≤ t => ((t * s : ℝ) : EReal) - g t) ht)
        (le_iSup (fun t : ℝ => ⨆ _ : (0 : ℝ) ≤ t, ((t * s : ℝ) : EReal) - g t) t)
    · rw [mulPairing_apply, hg ht, EReal.sub_top]; exact bot_le
  · exact le_iSup (fun t : ℝ => ((mulPairing t s : ℝ) : EReal) - g t) t

/-- The monotone conjugate as a restricted ordinary conjugate. -/
theorem monotoneConj_eq_restrict_conj (hg : ∀ ⦃t : ℝ⦄, t < 0 → g t = ⊤) :
    monotoneConj g = ConvexAnalysis.restrict (Set.Ici 0) (conj mulPairing g) := by
  rw [monotoneConj, funext fun s => (conj_mulPairing_apply hg s).symm]

/-- On the half-line the monotone conjugate and the ordinary conjugate agree. -/
theorem monotoneConj_of_nonneg' (hg : ∀ ⦃t : ℝ⦄, t < 0 → g t = ⊤) (hs : 0 ≤ s) :
    monotoneConj g s = conj mulPairing g s := by
  rw [monotoneConj_eq_restrict_conj hg, restrict_of_mem (Set.mem_Ici.2 hs)]

/-- The monotone conjugate dominates the ordinary one, being `+∞` where they differ. -/
theorem conj_le_monotoneConj (hg : ∀ ⦃t : ℝ⦄, t < 0 → g t = ⊤) (s : ℝ) :
    conj mulPairing g s ≤ monotoneConj g s := by
  rcases le_or_gt 0 s with hs | hs
  · exact (monotoneConj_of_nonneg' hg hs).ge
  · rw [monotoneConj_of_neg _ hs]; exact le_top

/-- The ordinary conjugate of a function that is `+∞` to the left of the origin is nondecreasing:
only nonnegative arguments contribute to the supremum. -/
theorem monotone_conj_mulPairing (hg : ∀ ⦃t : ℝ⦄, t < 0 → g t = ⊤) :
    Monotone (conj mulPairing g) := by
  intro s s' hss
  rw [conj_mulPairing_apply hg, conj_mulPairing_apply hg]
  refine iSup_le fun t => iSup_le fun ht => le_trans ?_
    (le_trans (le_iSup (fun _ : (0 : ℝ) ≤ t => ((t * s' : ℝ) : EReal) - g t) ht)
      (le_iSup (fun t : ℝ => ⨆ _ : (0 : ℝ) ≤ t, ((t * s' : ℝ) : EReal) - g t) t))
  exact EReal.sub_le_sub (by exact_mod_cast mul_le_mul_of_nonneg_left hss ht) le_rfl

/-- The conjugate is constant to the left of the origin, with the value `-g 0`. -/
theorem conj_mulPairing_of_nonpos (hg : MonotoneHalfLineFn g) (hs : s ≤ 0) :
    conj mulPairing g s = -g 0 := by
  rw [conj_mulPairing_apply hg.top_of_neg]
  refine le_antisymm (iSup_le fun t => iSup_le fun ht => ?_) ?_
  · refine le_trans (EReal.sub_le_sub (y := (0 : EReal)) ?_ le_rfl) ?_
    · exact_mod_cast mul_nonpos_of_nonneg_of_nonpos ht hs
    · rw [sub_eq_add_neg, zero_add, EReal.neg_le_neg_iff]; exact hg.zero_le t
  · refine le_trans (le_of_eq ?_)
      (le_trans (le_iSup (fun _ : (0 : ℝ) ≤ (0 : ℝ) => ((0 * s : ℝ) : EReal) - g 0) le_rfl)
        (le_iSup (fun t : ℝ => ⨆ _ : (0 : ℝ) ≤ t, ((t * s : ℝ) : EReal) - g t) (0 : ℝ)))
    rw [zero_mul, EReal.coe_zero, sub_eq_add_neg, zero_add]

/-- The monotone conjugate at the origin is `-g 0`. -/
theorem monotoneConj_zero (hg : MonotoneHalfLineFn g) : monotoneConj g 0 = -g 0 := by
  rw [monotoneConj_of_nonneg' hg.top_of_neg le_rfl, conj_mulPairing_of_nonpos hg le_rfl]

/-- **The class is stable under monotone conjugacy** — the first half of Rockafellar's
Theorem 12.4. -/
theorem monotoneHalfLineFn_monotoneConj (hg : MonotoneHalfLineFn g) :
    MonotoneHalfLineFn (monotoneConj g) where
  top_of_neg _ ht := monotoneConj_of_neg g ht
  monotoneOn s hs s' hs' hss := by
    rw [monotoneConj_of_nonneg' hg.top_of_neg hs, monotoneConj_of_nonneg' hg.top_of_neg hs']
    exact monotone_conj_mulPairing hg.top_of_neg hss
  convex := by
    rw [monotoneConj_eq_restrict_conj hg.top_of_neg]
    exact (convexFn_conj mulPairing g).restrict (convex_Ici 0)
  closed := by
    rw [monotoneConj_eq_restrict_conj hg.top_of_neg]
    exact closedFn_conj.restrict (fun _ => conj_ne_bot hg.proper.dom_nonempty _) isClosed_Ici
  zero_ne_top := by
    rw [monotoneConj_zero hg]
    exact fun h => hg.ne_bot 0 (EReal.neg_eq_top_iff.1 h)

/-- The negative half of the line contributes nothing to the biconjugate supremum at a nonnegative
argument: there `g⁺` is constant, and the constant is already the value of the term at the origin.
This is the only place where the truncation in `monotoneConj` has to be undone. -/
theorem iSup_sub_monotoneConj (hg : MonotoneHalfLineFn g) (ht : 0 ≤ t) :
    (⨆ s : ℝ, ((s * t : ℝ) : EReal) - monotoneConj g s)
      = ⨆ s : ℝ, ((s * t : ℝ) : EReal) - conj mulPairing g s := by
  refine le_antisymm
    (iSup_mono fun s => EReal.sub_le_sub le_rfl (conj_le_monotoneConj hg.top_of_neg s))
    (iSup_le fun s => ?_)
  rcases le_or_gt 0 s with hs | hs
  · exact le_trans (le_of_eq (by rw [monotoneConj_of_nonneg' hg.top_of_neg hs]))
      (le_iSup (fun s : ℝ => ((s * t : ℝ) : EReal) - monotoneConj g s) s)
  · have hz : (((0 : ℝ) * t : ℝ) : EReal) - monotoneConj g (0 : ℝ) = g 0 := by
      rw [monotoneConj_zero hg, zero_mul, EReal.coe_zero, sub_eq_add_neg, neg_neg, zero_add]
    refine le_trans ?_ (le_trans hz.ge
      (le_iSup (fun s : ℝ => ((s * t : ℝ) : EReal) - monotoneConj g s) (0 : ℝ)))
    rw [conj_mulPairing_of_nonpos hg hs.le, sub_eq_add_neg, neg_neg]
    calc ((s * t : ℝ) : EReal) + g 0
        ≤ (0 : EReal) + g 0 :=
          add_le_add (by exact_mod_cast mul_nonpos_of_nonpos_of_nonneg hs.le ht) le_rfl
      _ = g 0 := zero_add _

/-- **Rockafellar, Theorem 12.4.** Monotone conjugacy is an involution on the nondecreasing closed
convex functions of one nonnegative variable that are finite at the origin.

The proof is the Fenchel–Moreau theorem for `mulPairing` together with `iSup_sub_monotoneConj`,
which says that truncating the conjugate to the half-line does not change the second conjugate at
a nonnegative argument. -/
theorem monotoneConj_monotoneConj (hg : MonotoneHalfLineFn g) :
    monotoneConj (monotoneConj g) = g := by
  have hG := monotoneHalfLineFn_monotoneConj hg
  funext t
  rcases lt_or_ge t 0 with ht | ht
  · rw [monotoneConj_of_neg _ ht, hg.top_of_neg ht]
  have h1 : monotoneConj (monotoneConj g) t
      = ⨆ s : ℝ, ((s * t : ℝ) : EReal) - monotoneConj g s :=
    monotoneConj_of_nonneg' hG.top_of_neg ht
  have h2 : biconj mulPairing g t = ⨆ s : ℝ, ((t * s : ℝ) : EReal) - conj mulPairing g s := rfl
  rw [h1, iSup_sub_monotoneConj hg ht,
    iSup_congr (g := fun s : ℝ => ((t * s : ℝ) : EReal) - conj mulPairing g s)
      fun s => by rw [mul_comm], ← h2, biconj_eq_clFn hg.convex, hg.closed]

end MonotoneHalfLine

/-! ### Composing a gauge with a function on the half-line -/

section MonotoneComp

variable {E : Type*} {g : ℝ → EReal} {k : E → EReal} {x : E} {c : ℝ}

/-- The composite `g ∘ k` of a function on the half-line with a `[0, +∞]`-valued function `k`,
with the convention `g (+∞) = +∞`.

Presenting the composite as an infimum over the real levels above `k x` avoids extending `g` to
`EReal` by hand — and hence a `Decidable` split — while making both defining equations one-line
consequences: `monotoneComp g k x = g c` when `k x = c` and `g` is nondecreasing on the half-line
(`monotoneComp_of_eq_coe`), and `monotoneComp g k x = ⊤` when `k x = ⊤`
(`monotoneComp_of_eq_top`). -/
noncomputable def monotoneComp (g : ℝ → EReal) (k : E → EReal) : E → EReal :=
  fun x => ⨅ t : ℝ, ⨅ _ : k x ≤ (t : EReal), g t

/-- The defining formula for the composite. -/
theorem monotoneComp_apply (g : ℝ → EReal) (k : E → EReal) (x : E) :
    monotoneComp g k x = ⨅ t : ℝ, ⨅ _ : k x ≤ (t : EReal), g t := rfl

/-- Every real level above `k x` bounds the composite from above. -/
theorem monotoneComp_le (h : k x ≤ (c : EReal)) : monotoneComp g k x ≤ g c :=
  iInf_le_of_le c (le_of_eq (iInf_pos h))

/-- The composite is `+∞` wherever `k` is: no real level lies above `+∞`. -/
theorem monotoneComp_of_eq_top (g : ℝ → EReal) (h : k x = ⊤) : monotoneComp g k x = ⊤ :=
  iInf_eq_top.2 fun t => iInf_neg fun hc => EReal.coe_ne_top t (top_le_iff.1 (h ▸ hc))

/-- The composite at a finite value of `k`: the infimum is attained at the level `t = k x`,
because `g` is nondecreasing on the half-line. No semicontinuity is involved. -/
theorem monotoneComp_of_eq_coe (hg : MonotoneOn g (Set.Ici 0)) (hc : 0 ≤ c)
    (h : k x = (c : EReal)) : monotoneComp g k x = g c := by
  refine le_antisymm (monotoneComp_le (h.le.trans_eq rfl)) (le_iInf fun t => le_iInf fun ht => ?_)
  rw [h, EReal.coe_le_coe_iff] at ht
  exact hg (Set.mem_Ici.2 hc) (Set.mem_Ici.2 (hc.trans ht)) ht

/-- A nonnegative extended real is either `+∞` or a nonnegative real. -/
theorem eq_top_or_exists_coe_of_nonneg {z : EReal} (hz : 0 ≤ z) :
    z = ⊤ ∨ ∃ c : ℝ, 0 ≤ c ∧ z = (c : EReal) := by
  rcases eq_or_lt_of_le (le_top (a := z)) with htop | hlt
  · exact Or.inl htop
  obtain ⟨c, hc⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top
    (fun h => by simp [h] at hz) hlt
  exact Or.inr ⟨c, EReal.coe_nonneg.1 (hc ▸ hz), hc⟩

end MonotoneComp


/-! ### The conjugate of a gauge composed with a function on the half-line

The composite `g ∘ k` of a closed gauge with a nondecreasing closed convex function on the
half-line is conjugate to the composite of the polar gauge with the monotone conjugate. The proof
regroups the supremum defining the conjugate by the level `ζ = k x`: on the dilate `ζ • {k ≤ 1}`
the composite is at most `g ζ`, and the supremum of the pairing over that dilate is `ζ k°(y)`.

The lower bound needs no topology at all — only the trivial half `x ∈ ζ • C → k x ≤ ζ` of the
level-set description of a gauge. Closedness of `k` enters solely through the converse half, in
`conj_monotoneComp_le`. -/

section GaugeCompLower

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {g : ℝ → EReal} {k : E → EReal} {x : E} {y : F} {c : ℝ}

/-- **Where a gauge vanishes the pairing is nonpositive**, provided the polar gauge is finite
there.

The set `{k = 0}` is the recession cone of `{k ≤ 1}` and not in general `{0}`, so the bound has to
be obtained by scaling: `k (l⁻¹ • x) = 0 ≤ 1` for every `l > 0`, whence `⟨x, y⟩ ≤ l k°(y)`, and
letting `l` shrink gives `⟨x, y⟩ ≤ 0`. Finiteness of `k°(y)` is essential — in `EReal`,
`0 * (+∞) = 0`. -/
theorem pairing_nonpos_of_gauge_eq_zero (hk : IsGauge k) (hx : k x = 0)
    (hc : polarGauge B k y = (c : EReal)) : B x y ≤ 0 := by
  have hc0 : (0 : ℝ) ≤ c := by
    have h := polarGauge_nonneg B k y
    rw [hc] at h
    exact EReal.coe_nonneg.1 h
  have hsupp : supportFn B {z : E | k z ≤ 1} y = (c : EReal) := by
    rw [← hc, polarGauge_eq_supportFn hk.nonneg hk.posHomogeneous hk.map_zero]
  have hray : ∀ l : ℝ, 0 < l → B x y ≤ l * c := by
    intro l hl
    have hmem : l⁻¹ • x ∈ {z : E | k z ≤ 1} := by
      change k (l⁻¹ • x) ≤ 1
      rw [hk.posHomogeneous l⁻¹ (inv_pos.2 hl) x, hx, mul_zero]
      exact zero_le_one
    have hb := supportFn_le_coe_iff.1 hsupp.le _ hmem
    rwa [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hl] at hb
  by_contra hcon
  rw [not_le] at hcon
  have hb := hray _ (div_pos hcon (by linarith : (0 : ℝ) < 2 * (c + 1)))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (c + 1))] at hb
  nlinarith

/-- **The core lower bound for Theorem 15.3.** On the dilate `ζ • {k ≤ 1}` the composite `g ∘ k`
is at most `g ζ`, and the supremum of the pairing over that dilate is `ζ k°(y)`; so
`ζ k°(y) - g ζ` is a lower bound for the conjugate of `g ∘ k`, at every level `ζ > 0` where `g` is
finite.

Nothing is assumed about `g` beyond finiteness at the single level `ζ`, and nothing about `k`
beyond its being a gauge. This one lemma supplies both the `≥` half of the conjugacy formula and,
at a point where the polar gauge is `+∞`, the degeneracy that forces the conjugate to be `+∞`
there. -/
theorem coe_mul_polarGauge_sub_le_conj (hk : IsGauge k) {ζ r : ℝ} (hζ : 0 < ζ)
    (hr : g ζ = (r : EReal)) :
    (ζ : EReal) * polarGauge B k y - g ζ ≤ conj B (monotoneComp g k) y := by
  have hkC : gaugeFn {z : E | k z ≤ 1} = k :=
    gaugeFn_level_one hk.nonneg hk.posHomogeneous hk.map_zero
  have hsmul : (ζ : EReal) * polarGauge B k y = supportFn B (ζ • {z : E | k z ≤ 1}) y := by
    rw [polarGauge_eq_supportFn hk.nonneg hk.posHomogeneous hk.map_zero, supportFn_smul B hζ]
  have hbound : ∀ z ∈ ζ • {z : E | k z ≤ 1},
      ((B z y : ℝ) : EReal) + ((-r : ℝ) : EReal) ≤ conj B (monotoneComp g k) y := by
    intro z hz
    have hkz : k z ≤ (ζ : EReal) := by
      rw [← hkC]; exact gaugeFn_le_of_mem_smul hζ.le hz
    have hfz : monotoneComp g k z ≤ (r : EReal) := by
      rw [← hr]; exact monotoneComp_le hkz
    refine le_trans ?_ (sub_le_conj B (monotoneComp g k) z y)
    rw [_root_.EReal.coe_neg, ← sub_eq_add_neg]
    exact EReal.sub_le_sub le_rfl hfz
  rw [hsmul, hr, sub_eq_add_neg, ← _root_.EReal.coe_neg, supportFn_apply,
    Tdaf.EReal.biSup_add_coe]
  exact iSup₂_le hbound

/-- The origin realises the level `ζ = 0` of the computation, since a gauge vanishes there. -/
theorem sub_apply_zero_le_conj (hk : IsGauge k) (hg : MonotoneOn g (Set.Ici 0)) :
    (0 : EReal) - g 0 ≤ conj B (monotoneComp g k) y := by
  have hf0 : monotoneComp g k (0 : E) = g 0 :=
    monotoneComp_of_eq_coe hg le_rfl (by rw [hk.map_zero, _root_.EReal.coe_zero])
  have h := sub_le_conj B (monotoneComp g k) (0 : E) y
  rwa [hf0, map_zero, LinearMap.zero_apply, _root_.EReal.coe_zero] at h

/-- The `≥` half of the conjugacy formula, at a point where the polar gauge is finite. -/
theorem monotoneConj_le_conj_monotoneComp (hk : IsGauge k) (hg : MonotoneHalfLineFn g)
    (hc : polarGauge B k y = (c : EReal)) :
    monotoneConj g c ≤ conj B (monotoneComp g k) y := by
  have hc0 : (0 : ℝ) ≤ c := by
    have h := polarGauge_nonneg B k y
    rw [hc] at h
    exact EReal.coe_nonneg.1 h
  rw [monotoneConj_of_nonneg g hc0]
  refine iSup_le fun t => iSup_le fun ht => ?_
  by_cases htop : g t = ⊤
  · rw [htop, _root_.EReal.sub_top]; exact bot_le
  obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hg.ne_bot t)
    (lt_top_iff_ne_top.2 htop)
  rcases eq_or_lt_of_le ht with rfl | ht'
  · rw [zero_mul, _root_.EReal.coe_zero]
    exact sub_apply_zero_le_conj hk hg.monotoneOn
  · have h := coe_mul_polarGauge_sub_le_conj (B := B) (y := y) hk ht' hr
    rwa [hc, Tdaf.EReal.coe_mul_coe] at h

end GaugeCompLower

section GaugeComp

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {g : ℝ → EReal} {k : E → EReal} {x : E} {y : F} {c : ℝ}

/-- **The Cauchy–Schwarz inequality for a gauge and its polar**: `⟨x, y⟩ ≤ k(x) k°(y)` wherever
both sides are finite.

For `k(x) > 0` this is the level-set description of a closed gauge, `x ∈ k(x) • {k ≤ 1}`, together
with the identification of `k°` as the support function of `{k ≤ 1}`. For `k(x) = 0` the product
would be `0 · k°(y)`, and the bound is `pairing_nonpos_of_gauge_eq_zero`. -/
theorem pairing_le_mul_of_gauge (hk : IsGauge k) (hkc : ClosedFn k) {d : ℝ}
    (hx : k x = (c : EReal)) (hy : polarGauge B k y = (d : EReal)) : B x y ≤ c * d := by
  have hc0 : (0 : ℝ) ≤ c := by
    have h := hk.nonneg x
    rw [hx] at h
    exact EReal.coe_nonneg.1 h
  have hsupp : supportFn B {z : E | k z ≤ 1} y = (d : EReal) := by
    rw [← hy, polarGauge_eq_supportFn hk.nonneg hk.posHomogeneous hk.map_zero]
  rcases eq_or_lt_of_le hc0 with rfl | hpos
  · rw [zero_mul]
    exact pairing_nonpos_of_gauge_eq_zero hk (by rw [hx, _root_.EReal.coe_zero]) hy
  · have hkC : gaugeFn {z : E | k z ≤ 1} = k :=
      gaugeFn_level_one hk.nonneg hk.posHomogeneous hk.map_zero
    have hmem : x ∈ c • {z : E | k z ≤ 1} := by
      rw [← setOf_gaugeFn_le_pos (IsGauge.convex_level_one hk) (IsGauge.zero_mem_level_one hk)
        (isClosed_setOf_le_one hkc) hpos]
      change gaugeFn {z : E | k z ≤ 1} x ≤ (c : EReal)
      rw [hkC, hx]
    have hb := le_supportFn (B := B) hmem y
    rwa [supportFn_smul B hpos, hsupp, Tdaf.EReal.coe_mul_coe, EReal.coe_le_coe_iff] at hb

/-- The `≤` half of the conjugacy formula, at a point where the polar gauge is finite.

The supremum over `x` is regrouped by the level `ζ = k x`, and on each level the pairing is bounded
by `pairing_le_mul_of_gauge`. -/
theorem conj_monotoneComp_le (hk : IsGauge k) (hkc : ClosedFn k) (hg : MonotoneHalfLineFn g)
    (hc : polarGauge B k y = (c : EReal)) :
    conj B (monotoneComp g k) y ≤ monotoneConj g c := by
  have hc0 : (0 : ℝ) ≤ c := by
    have h := polarGauge_nonneg B k y
    rw [hc] at h
    exact EReal.coe_nonneg.1 h
  rw [conj_apply, monotoneConj_of_nonneg g hc0]
  refine iSup_le fun z => ?_
  rcases eq_top_or_exists_coe_of_nonneg (hk.nonneg z) with hz | ⟨c', hc'0, hc'⟩
  · rw [monotoneComp_of_eq_top g hz, _root_.EReal.sub_top]; exact bot_le
  have hfz : monotoneComp g k z = g c' := monotoneComp_of_eq_coe hg.monotoneOn hc'0 hc'
  have hpair : B z y ≤ c' * c := pairing_le_mul_of_gauge hk hkc hc' hc
  calc ((B z y : ℝ) : EReal) - monotoneComp g k z
      ≤ ((c' * c : ℝ) : EReal) - g c' := by
        rw [hfz]
        exact EReal.sub_le_sub (EReal.coe_le_coe_iff.2 hpair) le_rfl
    _ ≤ ⨆ t : ℝ, ⨆ _ : (0 : ℝ) ≤ t, ((t * c : ℝ) : EReal) - g t :=
        le_trans (le_iSup (fun _ : (0 : ℝ) ≤ c' => ((c' * c : ℝ) : EReal) - g c') hc'0)
          (le_iSup (fun t : ℝ => ⨆ _ : (0 : ℝ) ≤ t, ((t * c : ℝ) : EReal) - g t) c')

/-- **Rockafellar, Theorem 15.3**, the conjugacy formula: for a closed gauge `k` and a
nondecreasing closed convex `g` on the half-line that is finite at some positive level, the
conjugate of `g ∘ k` is `g⁺ ∘ k°`.

The finiteness hypothesis is used **only** where `k°(y) = +∞`, to force the conjugate to be `+∞`
there; both halves of the finite case hold without it. It cannot be dropped: for `g` the indicator
of `{0}` the left-hand side is `δ*(· ∣ {k ≤ 0})`, which vanishes on the polar of the recession cone
of `{k ≤ 1}`, while the right-hand side is `+∞` off the barrier cone of `{k ≤ 1}`, and those two
cones differ.

Neither compatibility nor continuity of the pairing is needed, and `g` need not be non-constant;
the topology on `E` enters only through the closedness of `k`. -/
theorem conj_monotoneComp (hk : IsGauge k) (hkc : ClosedFn k) (hg : MonotoneHalfLineFn g)
    (hfin : ∃ ζ : ℝ, 0 < ζ ∧ g ζ ≠ ⊤) :
    conj B (monotoneComp g k) = monotoneComp (monotoneConj g) (polarGauge B k) := by
  funext y
  rcases eq_top_or_exists_coe_of_nonneg (polarGauge_nonneg B k y) with htop | ⟨c, hc0, hc⟩
  · rw [monotoneComp_of_eq_top _ htop]
    obtain ⟨ζ, hζ, hζt⟩ := hfin
    obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hg.ne_bot ζ)
      (lt_top_iff_ne_top.2 hζt)
    have h := coe_mul_polarGauge_sub_le_conj (B := B) (y := y) hk hζ hr
    rw [htop, hr, _root_.EReal.coe_mul_top_of_pos hζ, _root_.EReal.top_sub_coe] at h
    exact top_le_iff.1 h
  · rw [monotoneComp_of_eq_coe (monotoneHalfLineFn_monotoneConj hg).monotoneOn hc0 hc]
    exact le_antisymm (conj_monotoneComp_le hk hkc hg hc)
      (monotoneConj_le_conj_monotoneComp hk hg hc)

end GaugeComp

end Tdaf.ConvexAnalysis
