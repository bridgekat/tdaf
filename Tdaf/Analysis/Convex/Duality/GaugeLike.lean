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

end Tdaf.ConvexAnalysis
