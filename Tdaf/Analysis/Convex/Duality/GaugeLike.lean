/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Tdaf.Analysis.Convex.Duality.Gauge

/-!
# Monotone conjugacy on the half-line, and the convex functions built from a gauge

Two correspondences that fit together. The first is conjugacy for nondecreasing convex functions
of one nonnegative variable: on that class the ordinary conjugate, cut back to the half-line, is
again such a function, and the operation is an involution. The second composes such a function
with a closed gauge on a vector space; the result is a convex function all of whose sublevel sets
are dilates of one another, and conjugacy on those functions is the first correspondence applied
level by level, with the gauge replaced by its polar.

Specialising the half-line factor to `ζ ↦ ζ^p / p` gives the functions positively homogeneous of
degree `p`, whose conjugates are positively homogeneous of the Hölder conjugate degree `q`. That
the two powers are exchanged is Young's inequality, read as a conjugacy.

## Main definitions

* `MonotoneHalfLineFn g` — `g : ℝ → EReal` is `+∞` on the negative axis, nondecreasing on the
  half-line, convex, closed, and finite at the origin.
* `monotoneConj g` — the **monotone conjugate** `g⁺(s) = sup {t s - g t ∣ t ≥ 0}`, itself taken to
  be `+∞` for `s < 0`.
* `monotoneComp g k` — the composite `g ∘ k` of such a `g` with a `[0, +∞]`-valued `k`, under the
  convention `g (+∞) = +∞`.
* `powHalfLine p` — the function `ζ ↦ ζ^p / p` of the half-line.
* `PosHomogeneousDeg p f` — `f (λ x) = λ^p f x` for `λ > 0`.
* `degGauge p f` — the gauge `(p f)^{1/p}` attached to such an `f`.

## Main results

* `monotoneHalfLineFn_monotoneConj`, `monotoneConj_monotoneConj` — the class is stable under
  `monotoneConj`, and `g⁺⁺ = g`.
* `conj_monotoneComp` — `(g ∘ k)* = g⁺ ∘ k°` for a closed gauge `k`.
* `monotoneConj_powHalfLine` — `(ζ ↦ ζ^p / p)⁺ = (σ ↦ σ^q / q)`.
* `posHomogeneousDeg_iff_exists_isGauge` — a closed proper convex function is positively
  homogeneous of degree `p` exactly when it is `(1/p) k^p` for a closed gauge `k`.
* `conj_monotoneComp_powHalfLine`, `polarGauge_degGauge`, `pairing_le_rpow_mul_rpow`,
  `polarSet_setOf_le_inv` — the conjugate of `(1/p) k^p` is `(1/q) (k°)^q`, the gauges
  `(p f)^{1/p}` and `(q f*)^{1/q}` are polar, and the level sets `{f ≤ 1/p}` and `{f* ≤ 1/q}` are
  polar sets.

## What is not here

The **characterisation** half of Rockafellar's Theorem 15.3 — that every gauge-like closed proper
convex function is of the form `g ∘ k` — is absent; only the conjugacy formula and the corollaries
that flow from it are proved. Corollary 15.3.1 does not depend on the characterisation: the gauge
is exhibited directly as `degGauge p f`, whose unit level set is `{f ≤ 1/p}`.

Note also that a `MonotoneHalfLineFn` may be constant, and then `g ∘ k` need **not** be closed:
its sublevel sets are `dom k`, which for a closed gauge can fail to be closed. That is what
Rockafellar's "non-constant" hypothesis buys. The conjugacy formula itself does not need it.

## References

Rockafellar, *Convex Analysis*, Theorem 12.4, and Theorem 15.3 with Corollaries 15.3.1 and
15.3.2.
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

/-! ### The powers of the half-line

`ζ ↦ ζ^p / p` for `1 < p < ∞`. Under monotone conjugacy these functions are permuted by
`p ↦ q`, the Hölder conjugate exponent; that is Young's inequality, read as a conjugacy. -/

section PowHalfLine

variable {p q ζ : ℝ}

/-- The function `ζ ↦ ζ^p / p` of the half-line, extended by `+∞` to the negative axis. -/
noncomputable def powHalfLine (p : ℝ) : ℝ → EReal :=
  ConvexAnalysis.restrict (Set.Ici 0) fun ζ => ((ζ ^ p / p : ℝ) : EReal)

@[simp] theorem powHalfLine_of_nonneg (p : ℝ) (hζ : 0 ≤ ζ) :
    powHalfLine p ζ = ((ζ ^ p / p : ℝ) : EReal) := restrict_of_mem hζ

theorem powHalfLine_of_neg (p : ℝ) (hζ : ζ < 0) : powHalfLine p ζ = ⊤ :=
  restrict_of_notMem (by simpa using hζ)

theorem powHalfLine_ne_top (p : ℝ) (hζ : 0 ≤ ζ) : powHalfLine p ζ ≠ ⊤ := by
  rw [powHalfLine_of_nonneg p hζ]; exact EReal.coe_ne_top _

theorem powHalfLine_zero (hp : 0 < p) : powHalfLine p 0 = 0 := by
  rw [powHalfLine_of_nonneg p le_rfl, Real.zero_rpow hp.ne', zero_div, _root_.EReal.coe_zero]

/-- `ζ ↦ ζ^p / p` is nondecreasing on the half-line. -/
theorem monotoneOn_powHalfLine (hp : 0 < p) : MonotoneOn (powHalfLine p) (Set.Ici 0) := by
  intro a ha b hb hab
  rw [powHalfLine_of_nonneg p ha, powHalfLine_of_nonneg p hb, EReal.coe_le_coe_iff]
  have h := Real.rpow_le_rpow ha hab hp.le
  gcongr

/-- Raising `z^{1/p}` back to the `p`th power returns `z`. -/
theorem rpow_inv_rpow (hp : 0 < p) {z : ℝ} (hz : 0 ≤ z) : (z ^ p⁻¹) ^ p = z := by
  rw [← Real.rpow_mul hz, inv_mul_cancel₀ hp.ne', Real.rpow_one]

/-- Taking the `1/p`th power of `z^p` returns `z`. -/
theorem rpow_rpow_inv (hp : 0 < p) {z : ℝ} (hz : 0 ≤ z) : (z ^ p) ^ p⁻¹ = z := by
  rw [← Real.rpow_mul hz, mul_inv_cancel₀ hp.ne', Real.rpow_one]

/-- The `1/p`th power does not move the unit level. -/
theorem rpow_inv_le_one_iff (hp : 0 < p) {z : ℝ} (hz : 0 ≤ z) : z ^ p⁻¹ ≤ 1 ↔ z ≤ 1 := by
  constructor
  · intro h
    have := Real.rpow_le_rpow (Real.rpow_nonneg hz _) h hp.le
    rwa [rpow_inv_rpow hp hz, Real.one_rpow] at this
  · intro h
    have := Real.rpow_le_rpow hz h (by positivity : (0 : ℝ) ≤ p⁻¹)
    rwa [Real.one_rpow] at this

/-- `ζ ↦ ζ^p / p` is a nondecreasing closed convex function of the half-line, finite at the
origin — the class on which monotone conjugacy is an involution. -/
theorem monotoneHalfLineFn_powHalfLine (hp : 1 ≤ p) : MonotoneHalfLineFn (powHalfLine p) where
  top_of_neg _ h := powHalfLine_of_neg p h
  monotoneOn := monotoneOn_powHalfLine (lt_of_lt_of_le zero_lt_one hp)
  convex := by
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
    have h := (convexOn_rpow hp).smul (le_of_lt (one_div_pos.2 hp0))
    have heq : (fun x : ℝ => (1 / p) • x ^ p) = fun x : ℝ => x ^ p / p := by
      funext x; rw [smul_eq_mul, one_div, inv_mul_eq_div]
    rw [heq] at h
    exact (convexOn_iff_convexFn (Set.Ici 0) fun x : ℝ => x ^ p / p).1 h
  closed := by
    have hcont : Continuous fun ζ : ℝ => ((ζ ^ p / p : ℝ) : EReal) :=
      EReal.continuous_coe_iff.2 ((Real.continuous_rpow_const (by linarith)).div_const p)
    exact ClosedFn.restrict
      ((closedFn_iff_lowerSemicontinuous fun _ => EReal.coe_ne_bot _).2
        hcont.lowerSemicontinuous)
      (fun _ => EReal.coe_ne_bot _) isClosed_Ici
  zero_ne_top := powHalfLine_ne_top p le_rfl

/-- **Young's inequality, as a conjugacy** (Rockafellar, Corollary 15.3.1): the monotone conjugate
of `ζ ↦ ζ^p / p` is `σ ↦ σ^q / q`, for Hölder conjugate exponents `p` and `q`.

The supremum `sup {ζ σ - ζ^p / p ∣ ζ ≥ 0}` is bounded above by `σ^q / q` by Young's inequality and
attained at `ζ = σ^{q-1}`, where `ζ σ = ζ^p = σ^q`. -/
theorem monotoneConj_powHalfLine (hpq : p.HolderConjugate q) :
    monotoneConj (powHalfLine p) = powHalfLine q := by
  have hp0 : (0 : ℝ) < p := hpq.pos
  have hq0 : (0 : ℝ) < q := hpq.symm.pos
  funext s
  rcases lt_or_ge s 0 with hs | hs
  · rw [monotoneConj_of_neg _ hs, powHalfLine_of_neg _ hs]
  rw [monotoneConj_of_nonneg _ hs, powHalfLine_of_nonneg _ hs]
  refine le_antisymm (iSup_le fun t => iSup_le fun ht => ?_) ?_
  · rw [powHalfLine_of_nonneg p ht, ← _root_.EReal.coe_sub, EReal.coe_le_coe_iff]
    have := Real.young_inequality_of_nonneg ht hs hpq
    linarith
  · have hq1 : (0 : ℝ) < q - 1 := hpq.symm.sub_one_pos
    have ht₀0 : (0 : ℝ) ≤ s ^ (q - 1) := Real.rpow_nonneg hs _
    have hval : s ^ (q - 1) * s - (s ^ (q - 1)) ^ p / p = s ^ q / q := by
      rcases eq_or_lt_of_le hs with rfl | hspos
      · rw [Real.zero_rpow hq1.ne', Real.zero_rpow hq0.ne', Real.zero_rpow hp0.ne']
        ring
      · have h1 : s ^ (q - 1) * s = s ^ q := by
          have hadd := Real.rpow_add hspos (q - 1) 1
          rw [Real.rpow_one] at hadd
          rw [← hadd]
          norm_num
        have h2 : (s ^ (q - 1)) ^ p = s ^ q := by
          rw [← Real.rpow_mul hs, hpq.symm.sub_one_mul_conj]
        rw [h1, h2]
        have h3 : (1 : ℝ) - p⁻¹ = q⁻¹ := hpq.one_sub_inv
        have h4 : s ^ q - s ^ q / p = s ^ q * (1 - p⁻¹) := by ring
        rw [h4, h3]; ring
    refine le_trans (le_of_eq ?_)
      (le_trans (le_iSup (fun _ : (0 : ℝ) ≤ s ^ (q - 1) =>
          ((s ^ (q - 1) * s : ℝ) : EReal) - powHalfLine p (s ^ (q - 1))) ht₀0)
        (le_iSup (fun t : ℝ => ⨆ _ : (0 : ℝ) ≤ t,
          ((t * s : ℝ) : EReal) - powHalfLine p t) (s ^ (q - 1))))
    rw [powHalfLine_of_nonneg p ht₀0, ← _root_.EReal.coe_sub, hval]

end PowHalfLine

/-! ### Positive homogeneity of degree `p`

`f (λ x) = λ^p f x` for `λ > 0`. For `1 < p < ∞` these are exactly the functions `(1/p) k^p` of a
closed gauge `k`, and the gauge is recovered as `(p f)^{1/p}`. -/

section PosHomogeneousDeg

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f k : E → EReal} {x : E} {p : ℝ}

/-- A function is **positively homogeneous of degree `p`** when `f (λ • x) = λ^p f x` for every
`λ > 0`. Degree `1` is `PosHomogeneous`; as there, only positive scalars are constrained, so the
value at the origin is not determined. -/
def PosHomogeneousDeg (p : ℝ) (f : E → EReal) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ x, f (a • x) = ((a ^ p : ℝ) : EReal) * f x

/-- Positive homogeneity of positive degree leaves only three possible values at the origin. -/
theorem PosHomogeneousDeg.map_zero_trichotomy (hp : 0 < p) (hf : PosHomogeneousDeg p f) :
    f 0 = 0 ∨ f 0 = ⊤ ∨ f 0 = ⊥ := by
  have h2 : ((2 : ℝ) ^ p) ≠ 1 := by
    have h := Real.rpow_lt_rpow_left_iff (x := 2) (y := 0) (z := p) (by norm_num)
    rw [Real.rpow_zero] at h
    exact ne_of_gt (h.2 hp)
  refine Tdaf.EReal.eq_zero_or_eq_top_or_eq_bot h2 ?_
  have h := hf 2 two_pos 0
  rw [smul_zero] at h
  exact h.symm

/-- **A convex function positively homogeneous of degree `p > 1` that vanishes at the origin is
nonnegative.** Convexity gives `λ^p f x ≤ λ f x` for `0 < λ < 1`, and `λ^p < λ` there. -/
theorem PosHomogeneousDeg.nonneg (hp : 1 < p) (hconv : ConvexFn f) (hne : ∀ z, f z ≠ ⊥)
    (hf : PosHomogeneousDeg p f) (h0 : f 0 = 0) (x : E) : 0 ≤ f x := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨a, ha⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hne x)
    (hcon.trans (by simp : (0 : EReal) < ⊤))
  have ha0 : a < 0 := by rw [ha] at hcon; exact_mod_cast hcon
  have hzero : f (0 : E) ≤ ((0 : ℝ) : EReal) := by rw [h0, _root_.EReal.coe_zero]
  have hcombo := hconv.epi_combo (x := x) (y := (0 : E)) (μ := a) (ν := 0) (le_of_eq ha) hzero
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [smul_zero, add_zero, hf _ (by norm_num) x, ha, Tdaf.EReal.coe_mul_coe,
    EReal.coe_le_coe_iff] at hcombo
  have hlt : ((1 : ℝ) / 2) ^ p < 1 / 2 := by
    have h := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1) hp
    rwa [Real.rpow_one] at h
  nlinarith [mul_lt_mul_of_neg_left hlt ha0]

/-- The composite `(1/p) k^p` of a gauge is positively homogeneous of degree `p`. -/
theorem posHomogeneousDeg_monotoneComp_powHalfLine (hp : 0 < p) (hk : IsGauge k) :
    PosHomogeneousDeg p (monotoneComp (powHalfLine p) k) := by
  intro a ha z
  rcases eq_top_or_exists_coe_of_nonneg (hk.nonneg z) with hz | ⟨c, hc0, hz⟩
  · have haz : k (a • z) = ⊤ := by
      rw [hk.posHomogeneous a ha z, hz, _root_.EReal.coe_mul_top_of_pos ha]
    rw [monotoneComp_of_eq_top _ haz, monotoneComp_of_eq_top _ hz,
      _root_.EReal.coe_mul_top_of_pos (Real.rpow_pos_of_pos ha p)]
  · have haz : k (a • z) = ((a * c : ℝ) : EReal) := by
      rw [hk.posHomogeneous a ha z, hz, Tdaf.EReal.coe_mul_coe]
    rw [monotoneComp_of_eq_coe (monotoneOn_powHalfLine hp) (by positivity) haz,
      monotoneComp_of_eq_coe (monotoneOn_powHalfLine hp) hc0 hz,
      powHalfLine_of_nonneg p (by positivity : (0 : ℝ) ≤ a * c), powHalfLine_of_nonneg p hc0,
      Tdaf.EReal.coe_mul_coe]
    exact congrArg _ (by rw [Real.mul_rpow ha.le hc0]; ring)

/-- The **gauge attached to a function positively homogeneous of degree `p`**: `(p f)^{1/p}`, with
`(+∞)^{1/p} = +∞`.

Written through `monotoneComp` so that the two defining equations come for free: it is
`(p a)^{1/p}` where `f` takes the finite value `a ≥ 0`, and `+∞` where `f` is. -/
noncomputable def degGauge (p : ℝ) (f : E → EReal) : E → EReal :=
  monotoneComp (fun a : ℝ => (((p * a) ^ p⁻¹ : ℝ) : EReal)) f

theorem monotoneOn_degGaugeFn (hp : 0 < p) :
    MonotoneOn (fun a : ℝ => (((p * a) ^ p⁻¹ : ℝ) : EReal)) (Set.Ici 0) := by
  intro a ha b _ hab
  have ha0 : (0 : ℝ) ≤ a := Set.mem_Ici.1 ha
  rw [EReal.coe_le_coe_iff]
  exact Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)

omit [AddCommGroup E] [Module ℝ E] in
theorem degGauge_of_eq_coe (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) (h : f x = (a : EReal)) :
    degGauge p f x = (((p * a) ^ p⁻¹ : ℝ) : EReal) :=
  monotoneComp_of_eq_coe (monotoneOn_degGaugeFn hp) ha h

omit [AddCommGroup E] [Module ℝ E] in
theorem degGauge_of_eq_top (p : ℝ) (h : f x = ⊤) : degGauge p f x = ⊤ :=
  monotoneComp_of_eq_top _ h

omit [AddCommGroup E] [Module ℝ E] in
theorem degGauge_nonneg (hp : 0 < p) (hnn : ∀ z, 0 ≤ f z) (x : E) : 0 ≤ degGauge p f x := by
  rcases eq_top_or_exists_coe_of_nonneg (hnn x) with hx | ⟨a, ha0, hx⟩
  · rw [degGauge_of_eq_top p hx]; exact le_top
  · rw [degGauge_of_eq_coe hp ha0 hx]
    exact EReal.coe_nonneg.2 (Real.rpow_nonneg (by positivity) _)

omit [Module ℝ E] in
theorem degGauge_map_zero (hp : 0 < p) (h0 : f 0 = 0) : degGauge p f 0 = 0 := by
  rw [degGauge_of_eq_coe hp le_rfl (by rw [h0, _root_.EReal.coe_zero]), mul_zero,
    Real.zero_rpow (by positivity), _root_.EReal.coe_zero]

theorem posHomogeneous_degGauge (hp : 0 < p) (hnn : ∀ z, 0 ≤ f z) (hf : PosHomogeneousDeg p f) :
    PosHomogeneous (degGauge p f) := by
  intro a ha z
  rcases eq_top_or_exists_coe_of_nonneg (hnn z) with hz | ⟨c, hc0, hz⟩
  · have haz : f (a • z) = ⊤ := by
      rw [hf a ha z, hz, _root_.EReal.coe_mul_top_of_pos (Real.rpow_pos_of_pos ha p)]
    rw [degGauge_of_eq_top p haz, degGauge_of_eq_top p hz,
      _root_.EReal.coe_mul_top_of_pos ha]
  · have haz : f (a • z) = ((a ^ p * c : ℝ) : EReal) := by
      rw [hf a ha z, hz, Tdaf.EReal.coe_mul_coe]
    have hac : (0 : ℝ) ≤ a ^ p * c := by positivity
    rw [degGauge_of_eq_coe hp hac haz, degGauge_of_eq_coe hp hc0 hz, Tdaf.EReal.coe_mul_coe]
    refine congrArg _ ?_
    have hrw : p * (a ^ p * c) = a ^ p * (p * c) := by ring
    rw [hrw, Real.mul_rpow (Real.rpow_nonneg ha.le p) (by positivity), rpow_rpow_inv hp ha.le]

omit [AddCommGroup E] [Module ℝ E] in
/-- The unit level set of `(p f)^{1/p}` is the level set `{f ≤ 1/p}`. -/
theorem setOf_degGauge_le_one (hp : 0 < p) (hnn : ∀ z, 0 ≤ f z) :
    {x : E | degGauge p f x ≤ 1} = {x : E | f x ≤ ((p⁻¹ : ℝ) : EReal)} := by
  ext z
  rcases eq_top_or_exists_coe_of_nonneg (hnn z) with hz | ⟨a, ha0, hz⟩
  · simp only [Set.mem_ofPred, degGauge_of_eq_top p hz, hz]
    have h1 : ¬ ((⊤ : EReal) ≤ 1) := by
      rw [top_le_iff, ← _root_.EReal.coe_one]
      exact EReal.coe_ne_top 1
    have h2 : ¬ ((⊤ : EReal) ≤ ((p⁻¹ : ℝ) : EReal)) := by
      rw [top_le_iff]; exact EReal.coe_ne_top _
    exact iff_of_false h1 h2
  · have hpa : (0 : ℝ) ≤ p * a := by positivity
    have h1 : degGauge p f z ≤ 1 ↔ (p * a) ^ p⁻¹ ≤ 1 := by
      rw [degGauge_of_eq_coe hp ha0 hz,
        show ((1 : EReal)) = ((1 : ℝ) : EReal) from (_root_.EReal.coe_one).symm,
        EReal.coe_le_coe_iff]
    have h2 : f z ≤ ((p⁻¹ : ℝ) : EReal) ↔ a ≤ p⁻¹ := by rw [hz, EReal.coe_le_coe_iff]
    change degGauge p f z ≤ 1 ↔ f z ≤ ((p⁻¹ : ℝ) : EReal)
    rw [h1, h2, rpow_inv_le_one_iff hp hpa, ← le_div_iff₀' hp, one_div]

/-- `(p f)^{1/p}` is the Minkowski functional of `{f ≤ 1/p}`. -/
theorem degGauge_eq_gaugeFn (hp : 0 < p) (hnn : ∀ z, 0 ≤ f z) (hf : PosHomogeneousDeg p f)
    (h0 : f 0 = 0) : degGauge p f = gaugeFn {x : E | f x ≤ ((p⁻¹ : ℝ) : EReal)} := by
  rw [← setOf_degGauge_le_one hp hnn]
  exact (gaugeFn_level_one (degGauge_nonneg hp hnn) (posHomogeneous_degGauge hp hnn hf)
    (degGauge_map_zero hp h0)).symm

/-- `(p f)^{1/p}` is a gauge. Convexity is not proved from the formula but read off from the
level set: `(p f)^{1/p}` is the Minkowski functional of the convex set `{f ≤ 1/p}`. -/
theorem isGauge_degGauge (hp : 0 < p) (hconv : ConvexFn f) (hnn : ∀ z, 0 ≤ f z)
    (hf : PosHomogeneousDeg p f) (h0 : f 0 = 0) : IsGauge (degGauge p f) where
  nonneg := degGauge_nonneg hp hnn
  posHomogeneous := posHomogeneous_degGauge hp hnn hf
  convexFn := by
    rw [degGauge_eq_gaugeFn hp hnn hf h0]
    exact convexFn_gaugeFn (hconv.convex_le _)
  map_zero := degGauge_map_zero hp h0

omit [AddCommGroup E] [Module ℝ E] in
/-- **`(1/p) [(p f)^{1/p}]^p = f`**: the gauge attached to a nonnegative function recovers it. -/
theorem monotoneComp_powHalfLine_degGauge (hp : 0 < p) (hnn : ∀ z, 0 ≤ f z) :
    monotoneComp (powHalfLine p) (degGauge p f) = f := by
  funext z
  rcases eq_top_or_exists_coe_of_nonneg (hnn z) with hz | ⟨a, ha0, hz⟩
  · rw [monotoneComp_of_eq_top _ (degGauge_of_eq_top p hz), hz]
  · have hpa : (0 : ℝ) ≤ p * a := by positivity
    have hd0 : (0 : ℝ) ≤ (p * a) ^ p⁻¹ := Real.rpow_nonneg hpa _
    have hval : ((p * a) ^ p⁻¹) ^ p / p = a := by
      rw [rpow_inv_rpow hp hpa]
      field_simp
    rw [monotoneComp_of_eq_coe (monotoneOn_powHalfLine hp) hd0 (degGauge_of_eq_coe hp ha0 hz),
      powHalfLine_of_nonneg p hd0, hval, hz]

/-- **`(p · (1/p) k^p)^{1/p} = k`**: the gauge is recovered from the composite, so the
representation of Corollary 15.3.1 is unique. -/
theorem degGauge_monotoneComp_powHalfLine (hp : 0 < p) (hk : IsGauge k) :
    degGauge p (monotoneComp (powHalfLine p) k) = k := by
  funext z
  rcases eq_top_or_exists_coe_of_nonneg (hk.nonneg z) with hz | ⟨c, hc0, hz⟩
  · rw [degGauge_of_eq_top p (monotoneComp_of_eq_top _ hz), hz]
  · have hval : p * (c ^ p / p) = c ^ p := by field_simp
    rw [degGauge_of_eq_coe (f := monotoneComp (powHalfLine p) k) hp (a := c ^ p / p)
        (by positivity)
        (by rw [monotoneComp_of_eq_coe (monotoneOn_powHalfLine hp) hc0 hz,
          powHalfLine_of_nonneg p hc0]),
      hval, rpow_rpow_inv hp hc0, hz]

end PosHomogeneousDeg

/-! ### Homogeneity of degree `p` for closed functions

Closedness is what pins the value at the origin, and with it the sign. -/

section PosHomogeneousDegClosed

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f : E → EReal} {p : ℝ}

/-- **A closed proper function positively homogeneous of degree `p > 0` vanishes at the origin.**
Along a ray into the origin the values are `λ^p f x₀ → 0`, so the epigraph, being closed, contains
`(0, 0)`; of the three values homogeneity allows at the origin, only `0` is `≤ 0`. -/
theorem PosHomogeneousDeg.map_zero_eq_zero (hp : 0 < p) (hcl : ClosedFn f) (hpr : Proper f)
    (hf : PosHomogeneousDeg p f) : f 0 = 0 := by
  obtain ⟨x₀, hx₀⟩ := hpr.dom_nonempty
  obtain ⟨b, hb⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hpr.ne_bot x₀) hx₀
  have hepi : IsClosed (epi f) :=
    lowerSemicontinuous_iff_isClosed_epi.1 (ClosedFn.lowerSemicontinuous hcl)
  have hmem : ∀ n : ℕ, ((1 / (n + 1 : ℝ)) • x₀, (1 / (n + 1 : ℝ)) ^ p * b) ∈ epi f := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have h : f ((1 / (n + 1 : ℝ)) • x₀) = (((1 / (n + 1 : ℝ)) ^ p * b : ℝ) : EReal) := by
      rw [hf _ hpos x₀, hb, Tdaf.EReal.coe_mul_coe]
    exact le_of_eq h
  have h1 : Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) • x₀) Filter.atTop (nhds (0 : E)) := by
    have hc : Continuous fun r : ℝ => r • x₀ := continuous_id.smul continuous_const
    have h := (hc.tendsto (0 : ℝ)).comp tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [zero_smul] at h
  have h2 : Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) ^ p * b) Filter.atTop
      (nhds (0 : ℝ)) := by
    have hc : Continuous fun r : ℝ => r ^ p * b :=
      (Real.continuous_rpow_const hp.le).mul continuous_const
    have h := (hc.tendsto (0 : ℝ)).comp tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [Real.zero_rpow hp.ne', zero_mul] at h
  have htend : Filter.Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ)) • x₀, (1 / (n + 1 : ℝ)) ^ p * b))
      Filter.atTop (nhds ((0 : E), (0 : ℝ))) := by
    rw [nhds_prod_eq]
    exact Filter.Tendsto.prodMk h1 h2
  have hzero := hepi.mem_of_tendsto htend (Filter.Eventually.of_forall hmem)
  have hle : f (0 : E) ≤ 0 := by
    have h : f (0 : E) ≤ ((0 : ℝ) : EReal) := hzero
    rwa [_root_.EReal.coe_zero] at h
  rcases PosHomogeneousDeg.map_zero_trichotomy hp hf with h | h | h
  · exact h
  · rw [h] at hle; exact absurd hle (by simp)
  · exact absurd h (hpr.ne_bot 0)

/-- `(p f)^{1/p}` is a **closed** gauge, being the Minkowski functional of the closed convex set
`{f ≤ 1/p}`. -/
theorem closedFn_degGauge (hp : 0 < p) (hconv : ConvexFn f) (hcl : ClosedFn f)
    (hnn : ∀ z, 0 ≤ f z) (hf : PosHomogeneousDeg p f) (h0 : f 0 = 0) :
    ClosedFn (degGauge p f) := by
  rw [degGauge_eq_gaugeFn hp hnn hf h0]
  refine closedFn_gaugeFn (hconv.convex_le _) ?_
    (lowerSemicontinuous_iff_isClosed_preimage.1 (ClosedFn.lowerSemicontinuous hcl) _)
  change f 0 ≤ ((p⁻¹ : ℝ) : EReal)
  rw [h0]
  exact EReal.coe_nonneg.2 (by positivity)

/-- **The representation `f = (1/p) [(p f)^{1/p}]^p`** of a closed proper convex function
positively homogeneous of degree `p`. -/
theorem monotoneComp_powHalfLine_degGauge_eq_self (hp : 1 < p) (hconv : ConvexFn f)
    (hcl : ClosedFn f) (hpr : Proper f) (hf : PosHomogeneousDeg p f) :
    monotoneComp (powHalfLine p) (degGauge p f) = f :=
  monotoneComp_powHalfLine_degGauge (lt_trans zero_lt_one hp)
    (PosHomogeneousDeg.nonneg hp hconv hpr.ne_bot hf
      (PosHomogeneousDeg.map_zero_eq_zero (lt_trans zero_lt_one hp) hcl hpr hf))

/-- **Rockafellar, Corollary 15.3.1**, first assertion: a closed proper convex function is
positively homogeneous of degree `p ∈ (1, ∞)` exactly when it is `(1/p) k^p` for a closed gauge
`k`. The gauge is unique — it is `(p f)^{1/p}`, by `degGauge_monotoneComp_powHalfLine`. -/
theorem posHomogeneousDeg_iff_exists_isGauge (hp : 1 < p) (hconv : ConvexFn f) (hcl : ClosedFn f)
    (hpr : Proper f) :
    PosHomogeneousDeg p f ↔
      ∃ k : E → EReal, IsGauge k ∧ ClosedFn k ∧ f = monotoneComp (powHalfLine p) k := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  refine ⟨fun hf => ?_, ?_⟩
  · have h0 : f 0 = 0 := PosHomogeneousDeg.map_zero_eq_zero hp0 hcl hpr hf
    have hnn : ∀ z, 0 ≤ f z := PosHomogeneousDeg.nonneg hp hconv hpr.ne_bot hf h0
    exact ⟨degGauge p f, isGauge_degGauge hp0 hconv hnn hf h0,
      closedFn_degGauge hp0 hconv hcl hnn hf h0,
      (monotoneComp_powHalfLine_degGauge hp0 hnn).symm⟩
  · rintro ⟨k, hk, -, rfl⟩
    exact posHomogeneousDeg_monotoneComp_powHalfLine hp0 hk

end PosHomogeneousDegClosed

/-! ### Conjugacy for the homogeneous functions of degree `p`

Corollaries 15.3.1 and 15.3.2: `[(1/p) k^p]* = (1/q) (k°)^q`, the gauge `(p f)^{1/p}` is polar to
`(q f*)^{1/q}`, and the two unit level sets `{f ≤ 1/p}` and `{f* ≤ 1/q}` are polar sets. -/

section PowConj

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f k : E → EReal} {x : E} {y : F} {p q : ℝ}

/-- **Rockafellar, Corollary 15.3.1**, second assertion: `[(1/p) k^p]* = (1/q) (k°)^q`. -/
theorem conj_monotoneComp_powHalfLine (hpq : p.HolderConjugate q) (hk : IsGauge k)
    (hkc : ClosedFn k) :
    conj B (monotoneComp (powHalfLine p) k) = monotoneComp (powHalfLine q) (polarGauge B k) := by
  rw [conj_monotoneComp hk hkc (monotoneHalfLineFn_powHalfLine hpq.lt.le)
      ⟨1, one_pos, powHalfLine_ne_top p zero_le_one⟩,
    monotoneConj_powHalfLine hpq]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The unit level set of a polar gauge is the polar set of the unit level set. -/
theorem setOf_polarGauge_le_one (hk : IsGauge k) :
    {y : F | polarGauge B k y ≤ 1} = polarSet B {x : E | k x ≤ 1} := by
  rw [polarGauge_eq_supportFn hk.nonneg hk.posHomogeneous hk.map_zero]
  ext z
  change supportFn B {x : E | k x ≤ 1} z ≤ 1 ↔ z ∈ polarSet B {x : E | k x ≤ 1}
  rw [show ((1 : EReal)) = ((1 : ℝ) : EReal) from (_root_.EReal.coe_one).symm,
    supportFn_le_coe_iff, mem_polarSet]

variable (hpq : p.HolderConjugate q) (hconv : ConvexFn f) (hcl : ClosedFn f) (hpr : Proper f)
  (hf : PosHomogeneousDeg p f)
include hpq hconv hcl hpr hf

/-- The conjugate of a closed proper convex function positively homogeneous of degree `p` is
`(1/q) (k°)^q` for the gauge `k = (p f)^{1/p}` — in particular it is positively homogeneous of
degree `q`. -/
theorem conj_eq_monotoneComp_powHalfLine :
    conj B f = monotoneComp (powHalfLine q) (polarGauge B (degGauge p f)) := by
  have h0 : f 0 = 0 := PosHomogeneousDeg.map_zero_eq_zero hpq.pos hcl hpr hf
  have hnn : ∀ z, 0 ≤ f z := PosHomogeneousDeg.nonneg hpq.lt hconv hpr.ne_bot hf h0
  conv_lhs => rw [← monotoneComp_powHalfLine_degGauge hpq.pos hnn]
  exact conj_monotoneComp_powHalfLine hpq (isGauge_degGauge hpq.pos hconv hnn hf h0)
    (closedFn_degGauge hpq.pos hconv hcl hnn hf h0)

/-- **Rockafellar, Corollary 15.3.2**: `(p f)^{1/p}` is a closed gauge whose polar is
`(q f*)^{1/q}`. -/
theorem polarGauge_degGauge : polarGauge B (degGauge p f) = degGauge q (conj B f) := by
  have h0 : f 0 = 0 := PosHomogeneousDeg.map_zero_eq_zero hpq.pos hcl hpr hf
  have hnn : ∀ z, 0 ≤ f z := PosHomogeneousDeg.nonneg hpq.lt hconv hpr.ne_bot hf h0
  rw [conj_eq_monotoneComp_powHalfLine (B := B) hpq hconv hcl hpr hf,
    degGauge_monotoneComp_powHalfLine hpq.symm.pos
      (isGauge_polarGauge (B := B) (degGauge_nonneg hpq.pos hnn)
        (posHomogeneous_degGauge hpq.pos hnn hf) (degGauge_map_zero hpq.pos h0))]

/-- **Rockafellar, Corollary 15.3.2**, the Hölder-type inequality
`⟨x, y⟩ ≤ [p f(x)]^{1/p} [q f*(y)]^{1/q}` on `dom f × dom f*`. -/
theorem pairing_le_rpow_mul_rpow {a b : ℝ} (hx : f x = (a : EReal))
    (hy : conj B f y = (b : EReal)) : B x y ≤ (p * a) ^ p⁻¹ * (q * b) ^ q⁻¹ := by
  have h0 : f 0 = 0 := PosHomogeneousDeg.map_zero_eq_zero hpq.pos hcl hpr hf
  have hnn : ∀ z, 0 ≤ f z := PosHomogeneousDeg.nonneg hpq.lt hconv hpr.ne_bot hf h0
  have ha0 : (0 : ℝ) ≤ a := by
    have h := hnn x
    rw [hx] at h
    exact EReal.coe_nonneg.1 h
  have hb0 : (0 : ℝ) ≤ b := by
    have h := zero_le_conj (B := B) (le_of_eq h0) y
    rw [hy] at h
    exact EReal.coe_nonneg.1 h
  refine pairing_le_mul_of_gauge (isGauge_degGauge hpq.pos hconv hnn hf h0)
    (closedFn_degGauge hpq.pos hconv hcl hnn hf h0) (degGauge_of_eq_coe hpq.pos ha0 hx) ?_
  rw [polarGauge_degGauge hpq hconv hcl hpr hf]
  exact degGauge_of_eq_coe hpq.symm.pos hb0 hy

/-- **Rockafellar, Corollary 15.3.2**: the closed convex sets `{f ≤ 1/p}` and `{f* ≤ 1/q}` are
polar to each other. -/
theorem polarSet_setOf_le_inv :
    polarSet B {x : E | f x ≤ ((p⁻¹ : ℝ) : EReal)}
      = {y : F | conj B f y ≤ ((q⁻¹ : ℝ) : EReal)} := by
  have h0 : f 0 = 0 := PosHomogeneousDeg.map_zero_eq_zero hpq.pos hcl hpr hf
  have hnn : ∀ z, 0 ≤ f z := PosHomogeneousDeg.nonneg hpq.lt hconv hpr.ne_bot hf h0
  have hcnn : ∀ z, 0 ≤ conj B f z := fun z => zero_le_conj (le_of_eq h0) z
  rw [← setOf_degGauge_le_one hpq.pos hnn, ← setOf_polarGauge_le_one
      (isGauge_degGauge hpq.pos hconv hnn hf h0),
    polarGauge_degGauge hpq hconv hcl hpr hf, setOf_degGauge_le_one hpq.symm.pos hcnn]

end PowConj

end Tdaf.ConvexAnalysis
