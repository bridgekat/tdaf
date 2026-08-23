/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.ConcaveConj
import Tdaf.Analysis.Convex.Duality.Polar
import Tdaf.Analysis.Convex.Optimization.Minimum

/-!
# Fenchel's duality theorem

Rockafellar's §31. Minimising a difference `f - g`, with `f` convex and `g` concave, is dual to
maximising `g* - f*`, where `g*` is the *concave* conjugate.

## Main results

* `concaveConj_sub_conj_le_sub` — weak duality, pointwise: `g*(y) - f*(y) ≤ f x - g x`. This is
  Fenchel's inequality used twice, and it needs no hypothesis whatsoever.
* `fenchel_duality` — **Theorem 31.1** under condition (a): `inf (f - g) = sup (g* - f*)`.
* `exists_concaveConj_sub_conj_eq`, `isGreatest_concaveConj_sub_conj` — under (a) the supremum is
  attained.
* `fenchel_duality_of_closed`, `exists_sub_eq_iInf` — **Theorem 31.1** under condition (b): the same
  equality, with the *infimum* attained.
* `fenchel_duality_comp`, `exists_concaveConj_sub_conj_comp_eq` — **Theorem 31.2**: the same
  equality with a linear transformation interposed, `inf (f - g A) = sup (g* - f* A')`, with the
  supremum attained. `concaveConj_compLin` is the concave face of Theorem 16.3 that it runs on.
* `sub_eq_concaveConj_sub_conj_iff` — **Theorem 31.3**, the Kuhn–Tucker conditions `y ∈ ∂f x` and
  `-y ∈ ∂(-g) x`, with `iInf_sub_eq_iff_exists_kuhnTucker` for **Corollary 31.3.1**.
* `sub_comp_eq_concaveConj_sub_conj_iff` — **Theorem 31.3** with a linear transformation: the
  Kuhn–Tucker conditions `A' z ∈ ∂f x` and `-z ∈ ∂(-g)(A x)`, with
  `iInf_sub_comp_eq_iff_exists_kuhnTucker` for **Corollary 31.3.1**.

## Design notes

**The hypothesis is `IsExactSum B f (-g)`, not a constraint qualification.** Rockafellar states
Theorem 31.1 under (a) `ri (dom f) ∩ ri (dom g) ≠ ∅`, under (b) `f`, `g` closed with
`ri (dom g*) ∩ ri (dom f*) ≠ ∅`, and under two polyhedral weakenings of each. All four are ways of
saying that `f` and `-g` add exactly — Theorem 16.4 for (a), Theorem 20.1 for the polyhedral
variants — so the theorem is proved once against `IsExactSum` and every variant is an instance.
See `Duality/Relint.lean` and `Polyhedral/Duality.lean` for the sufficient conditions.

**`f - g` is `f + (-g)`, and that is the whole proof.** Fenchel's theorem is Theorem 27.1(a)
(`inf h = -h*(0)`) applied to `h = f + (-g)`, with Theorem 16.4 splitting `h*(0)` as an infimal
convolution and `neg_concaveConj` turning `(-g)*(-y)` into `-g*(y)`. No separation argument is
needed here because the separation already happened, once, in Theorem 16.4.

**Condition (b) is condition (a) on the dual pair.** `fenchel_duality` applied with `B.flip` to
`f*` and `-g*`, together with Fenchel–Moreau, gives the same equality with the *infimum* attained;
that is `exists_sub_eq_iSup_of_closed` below.

**Theorem 31.2 splits condition (a) into two interfaces.** Rockafellar's condition (a) for the
transformed problem is "there is an `x ∈ ri (dom f)` with `A x ∈ ri (dom g)`". That single
condition does two jobs: it makes `f` and `-(g A)` add exactly (Theorem 16.4) and it makes `g` pull
back exactly along `A` (Theorem 16.3). Here the two jobs are separate hypotheses, `IsExactSum` and
`IsExactImage`, for the same reason that Theorem 31.1 takes `IsExactSum` rather than a constraint
qualification: the polyhedral weakenings of (a) supply the same two interfaces.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §31
  (Theorems 31.1-31.5).
-/

namespace Tdaf.ConvexAnalysis

section Fenchel

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- Negation turns a difference around, provided neither of the two `∞ - ∞` collisions occurs. -/
private theorem neg_sub_comm {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊤) : -(a - b) = b - a := by
  rw [_root_.EReal.neg_sub (.inl ha) (.inr hb), sub_eq_add_neg, add_comm]

/-- The companion of `neg_sub_comm` with the other pair of side conditions. -/
private theorem neg_sub_comm' {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊥) : -(a - b) = b - a := by
  rw [_root_.EReal.neg_sub (.inr hb) (.inl ha), sub_eq_add_neg, add_comm]

omit [Module ℝ E] [Module ℝ F] in
/-- Reindexing an infimum over a group by negation. -/
private theorem iInf_neg_comp (ψ : F → EReal) : (⨅ y : F, ψ y) = ⨅ y : F, ψ (-y) :=
  le_antisymm (le_iInf fun y => iInf_le ψ (-y))
    (le_iInf fun y => le_trans (iInf_le (fun z => ψ (-z)) (-y)) (le_of_eq (by rw [neg_neg])))

/-- **The arithmetic behind weak duality.** Two Fenchel inequalities sharing the same *finite*
value `p` combine into a comparison of differences. No hypothesis on `a`, `b`, `c`, `d` is needed:
both `∞ - ∞` collisions are already absorbed on the correct side. -/
private theorem sub_le_sub_of_le_sub_of_sub_le {a b c d : EReal} {p : ℝ}
    (h1 : a ≤ (p : EReal) - b) (h2 : (p : EReal) - c ≤ d) : a - d ≤ c - b := by
  have hpb : ((p : ℝ) : EReal) ≠ ⊥ := _root_.EReal.coe_ne_bot _
  have hpt : ((p : ℝ) : EReal) ≠ ⊤ := _root_.EReal.coe_ne_top _
  have h3 : -d ≤ c - ((p : ℝ) : EReal) := by
    refine le_trans (_root_.EReal.neg_le_neg_iff.2 h2) (le_of_eq ?_)
    rw [_root_.EReal.neg_sub (.inl hpb) (.inl hpt), sub_eq_add_neg, add_comm]
  have hsum : a + -d ≤ (((p : ℝ) : EReal) - b) + (c - ((p : ℝ) : EReal)) := add_le_add h1 h3
  refine le_trans (le_of_eq (sub_eq_add_neg _ _)) (le_trans hsum (le_of_eq ?_))
  rw [sub_eq_add_neg ((p : ℝ) : EReal) b, sub_eq_add_neg c ((p : ℝ) : EReal),
    add_comm c (-((p : ℝ) : EReal)),
    add_add_add_comm ((p : ℝ) : EReal) (-b) (-((p : ℝ) : EReal)) c]
  have hpp : ((p : ℝ) : EReal) + -((p : ℝ) : EReal) = 0 := by
    rw [← _root_.EReal.coe_neg, ← _root_.EReal.coe_add, add_neg_cancel, _root_.EReal.coe_zero]
  rw [hpp, zero_add, add_comm (-b) c, sub_eq_add_neg]

/-- **Weak duality**, pointwise: every dual value is below every primal value. This is Fenchel's
inequality for `f` and Fenchel's inequality for `g` added together.

No hypothesis at all is needed. Both `∞ - ∞` collisions are already absorbed on the correct side:
if `f x = ⊥` then `f* y = ⊤` and the left side is `⊥`, and if `g x = ⊤` then `g* y = ⊥` and the
left side is `⊥` again. -/
theorem concaveConj_sub_conj_le_sub (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) (x : E) (y : F) :
    concaveConj B g y - conj B f y ≤ f x - g x :=
  sub_le_sub_of_le_sub_of_sub_le (concaveConj_le_sub B g x y) (sub_le_conj B f x y)

/-- **Rockafellar, Theorem 31.1 (Fenchel's duality theorem)**: the infimum of `f - g` equals the
supremum of `g* - f*`.

The whole proof is Theorem 27.1(a) applied to `f + (-g)`, plus Theorem 16.4 to split the conjugate
of that sum at the origin, plus the sign dictionary `neg_concaveConj`. -/
theorem fenchel_duality (hex : IsExactSum B f (-g)) :
    (⨅ x, f x - g x) = ⨆ y, concaveConj B g y - conj B f y := by
  have hex' : IsExactSum B f (fun x => -(g x)) := hex
  have hne : ∀ y : F, concaveConj B g y ≠ ⊤ := fun y hc =>
    hex'.conj_right_ne_bot (-y) (by rw [← neg_concaveConj B g y, hc, _root_.EReal.neg_top])
  have hprimal : (⨅ x, f x - g x) = -(conj B (f + fun x => -(g x)) 0) := by
    rw [← iInf_eq_neg_conj_zero B]
    exact iInf_congr fun x => by rw [Pi.add_apply, sub_eq_add_neg]
  have hdual : conj B (f + fun x => -(g x)) 0 = ⨅ y : F, conj B f y - concaveConj B g y := by
    rw [hex'.conj_add_apply 0, iInf_neg_comp]
    refine iInf_congr fun y => ?_
    rw [zero_sub, neg_neg, ← neg_concaveConj B g y, sub_eq_add_neg]
  rw [hprimal, hdual, Tdaf.EReal.neg_iInf]
  exact iSup_congr fun y => neg_sub_comm (hex'.conj_left_ne_bot y) (hne y)

/-- **Rockafellar, Theorem 31.1**, the attainment clause: under exact addition the supremum of
`g* - f*` is attained. This is the attainment half of Theorem 16.4 read at the origin. -/
theorem exists_concaveConj_sub_conj_eq (hex : IsExactSum B f (-g)) :
    ∃ y : F, concaveConj B g y - conj B f y = ⨅ x, f x - g x := by
  have hex' : IsExactSum B f (fun x => -(g x)) := hex
  have hne : ∀ y : F, concaveConj B g y ≠ ⊤ := fun y hc =>
    hex'.conj_right_ne_bot (-y) (by rw [← neg_concaveConj B g y, hc, _root_.EReal.neg_top])
  have hprimal : (⨅ x, f x - g x) = -(conj B (f + fun x => -(g x)) 0) := by
    rw [← iInf_eq_neg_conj_zero B]
    exact iInf_congr fun x => by rw [Pi.add_apply, sub_eq_add_neg]
  obtain ⟨y₁, y₂, hy, hval⟩ := hex'.exists_conj_add_eq 0
  have hy2 : y₂ = -y₁ := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hy
  subst hy2
  rw [← neg_concaveConj B g y₁, ← sub_eq_add_neg] at hval
  refine ⟨y₁, ?_⟩
  rw [hprimal, ← hval, neg_sub_comm (hex'.conj_left_ne_bot y₁) (hne y₁)]

/-- **Rockafellar, Theorem 31.1**, packaged: the common value is the *greatest* dual value. -/
theorem isGreatest_concaveConj_sub_conj (hex : IsExactSum B f (-g)) :
    IsGreatest (Set.range fun y => concaveConj B g y - conj B f y) (⨅ x, f x - g x) := by
  obtain ⟨y, hy⟩ := exists_concaveConj_sub_conj_eq hex
  refine ⟨⟨y, hy⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  rw [fenchel_duality hex]
  exact le_iSup (fun w : F => concaveConj B g w - conj B f w) z

end Fenchel

/-! ### Theorem 31.2: a linear transformation between the two functions -/

section Comp

/-- A constant slides out of a supremum as a subtrahend, provided it is not `-∞`.

The hypothesis is exactly what rules out the disagreement at `c = ⊥`: there `(⨆ i, u i) - ⊥` is
`⊤` as soon as the supremum is not `⊥`, while every `u i - ⊥` is `⊤` only where `u i ≠ ⊥`. -/
private theorem iSup_sub_of_ne_bot {ι : Sort*} (u : ι → EReal) {c : EReal} (hc : c ≠ ⊥) :
    (⨆ i, u i) - c = ⨆ i, (u i - c) := by
  induction c with
  | bot => exact absurd rfl hc
  | coe r =>
    rw [sub_eq_add_neg, ← _root_.EReal.coe_neg, Tdaf.EReal.iSup_add_coe]
    exact iSup_congr fun i => by rw [sub_eq_add_neg, ← _root_.EReal.coe_neg]
  | top =>
    have h : ∀ x : EReal, x - (⊤ : EReal) = ⊥ := fun x => by
      rw [sub_eq_add_neg, _root_.EReal.neg_top, _root_.EReal.add_bot]
    simp only [h, iSup_bot]

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {f : E → EReal} {g : G → EReal}

/-- **The concave face of Rockafellar's Theorem 16.3.** The concave conjugate of an inverse image
`g A` is the *supremum* of `g*` over the fibres of the transpose, where the convex statement
(`IsExactImage.conj_compLin`) has an infimum.

Both reflections of `neg_concaveConj` are at work: the fibre `A' z = -y` of the convex statement
becomes the fibre `A' z = y` here, because `z` is reflected as well as the value. -/
theorem concaveConj_compLin (hA : IsAdjointPair B B' A A')
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) (y : F) :
    concaveConj B (compLin g A) y = ⨆ z : H, ⨆ _ : A' z = y, concaveConj B' g z := by
  set k : H → EReal := conj B' (fun w => -(g w)) with hk
  have hneg : ∀ z : H, -(concaveConj B' g z) = k (-z) := fun z => neg_concaveConj B' g z
  have hmain : mapLin A' k (-y) = ⨅ z : H, ⨅ _ : A' z = y, k (-z) := by
    refine le_antisymm (le_iInf fun z => le_iInf fun hz => mapLin_le ?_) (le_mapLin fun w hw => ?_)
    · rw [map_neg, hz]
    · refine le_trans (iInf₂_le (f := fun z (_ : A' z = y) => k (-z)) (-w) ?_) (le_of_eq ?_)
      · rw [map_neg, hw, neg_neg]
      · rw [neg_neg]
  have hcomp : concaveConj B (compLin g A) y = -(mapLin A' k (-y)) := by
    rw [concaveConj_eq_neg_conj_neg]
    congr 1
    exact congrFun (himg.conj_compLin) (-y)
  rw [hcomp, hmain, Tdaf.EReal.neg_iInf]
  refine iSup_congr fun z => ?_
  rw [Tdaf.EReal.neg_iInf]
  exact iSup_congr fun _ => (hneg z).symm ▸ neg_neg _

/-- **Rockafellar, Theorem 31.2 (Fenchel's duality theorem with a linear transformation)**:
`inf (f - g A) = sup (g* - f* A')`.

Theorem 31.1 applied to `f` and `g A` gives the supremum over the *dual* space `F`; the concave
face of Theorem 16.3 (`concaveConj_compLin`) rewrites each dual value as a supremum over the fibre
of `A'`, and the two suprema collapse into one over `H`.

The two hypotheses are Rockafellar's condition (a) split in two. `hex` is what makes `f` and
`-(g A)` add exactly (Theorem 16.4), `himg` is what makes `g` pull back exactly along `A`
(Theorem 16.3); `ri (dom f) ∩ A⁻¹ (ri (dom g)) ≠ ∅` delivers both. -/
theorem fenchel_duality_comp (hA : IsAdjointPair B B' A A')
    (hex : IsExactSum B f fun x => -(g (A x)))
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) :
    (⨅ x, f x - g (A x)) = ⨆ z : H, concaveConj B' g z - conj B f (A' z) := by
  have hex' : IsExactSum B f (-(compLin g A)) := hex
  have h31 : (⨅ x, f x - g (A x)) = ⨆ y : F, concaveConj B (compLin g A) y - conj B f y :=
    fenchel_duality hex'
  have key : ∀ y : F, concaveConj B (compLin g A) y - conj B f y
      = ⨆ z : H, ⨆ _ : A' z = y, (concaveConj B' g z - conj B f (A' z)) := by
    intro y
    rw [concaveConj_compLin hA himg y, iSup_sub_of_ne_bot _ (hex'.conj_left_ne_bot y)]
    refine iSup_congr fun z => ?_
    rw [iSup_sub_of_ne_bot _ (hex'.conj_left_ne_bot y)]
    exact iSup_congr fun hz => by rw [hz]
  rw [h31]
  refine le_antisymm (iSup_le fun y => ?_) (iSup_le fun z => ?_)
  · rw [key y]
    exact iSup_le fun w => iSup_le fun _ =>
      le_iSup (fun v : H => concaveConj B' g v - conj B f (A' v)) w
  · refine le_trans ?_
      (le_iSup (fun y : F => concaveConj B (compLin g A) y - conj B f y) (A' z))
    rw [key (A' z)]
    exact le_iSup₂ (f := fun w (_ : A' w = A' z) => concaveConj B' g w - conj B f (A' w)) z rfl

/-- **Rockafellar, Theorem 31.2**, the attainment clause: under exact addition and exact pullback
the supremum of `g* - f* A'` is attained.

Two attainment statements are chained: Theorem 31.1 attains the supremum over `F` at some `y`, and
Theorem 16.3 attains the infimum over the fibre `A' ⁻¹ {-y}` at some `z`. The second is available
only where `(−g A)*(−y)` is finite, so the degenerate case — a common value of `-∞`, where every
dual value already equals it — is taken separately. -/
theorem exists_concaveConj_sub_conj_comp_eq (hA : IsAdjointPair B B' A A')
    (hex : IsExactSum B f fun x => -(g (A x)))
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) :
    ∃ z : H, concaveConj B' g z - conj B f (A' z) = ⨅ x, f x - g (A x) := by
  have hex' : IsExactSum B f (-(compLin g A)) := hex
  rcases eq_or_ne (⨅ x, f x - g (A x)) ⊥ with hb | hb
  · have hle : concaveConj B' g 0 - conj B f (A' 0) ≤ ⨅ x, f x - g (A x) := by
      rw [fenchel_duality_comp hA hex himg]
      exact le_iSup (fun z : H => concaveConj B' g z - conj B f (A' z)) 0
    exact ⟨0, le_antisymm hle (by rw [hb]; exact bot_le)⟩
  obtain ⟨y, hy⟩ : ∃ y : F, concaveConj B (compLin g A) y - conj B f y = ⨅ x, f x - g (A x) :=
    exists_concaveConj_sub_conj_eq hex'
  have hyb : concaveConj B (compLin g A) y ≠ ⊥ := by
    intro hc
    exact hb (by rw [← hy, hc, sub_eq_add_neg, _root_.EReal.bot_add])
  have hlt : conj B (compLin (fun w => -(g w)) A) (-y) < ⊤ := by
    refine lt_of_le_of_ne le_top fun hc => hyb ?_
    rw [concaveConj_eq_neg_conj_neg]
    change -(conj B (compLin (fun w => -(g w)) A) (-y)) = ⊥
    rw [hc, _root_.EReal.neg_top]
  obtain ⟨z, hz, hzeq⟩ := himg.exists_conj_compLin_eq hlt
  refine ⟨-z, ?_⟩
  have hA'z : A' (-z) = y := by rw [map_neg, hz, neg_neg]
  have hval : concaveConj B' g (-z) = concaveConj B (compLin g A) y := by
    rw [concaveConj_eq_neg_conj_neg, neg_neg, hzeq, concaveConj_eq_neg_conj_neg]
    rfl
  rw [hA'z, hval, hy]

end Comp

/-! ### Condition (b): the closed case, with the infimum attained -/

section Closed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f g : E → EReal}

/-- The dual-side reading of the primal value: under condition (b) the infimum of `f - g` is minus
the infimum of `f* - g*`.

Everything here is `fenchel_duality` applied to the pair `(f*, g*)` over `B.flip`, with
Fenchel–Moreau collapsing the two biconjugates. -/
theorem iInf_sub_eq_neg_iInf_conj_sub (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn fun x => -(g x))
    (hex : IsExactSum B.flip (conj B f) (-(concaveConj B g))) :
    (⨅ x, f x - g x) = -(⨅ y : F, conj B f y - concaveConj B g y) := by
  have hgt : ∀ x, g x ≠ ⊤ := fun x hx => hg.proper.ne_bot x (by rw [hx, _root_.EReal.neg_top])
  have hbi : ∀ x, conj B.flip (conj B f) x = f x := fun x =>
    congrFun (biconj_eq_self hf.convex hf.closed) x
  have hbc : ∀ x, concaveConj B.flip (concaveConj B g) x = g x := fun x =>
    congrFun (biconcaveConj_eq_self (concaveFn_iff_convexFn_neg.2 hg.convex) hg.closed) x
  have hkey := fenchel_duality (B := B.flip) (f := conj B f) (g := concaveConj B g) hex
  rw [show (⨆ x : E, concaveConj B.flip (concaveConj B g) x - conj B.flip (conj B f) x)
        = ⨆ x : E, -(f x - g x) from
      iSup_congr fun x => by
        rw [hbi, hbc]
        exact (neg_sub_comm (hf.proper.ne_bot x) (hgt x)).symm,
    ← Tdaf.EReal.neg_iInf] at hkey
  rw [hkey, neg_neg]

/-- **Rockafellar, Theorem 31.1** under condition (b): `f` and `g` closed, with the conjugates
adding exactly. The equality is the same; what condition (b) buys is attainment on the *primal*
side, which is `exists_sub_eq_iInf`. -/
theorem fenchel_duality_of_closed (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn fun x => -(g x))
    (hex : IsExactSum B.flip (conj B f) (-(concaveConj B g))) :
    (⨅ x, f x - g x) = ⨆ y : F, concaveConj B g y - conj B f y := by
  have hdc : (domConcave g).Nonempty := by
    rw [domConcave_eq_dom_neg]
    exact hg.proper.dom_nonempty
  rw [iInf_sub_eq_neg_iInf_conj_sub hf hg hex, Tdaf.EReal.neg_iInf]
  exact iSup_congr fun y =>
    neg_sub_comm (conj_ne_bot hf.proper.dom_nonempty y) (concaveConj_ne_top hdc y)

/-- **Rockafellar, Theorem 31.1**, condition (b)'s attainment clause: the *infimum* of `f - g` is
attained. It is `exists_concaveConj_sub_conj_eq` on the dual pair. -/
theorem exists_sub_eq_iInf (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn fun x => -(g x))
    (hex : IsExactSum B.flip (conj B f) (-(concaveConj B g))) :
    ∃ x : E, f x - g x = ⨅ z, f z - g z := by
  have hgt : ∀ x, g x ≠ ⊤ := fun x hx => hg.proper.ne_bot x (by rw [hx, _root_.EReal.neg_top])
  have hbi : ∀ x, conj B.flip (conj B f) x = f x := fun x =>
    congrFun (biconj_eq_self hf.convex hf.closed) x
  have hbc : ∀ x, concaveConj B.flip (concaveConj B g) x = g x := fun x =>
    congrFun (biconcaveConj_eq_self (concaveFn_iff_convexFn_neg.2 hg.convex) hg.closed) x
  obtain ⟨x, hx⟩ := exists_concaveConj_sub_conj_eq (B := B.flip) (f := conj B f)
    (g := concaveConj B g) hex
  rw [hbi, hbc] at hx
  exact ⟨x, by rw [iInf_sub_eq_neg_iInf_conj_sub hf hg hex, ← hx,
    neg_sub_comm' (hgt x) (hf.proper.ne_bot x)]⟩

end Closed

/-! ### Theorem 31.3: the Fenchel optimality conditions -/

section Optimality

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal} {x : E} {y : F}

/-- A difference of two `EReal`s that avoids both `∞ - ∞` collisions on the *stated* side is finite
as soon as it equals another such difference. -/
private theorem finite_of_sub_eq {a b c d : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (hd : d ≠ ⊥) (h : a - b = c - d) : a ≠ ⊤ ∧ b ≠ ⊥ ∧ c ≠ ⊥ ∧ d ≠ ⊤ := by
  induction a <;> induction b <;> induction c <;> induction d <;>
    simp_all [← _root_.EReal.coe_sub]

private theorem finite_of_add_eq {a d p : EReal} (ha : a ≠ ⊥) (hd : d ≠ ⊥) (hp : p ≠ ⊤)
    (h : a + d = p) : a ≠ ⊤ ∧ d ≠ ⊤ := by
  induction a <;> induction d <;> simp_all

private theorem finite_of_add_eq' {b c p : EReal} (hb : b ≠ ⊤) (hc : c ≠ ⊤) (hp : p ≠ ⊥)
    (h : b + c = p) : b ≠ ⊥ ∧ c ≠ ⊥ := by
  induction b <;> induction c <;> simp_all

/-- **The arithmetic behind Theorem 31.3.** Squeezed between `p ≤ a + d` and `b + c ≤ p`, the
equality `a - b = c - d` says exactly that both squeezes are tight. -/
private theorem sub_eq_sub_iff_of_le {a b c d p : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (hd : d ≠ ⊥) (hp1 : p ≠ ⊥) (hp2 : p ≠ ⊤) (h1 : p ≤ a + d) (h2 : b + c ≤ p) :
    a - b = c - d ↔ a + d = p ∧ b + c = p := by
  obtain ⟨π, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hp1 (lt_top_iff_ne_top.2 hp2)
  constructor
  · intro h
    obtain ⟨hat, hbb, hcb, hdt⟩ := finite_of_sub_eq ha hb hc hd h
    obtain ⟨α, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top ha (lt_top_iff_ne_top.2 hat)
    obtain ⟨β, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbb (lt_top_iff_ne_top.2 hb)
    obtain ⟨γ, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hcb (lt_top_iff_ne_top.2 hc)
    obtain ⟨δ, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hd (lt_top_iff_ne_top.2 hdt)
    rw [← _root_.EReal.coe_sub, ← _root_.EReal.coe_sub, _root_.EReal.coe_eq_coe_iff] at h
    rw [← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at h1
    rw [← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at h2
    rw [← _root_.EReal.coe_add, ← _root_.EReal.coe_add, _root_.EReal.coe_eq_coe_iff,
      _root_.EReal.coe_eq_coe_iff]
    constructor <;> linarith
  · rintro ⟨e1, e2⟩
    obtain ⟨hat, hdt⟩ := finite_of_add_eq ha hd (_root_.EReal.coe_ne_top π) e1
    obtain ⟨hbb, hcb⟩ := finite_of_add_eq' hb hc (_root_.EReal.coe_ne_bot π) e2
    obtain ⟨α, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top ha (lt_top_iff_ne_top.2 hat)
    obtain ⟨β, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbb (lt_top_iff_ne_top.2 hb)
    obtain ⟨γ, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hcb (lt_top_iff_ne_top.2 hc)
    obtain ⟨δ, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hd (lt_top_iff_ne_top.2 hdt)
    rw [← _root_.EReal.coe_add, _root_.EReal.coe_eq_coe_iff] at e1
    rw [← _root_.EReal.coe_add, _root_.EReal.coe_eq_coe_iff] at e2
    rw [← _root_.EReal.coe_sub, ← _root_.EReal.coe_sub, _root_.EReal.coe_eq_coe_iff]
    linarith

/-- **Theorem 23.5 on the concave side**: the concave Fenchel equality `g x + g*(y) = ⟨x, y⟩` says
that `-y` is a subgradient of the convex function `-g` at `x`.

Rockafellar writes the condition as `x ∈ ∂g*(y)`, using the superdifferential of a concave
function. That superdifferential is `-∂(-g)`, so no new notion is needed here. -/
theorem neg_mem_subgradient_neg_iff_add_concaveConj_eq (hpg : Proper fun z => -(g z)) :
    -y ∈ subgradient B (fun z => -(g z)) x ↔ g x + concaveConj B g y = ((B x y : ℝ) : EReal) := by
  have hgt : g x ≠ ⊤ := fun hc => hpg.ne_bot x (by rw [hc, _root_.EReal.neg_top])
  have hdc : (domConcave g).Nonempty := by
    rw [domConcave_eq_dom_neg]
    exact hpg.dom_nonempty
  have hct : concaveConj B g y ≠ ⊤ := concaveConj_ne_top hdc y
  have hpn : ((B x (-y) : ℝ) : EReal) = -((B x y : ℝ) : EReal) := by
    rw [map_neg, _root_.EReal.coe_neg]
  rw [hpg.mem_subgradient_iff_add_conj_eq, ← neg_concaveConj B g y, hpn, ← sub_eq_add_neg,
    ← _root_.EReal.neg_add (.inr hct) (.inl hgt), neg_inj]

/-- **Rockafellar, Theorem 31.3** (with the linear transformation taken to be the identity): `x`
and `y` are jointly optimal for the two problems of Fenchel's duality theorem exactly when they
satisfy the Kuhn–Tucker conditions `y ∈ ∂f x` and `-y ∈ ∂(-g) x`.

Both conditions are Fenchel's inequality holding with equality (Theorem 23.5), and the theorem is
the observation that `f x - g x = g*(y) - f*(y)` squeezes the two inequalities
`⟨x, y⟩ ≤ f x + f*(y)` and `g x + g*(y) ≤ ⟨x, y⟩` together. -/
theorem sub_eq_concaveConj_sub_conj_iff (hpf : Proper f) (hpg : Proper fun z => -(g z)) :
    f x - g x = concaveConj B g y - conj B f y ↔
      y ∈ subgradient B f x ∧ -y ∈ subgradient B (fun z => -(g z)) x := by
  have hgt : g x ≠ ⊤ := fun hc => hpg.ne_bot x (by rw [hc, _root_.EReal.neg_top])
  have hdc : (domConcave g).Nonempty := by
    rw [domConcave_eq_dom_neg]
    exact hpg.dom_nonempty
  rw [sub_eq_sub_iff_of_le (hpf.ne_bot x) hgt (concaveConj_ne_top hdc y)
      (conj_ne_bot hpf.dom_nonempty y) (_root_.EReal.coe_ne_bot _) (_root_.EReal.coe_ne_top _)
      (le_add_conj (hpf.ne_bot x) hpf.dom_nonempty y) (add_concaveConj_le B g x y),
    hpf.mem_subgradient_iff_add_conj_eq, neg_mem_subgradient_neg_iff_add_concaveConj_eq hpg]

/-- **Rockafellar, Theorem 31.3**, first consequence: a point where the primal and dual values
agree already minimises `f - g`. Only weak duality is used, so no hypothesis is needed. -/
theorem iInf_sub_eq_of_sub_eq (h : f x - g x = concaveConj B g y - conj B f y) :
    (⨅ z, f z - g z) = f x - g x :=
  le_antisymm (iInf_le _ x) (le_iInf fun z => by
    rw [h]; exact concaveConj_sub_conj_le_sub B f g z y)

/-- **Rockafellar, Theorem 31.3**, second consequence: the same point maximises `g* - f*`. -/
theorem iSup_sub_eq_of_sub_eq (h : f x - g x = concaveConj B g y - conj B f y) :
    (⨆ w : F, concaveConj B g w - conj B f w) = concaveConj B g y - conj B f y :=
  le_antisymm (iSup_le fun w => by
      rw [← h]; exact concaveConj_sub_conj_le_sub B f g x w)
    (le_iSup (fun w : F => concaveConj B g w - conj B f w) y)

/-- **Rockafellar, Corollary 31.3.1** (with the identity in place of `A`): under exact addition,
`x` minimises `f - g` exactly when it carries a Kuhn–Tucker pair. -/
theorem iInf_sub_eq_iff_exists_kuhnTucker (hex : IsExactSum B f (-g)) (x : E) :
    (⨅ z, f z - g z) = f x - g x ↔
      ∃ y : F, y ∈ subgradient B f x ∧ -y ∈ subgradient B (fun z => -(g z)) x := by
  have hpf : Proper f := hex.proper_left
  have hpg : Proper fun z => -(g z) := hex.proper_right
  constructor
  · intro hmin
    obtain ⟨y, hy⟩ := exists_concaveConj_sub_conj_eq hex
    exact ⟨y, (sub_eq_concaveConj_sub_conj_iff hpf hpg).1 (hmin.symm.trans hy.symm)⟩
  · rintro ⟨y, hy⟩
    exact iInf_sub_eq_of_sub_eq ((sub_eq_concaveConj_sub_conj_iff hpf hpg).2 hy)

end Optimality

/-! ### Optimality conditions for the transformed pair of problems

A pair `(x, z)` is jointly optimal for `inf (f - g A)` and `sup (g* - f* A')` exactly when
`A' z ∈ ∂f x` and `A x` lies in the superdifferential of `g*` at `z`. The superdifferential of a
concave function is `-∂` of its negative, so the second condition reads `-z ∈ ∂(-g)(A x)` and no
new notion is needed.

These are Rockafellar's Kuhn–Tucker conditions for the pair of programs of Theorem 31.2. -/

section OptimalityComp

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {f : E → EReal} {g : G → EReal} {x : E} {z : H}

/-- **Weak duality for the transformed problem**, pointwise: every value of `g* - f* A'` is below
every value of `f - g A`.

Like `concaveConj_sub_conj_le_sub` it needs no hypothesis beyond the adjointness datum, which is
what identifies the two pairings `⟨A x, z⟩'` and `⟨x, A' z⟩` at which the two Fenchel inequalities
are read. -/
theorem concaveConj_sub_conj_comp_le_sub (hA : IsAdjointPair B B' A A') (x : E) (z : H) :
    concaveConj B' g z - conj B f (A' z) ≤ f x - g (A x) := by
  refine sub_le_sub_of_le_sub_of_sub_le (p := B x (A' z)) ?_ (sub_le_conj B f x (A' z))
  rw [← hA x z]
  exact concaveConj_le_sub B' g (A x) z

/-- **Rockafellar, Theorem 31.3**: `x` and `z` are jointly optimal for the two programs of
Theorem 31.2 exactly when they satisfy the Kuhn–Tucker conditions `A' z ∈ ∂f x` and
`-z ∈ ∂(-g)(A x)`.

The proof is the one at `A = id`, with the shared finite value `⟨x, A' z⟩ = ⟨A x, z⟩'`: the
equality `f x - g (A x) = g*(z) - f*(A' z)` squeezes `⟨x, A' z⟩ ≤ f x + f*(A' z)` and
`g (A x) + g*(z) ≤ ⟨A x, z⟩'` together, and each of the two squeezes being tight is Theorem 23.5
for `f`, respectively for `-g`. -/
theorem sub_comp_eq_concaveConj_sub_conj_iff (hA : IsAdjointPair B B' A A') (hpf : Proper f)
    (hpg : Proper fun w => -(g w)) :
    f x - g (A x) = concaveConj B' g z - conj B f (A' z) ↔
      A' z ∈ subgradient B f x ∧ -z ∈ subgradient B' (fun w => -(g w)) (A x) := by
  have hgt : g (A x) ≠ ⊤ := fun hc => hpg.ne_bot (A x) (by rw [hc, _root_.EReal.neg_top])
  have hdc : (domConcave g).Nonempty := by
    rw [domConcave_eq_dom_neg]
    exact hpg.dom_nonempty
  have hp : ((B' (A x) z : ℝ) : EReal) = ((B x (A' z) : ℝ) : EReal) := by rw [hA x z]
  have h2 : g (A x) + concaveConj B' g z ≤ ((B x (A' z) : ℝ) : EReal) := by
    rw [← hp]
    exact add_concaveConj_le B' g (A x) z
  rw [sub_eq_sub_iff_of_le (hpf.ne_bot x) hgt (concaveConj_ne_top hdc z)
      (conj_ne_bot hpf.dom_nonempty (A' z)) (_root_.EReal.coe_ne_bot _)
      (_root_.EReal.coe_ne_top _)
      (le_add_conj (hpf.ne_bot x) hpf.dom_nonempty (A' z)) h2,
    hpf.mem_subgradient_iff_add_conj_eq,
    neg_mem_subgradient_neg_iff_add_concaveConj_eq (B := B') (g := g) (x := A x) (y := z) hpg, hp]

/-- **Rockafellar, Theorem 31.3**, first consequence: a point where the primal and dual values
agree already minimises `f - g A`. Only weak duality is used, so no hypothesis is needed. -/
theorem iInf_sub_comp_eq_of_sub_eq (hA : IsAdjointPair B B' A A')
    (h : f x - g (A x) = concaveConj B' g z - conj B f (A' z)) :
    (⨅ w, f w - g (A w)) = f x - g (A x) :=
  le_antisymm (iInf_le _ x) (le_iInf fun w => by
    rw [h]; exact concaveConj_sub_conj_comp_le_sub hA w z)

/-- **Rockafellar, Theorem 31.3**, second consequence: the same pair maximises `g* - f* A'`. -/
theorem iSup_sub_comp_eq_of_sub_eq (hA : IsAdjointPair B B' A A')
    (h : f x - g (A x) = concaveConj B' g z - conj B f (A' z)) :
    (⨆ w : H, concaveConj B' g w - conj B f (A' w)) = concaveConj B' g z - conj B f (A' z) :=
  le_antisymm (iSup_le fun w => by
      rw [← h]; exact concaveConj_sub_conj_comp_le_sub hA x w)
    (le_iSup (fun w : H => concaveConj B' g w - conj B f (A' w)) z)

/-- **Rockafellar, Corollary 31.3.1**: under Theorem 31.2's two exactness hypotheses, `x`
minimises `f - g A` exactly when it carries a Kuhn–Tucker pair.

The two directions use the two hypotheses asymmetrically: the forward one needs the *attainment*
clause of Theorem 31.2 (`exists_concaveConj_sub_conj_comp_eq`) to produce the multiplier, while
the backward one is weak duality alone. Properness of `-g` is `IsExactImage.proper`; properness of
`f` is `IsExactSum.proper_left`. -/
theorem iInf_sub_comp_eq_iff_exists_kuhnTucker (hA : IsAdjointPair B B' A A')
    (hex : IsExactSum B f fun w => -(g (A w)))
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) (x : E) :
    (⨅ w, f w - g (A w)) = f x - g (A x) ↔
      ∃ z : H, A' z ∈ subgradient B f x ∧ -z ∈ subgradient B' (fun w => -(g w)) (A x) := by
  have hpf : Proper f := hex.proper_left
  have hpg : Proper fun w => -(g w) := himg.proper
  constructor
  · intro hmin
    obtain ⟨z, hz⟩ := exists_concaveConj_sub_conj_comp_eq hA hex himg
    exact ⟨z, (sub_comp_eq_concaveConj_sub_conj_iff hA hpf hpg).1 (hmin.symm.trans hz.symm)⟩
  · rintro ⟨z, hz⟩
    exact iInf_sub_comp_eq_of_sub_eq hA ((sub_comp_eq_concaveConj_sub_conj_iff hA hpf hpg).2 hz)

end OptimalityComp

/-! ### Theorem 31.4: minimising over a convex cone -/

section Cone

open Pointwise

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {K : Set E} {x : E} {y : F}

/-- Rockafellar's `K*` is the *negative* of the polar cone `K°`: the vectors making a non-acute
angle with everything in `K`. `Set` negation is a preimage, so `y ∈ -K°` unfolds to `-y ∈ K°`. -/
theorem mem_neg_polarCone : y ∈ -(polarCone B K) ↔ ∀ z ∈ K, 0 ≤ B z y := by
  simp [Set.mem_neg, mem_polarCone, map_neg]

omit [Module ℝ F] in
/-- Negating a set moves the negation onto the argument of its indicator. -/
private theorem indicatorFn_neg_set (S : Set F) (w : F) :
    indicatorFn (-S) w = indicatorFn S (-w) := by
  by_cases hw : -w ∈ S
  · rw [indicatorFn_of_mem (Set.mem_neg.2 hw), indicatorFn_of_mem hw]
  · rw [indicatorFn_of_notMem fun hc => hw (Set.mem_neg.1 hc), indicatorFn_of_notMem hw]

/-- A constrained infimum is an unconstrained infimum of the function plus an indicator, provided
the function never takes `⊥`. -/
private theorem iInf_mem_eq_iInf_add_indicatorFn {α : Type*} (φ : α → EReal) (S : Set α)
    (hb : ∀ z, φ z ≠ ⊥) : (⨅ z ∈ S, φ z) = ⨅ z, (φ + indicatorFn S) z := by
  refine iInf_congr fun z => ?_
  by_cases hz : z ∈ S
  · rw [iInf_pos hz, Pi.add_apply, indicatorFn_of_mem hz, add_zero]
  · rw [iInf_neg hz, Pi.add_apply, indicatorFn_of_notMem hz]
    exact (_root_.EReal.add_top_of_ne_bot (hb z)).symm

/-- **Rockafellar, Theorem 31.4**: minimising a convex function over a convex cone `K` is dual to
minimising its conjugate over `K* = -K°`.

Rockafellar derives this from Theorem 31.1 with `g = -δ(· | K)`. Here it is cheaper to go straight
to the source both proofs share: Theorem 27.1(a) applied to `f + δ(· | K)`, with the sum's
conjugate split at the origin by `IsExactSum` and `conj_indicatorFn_eq_indicatorFn_polarCone`
(Theorem 14.1) evaluating the second factor. The `0 - y` produced by the splitting is exactly the
sign flip that turns `K°` into `K*`. -/
theorem iInf_add_indicatorFn_eq_neg_iInf_conj_add_indicatorFn
    (hex : IsExactSum B f (indicatorFn K)) (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) :
    (⨅ z, (f + indicatorFn K) z) = -(⨅ w, (conj B f + indicatorFn (-(polarCone B K))) w) := by
  rw [iInf_eq_neg_conj_zero B, hex.conj_add_apply 0, iInf_neg_comp]
  congr 1
  refine iInf_congr fun w => ?_
  rw [Pi.add_apply, conj_indicatorFn_eq_indicatorFn_polarCone hK hne, zero_sub, neg_neg,
    indicatorFn_neg_set]

/-- **Rockafellar, Theorem 31.4**, in the book's own notation:
`inf {f x | x ∈ K} = -inf {f*(y) | y ∈ K*}`. -/
theorem iInf_mem_eq_neg_iInf_mem_neg_polarCone (hex : IsExactSum B f (indicatorFn K))
    (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) :
    (⨅ z ∈ K, f z) = -(⨅ w ∈ -(polarCone B K), conj B f w) := by
  rw [iInf_mem_eq_iInf_add_indicatorFn f K hex.proper_left.ne_bot,
    iInf_mem_eq_iInf_add_indicatorFn (conj B f) _ (conj_ne_bot hex.proper_left.dom_nonempty)]
  exact iInf_add_indicatorFn_eq_neg_iInf_conj_add_indicatorFn hex hK hne

/-- **Weak duality for the cone program**: every dual value is below every primal value. This is
`sub_le_conj` and needs no hypothesis beyond `x ∈ K` and `w ∈ K*`. -/
theorem neg_conj_le_of_mem_neg_polarCone (hxK : x ∈ K) {w : F} (hwK : w ∈ -(polarCone B K)) :
    -(conj B f w) ≤ f x := by
  have hle : -(f x) ≤ conj B f w := by
    refine le_trans (le_of_eq (zero_sub (f x)).symm) (le_trans ?_ (sub_le_conj B f x w))
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add (by exact_mod_cast mem_neg_polarCone.1 hwK x hxK) le_rfl
  rw [← _root_.EReal.neg_le_neg_iff, neg_neg] at hle
  exact hle

/-- `f x + f*(y) = 0` pins `f*(y)` to `-f x`; both values are then finite. -/
private theorem neg_conj_eq_of_add_eq_zero (hp : Proper f) (hz : f x + conj B f y = 0) :
    -(conj B f y) = f x := by
  have hcb : conj B f y ≠ ⊥ := conj_ne_bot hp.dom_nonempty y
  have hfb : f x ≠ ⊥ := hp.ne_bot x
  have hft : f x ≠ ⊤ := fun hc => by
    rw [hc, _root_.EReal.top_add_of_ne_bot hcb] at hz
    exact absurd hz (by simp)
  have hct : conj B f y ≠ ⊤ := fun hc => by
    rw [hc, _root_.EReal.add_top_of_ne_bot hfb] at hz
    exact absurd hz (by simp)
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hfb (lt_top_iff_ne_top.2 hft)
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hcb (lt_top_iff_ne_top.2 hct)
  rw [hr, hs, ← _root_.EReal.coe_add] at hz
  rw [hs, hr, ← _root_.EReal.coe_neg, _root_.EReal.coe_eq_coe_iff]
  have : r + s = 0 := by exact_mod_cast hz
  linarith

/-- **Rockafellar, Theorem 31.4**, the optimality conditions: for `x ∈ K` and `y ∈ K*`, the primal
and dual values agree exactly when `y` is a subgradient of `f` at `x` and `x` is orthogonal to `y`.

Rockafellar reads the conditions off the Kuhn–Tucker conditions of Theorem 31.3 for
`g = -δ(· | K)`, where `x ∈ ∂g*(y)` unfolds to `x ∈ K`, `y ∈ K*` and `⟨x, y⟩ = 0`. -/
theorem add_conj_eq_zero_iff_mem_subgradient_and_pairing_eq_zero (hp : Proper f) (hxK : x ∈ K)
    (hyK : y ∈ -(polarCone B K)) :
    f x + conj B f y = 0 ↔ y ∈ subgradient B f x ∧ (B x y : ℝ) = 0 := by
  have hxy : (0 : ℝ) ≤ B x y := mem_neg_polarCone.1 hyK x hxK
  rw [hp.mem_subgradient_iff_add_conj_eq]
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2, _root_.EReal.coe_zero]⟩
  have hle : ((B x y : ℝ) : EReal) ≤ 0 := h ▸ hp.le_add_conj x y
  have hzero : (B x y : ℝ) = 0 := le_antisymm (by exact_mod_cast hle) hxy
  exact ⟨by rw [h, hzero, _root_.EReal.coe_zero], hzero⟩

/-- **Rockafellar, Theorem 31.4**: the optimality conditions make `x` optimal for the primal cone
program. Only `⟨x, y⟩ = 0` and `y ∈ K*` are used, through
`⟨z - x, y⟩ = ⟨z, y⟩ ≥ 0` for `z ∈ K`. -/
theorem forall_le_of_mem_subgradient_of_pairing_eq_zero (hyK : y ∈ -(polarCone B K))
    (hy : y ∈ subgradient B f x) (hxy : (B x y : ℝ) = 0) {z : E} (hz : z ∈ K) : f x ≤ f z := by
  have hzy : (0 : ℝ) ≤ B (z - x) y := by
    rw [map_sub, LinearMap.sub_apply, hxy, sub_zero]
    exact mem_neg_polarCone.1 hyK z hz
  exact le_trans (le_add_of_nonneg_right (by exact_mod_cast hzy)) (hy z)

/-- **Rockafellar, Theorem 31.4**: the optimality conditions make `y` optimal for the dual cone
program. -/
theorem conj_le_conj_of_mem_subgradient_of_pairing_eq_zero (hp : Proper f) (hxK : x ∈ K)
    (hy : y ∈ subgradient B f x) (hxy : (B x y : ℝ) = 0) {w : F} (hwK : w ∈ -(polarCone B K)) :
    conj B f y ≤ conj B f w := by
  have hsum : f x + conj B f y = 0 := by
    rw [hp.mem_subgradient_iff_add_conj_eq.1 hy, hxy, _root_.EReal.coe_zero]
  have hxeq : -(conj B f y) = f x := neg_conj_eq_of_add_eq_zero hp hsum
  rw [← _root_.EReal.neg_le_neg_iff, hxeq]
  exact neg_conj_le_of_mem_neg_polarCone hxK hwK

end Cone

end Tdaf.ConvexAnalysis
