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
* `sub_eq_concaveConj_sub_conj_iff` — **Theorem 31.3**, the Kuhn–Tucker conditions `y ∈ ∂f x` and
  `-y ∈ ∂(-g) x`, with `iInf_sub_eq_iff_exists_kuhnTucker` for **Corollary 31.3.1**.

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

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §31 (Theorem 31.1).
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

/-- **Weak duality**, pointwise: every dual value is below every primal value. This is Fenchel's
inequality for `f` and Fenchel's inequality for `g` added together.

No hypothesis at all is needed. Both `∞ - ∞` collisions are already absorbed on the correct side:
if `f x = ⊥` then `f* y = ⊤` and the left side is `⊥`, and if `g x = ⊤` then `g* y = ⊥` and the
left side is `⊥` again. -/
theorem concaveConj_sub_conj_le_sub (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) (x : E) (y : F) :
    concaveConj B g y - conj B f y ≤ f x - g x := by
  set p : EReal := ((B x y : ℝ) : EReal) with hp
  have hpb : p ≠ ⊥ := _root_.EReal.coe_ne_bot _
  have hpt : p ≠ ⊤ := _root_.EReal.coe_ne_top _
  have h1 : concaveConj B g y ≤ p - g x := concaveConj_le_sub B g x y
  have h2 : p - f x ≤ conj B f y := sub_le_conj B f x y
  have h3 : -(conj B f y) ≤ f x - p := by
    refine le_trans (_root_.EReal.neg_le_neg_iff.2 h2) (le_of_eq ?_)
    rw [_root_.EReal.neg_sub (.inl hpb) (.inl hpt), sub_eq_add_neg, add_comm]
  have hsum : concaveConj B g y + -(conj B f y) ≤ (p - g x) + (f x - p) := add_le_add h1 h3
  refine le_trans (le_of_eq (sub_eq_add_neg _ _)) (le_trans hsum (le_of_eq ?_))
  rw [sub_eq_add_neg p (g x), sub_eq_add_neg (f x) p, add_comm (f x) (-p),
    add_add_add_comm p (-(g x)) (-p) (f x)]
  have hpp : p + -p = 0 := by
    rw [hp, ← _root_.EReal.coe_neg, ← _root_.EReal.coe_add, add_neg_cancel, _root_.EReal.coe_zero]
  rw [hpp, zero_add, add_comm (-(g x)) (f x), sub_eq_add_neg]

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
