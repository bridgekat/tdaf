/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Continuity
import Tdaf.Analysis.Convex.Duality.InnerPairing
import Tdaf.Analysis.Convex.Operations.InfConv
import Tdaf.Analysis.Convex.Optimization.Minimum

/-!
# Moreau's decomposition

Rockafellar's Theorem 31.5. For a space paired with itself by a symmetric positive definite form
`B` whose quadratic form is continuous, the quadratic `w z = ½ B z z` is its own conjugate, and
infimal convolution with it splits `w` between a closed proper convex function and its conjugate:

`(f □ w) + (f* □ w) = w`.

## Main results

* `quadFn B` — Rockafellar's `w z = ½ B z z` as an `EReal`-valued function.
* `conj_quadFn` — the quadratic is self-conjugate under its own pairing.
* `conj_quadFn_sub` — `(w(z - ·))*(y) = B z y + w y`, the translate computation the theorem runs
  on.
* `moreau_add` — **Theorem 31.5 (Moreau)**: `(f □ w) z + (f* □ w) z = w z`.
* `infConv_quadFn_ne_top`, `infConv_quadFn_ne_bot` — both Moreau envelopes are finite.

## Design notes

**No concave conjugate appears.** Rockafellar proves Theorem 31.5 by applying Fenchel's duality
theorem to `g x = -w(z - x)` and computing `g*`. Here the same computation is done one level down,
on `conj` itself: `w(z - ·)` is an ordinary convex function, its conjugate is `⟨z, ·⟩ + w`, and the
theorem is Theorem 27.1(a) applied to `f + w(z - ·)` with `IsExactSum.conj_add_apply` splitting the
conjugate at the origin. That is the same route `Fenchel.lean` takes for Theorems 31.1 and 31.4.

**The constraint qualification is continuity, not relative interiors.** `w(z - ·)` is finite and
continuous everywhere, so `IsExactSum.of_continuousAt` applies at any point of `dom f` and the
theorem holds in an arbitrary real Hilbert space — no finite-dimensionality, no `ri`.

**The pairing is general, not an inner product.** Everything here goes through `B` and never
through the norm, so the theorem applies verbatim on `U × X` with
`prodPairing (innerₗ U) (innerₗ X)` — which is what §37 needs, and which has no
`InnerProductSpace` instance because the product carries the supremum norm. `innerₗ E` on a real
inner-product space is the motivating instance and is recovered by `quadFn_innerL`. See
`Duality/InnerPairing.lean`.

**Finiteness is extracted, not assumed.** The final step cancels `(f* □ w) z` from both sides, so
that value has to be a real number. It is: bounded above by evaluating at any point of `dom f*`
(which is nonempty by Theorem 12.2, `proper_conj`), and bounded below because the conjugate at the
origin of `f + w(z - ·)` dominates `-(f x₀ + w(z - x₀))` for `x₀ ∈ dom f`.

## What is not here

**Attainment, uniqueness and the `prox` operator are in `Optimization/Prox.lean`.** Rockafellar's
Theorem 31.5 also says that both infima are *uniquely attained*, that the minimisers `x` and `x*`
are characterised by `z = x + x*` with `x* ∈ ∂f x`, and that they are the gradients of the two
Moreau envelopes. The first two clauses, and Corollaries 31.5.1 and 31.5.2 with them, are proved
in `Optimization/Prox.lean`; attainment is Theorem 27.2, so that file is finite-dimensional where
this one is not.

**The gradient formulas** `x = ∇(f* □ w) z` and `x* = ∇(f □ w) z` are in
`Optimization/MoreauGradient.lean`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §31 (Theorem 31.5).
-/

open RealInnerProductSpace

namespace Tdaf.ConvexAnalysis

/-! ### The quadratic `w z = ½ B z z` -/

section Quadratic

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ}

/-- **Rockafellar's `w`**: `w z = ½ B z z`, as an `EReal`-valued function so that it lives in the
same world as `conj` and `infConv`. -/
noncomputable def quadFn (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E → EReal :=
  fun z => ((B z z / 2 : ℝ) : EReal)

theorem quadFn_apply (z : E) : quadFn B z = ((B z z / 2 : ℝ) : EReal) := rfl

theorem quadFn_ne_bot (z : E) : quadFn B z ≠ ⊥ := _root_.EReal.coe_ne_bot _

theorem quadFn_ne_top (z : E) : quadFn B z ≠ ⊤ := _root_.EReal.coe_ne_top _

@[simp] theorem quadFn_neg (z : E) : quadFn B (-z) = quadFn B z := by
  rw [quadFn_apply, quadFn_apply, self_pairing_neg]

/-- The quadratic translated to the origin is the quadratic: `w (0 - ·) = w`. -/
theorem quadFn_zero_sub : (fun u : E => quadFn B (0 - u)) = quadFn B := by
  funext u
  rw [zero_sub, quadFn_neg]

variable [IsInnerPairing B]

/-- `x ↦ w(z - x)` is a convex function: the defect is `½ a b B (u - v) (u - v) ≥ 0`. -/
theorem convexFn_quadFn_sub (z : E) : ConvexFn (fun x => quadFn B (z - x)) := by
  refine convexFn_of_epi_combo fun x y μ ν hx hy a b ha hb hab => ?_
  rw [quadFn_apply, _root_.EReal.coe_le_coe_iff] at hx hy
  have harg : z - (a • x + b • y) = a • (z - x) + b • (z - y) := by
    rw [smul_sub, smul_sub, ← add_sub_add_comm, ← add_smul, hab, one_smul]
  rw [quadFn_apply, harg, _root_.EReal.coe_le_coe_iff]
  refine le_trans (self_pairing_combo_le ha hb hab) ?_
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

/-- `w` is a convex function. -/
theorem convexFn_quadFn : ConvexFn (quadFn B) := by
  rw [← quadFn_zero_sub]
  exact convexFn_quadFn_sub 0

omit [IsInnerPairing B] in
/-- `x ↦ w(z - x)` is proper: it is finite everywhere. -/
theorem proper_quadFn_sub (z : E) : Proper (fun x => quadFn B (z - x)) :=
  ⟨⟨z, mem_dom.2 (lt_top_iff_ne_top.2 (quadFn_ne_top _))⟩, fun _ => quadFn_ne_bot _⟩

/-- **The quadratic is self-conjugate** under its own pairing: `w* = w`. The supremum
`⨆ x (B x y - ½ B x x)` has defect `½ B (x - y) (x - y)` and is attained at `x = y`. -/
theorem conj_quadFn (y : E) : conj B (quadFn B) y = quadFn B y := by
  rw [conj_apply]
  refine le_antisymm (iSup_le fun x => ?_) ?_
  · rw [quadFn_apply, quadFn_apply, ← _root_.EReal.coe_sub, _root_.EReal.coe_le_coe_iff]
    linarith [self_pairing_sub (B := B) x y, self_pairing_nonneg B (x - y)]
  · refine le_trans (le_of_eq ?_)
      (le_iSup (fun x : E => ((B x y : ℝ) : EReal) - quadFn B x) y)
    rw [quadFn_apply, ← _root_.EReal.coe_sub, _root_.EReal.coe_eq_coe_iff]
    ring

/-- **The conjugate of a translate of the quadratic**: `(w(z - ·))*(y) = B z y + w y`. The
supremum has defect `½ B ((x - z) - y) ((x - z) - y)` and is attained at `x = z + y`. -/
theorem conj_quadFn_sub (z y : E) :
    conj B (fun x => quadFn B (z - x)) y = ((B z y : ℝ) : EReal) + quadFn B y := by
  have hsub : ∀ u : E, B (u - z) y = B u y - B z y := fun u => by
    rw [map_sub, LinearMap.sub_apply]
  rw [conj_apply]
  refine le_antisymm (iSup_le fun x => ?_) ?_
  · rw [quadFn_apply, quadFn_apply, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_add,
      _root_.EReal.coe_le_coe_iff]
    linarith [self_pairing_sub (B := B) (x - z) y, self_pairing_nonneg B (x - z - y), hsub x,
      self_pairing_sub_rev (B := B) z x]
  · refine le_trans (le_of_eq ?_)
      (le_iSup (fun x : E => ((B x y : ℝ) : EReal) - quadFn B (z - x)) (z + y))
    have harg : z - (z + y) = -y := by abel
    have hadd : B (z + y) y = B z y + B y y := by rw [map_add, LinearMap.add_apply]
    rw [harg, quadFn_apply, quadFn_apply, ← _root_.EReal.coe_add, ← _root_.EReal.coe_sub,
      _root_.EReal.coe_eq_coe_iff, hadd, self_pairing_neg]
    ring

end Quadratic

/-! ### The quadratic in a topological space -/

section QuadraticTopology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} [IsContinuousInnerPairing B]

/-- `x ↦ w(z - x)` is continuous, which is the constraint qualification the theorem uses. -/
theorem continuous_quadFn_sub (z : E) : Continuous (fun x => quadFn B (z - x)) := by
  have h : Continuous fun x : E => (B (z - x) (z - x) / 2 : ℝ) :=
    ((continuous_self_pairing' B).comp (continuous_const.sub continuous_id)).div_const 2
  exact continuous_coe_real_ereal.comp h

end QuadraticTopology

/-! ### The inner-product instance -/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On a real inner-product space the general quadratic is Rockafellar's `½|z|²`. -/
@[simp] theorem quadFn_innerL (z : E) : quadFn (innerₗ E) z = ((‖z‖ ^ 2 / 2 : ℝ) : EReal) := by
  rw [quadFn_apply, innerₗ_apply_apply, real_inner_self_eq_norm_sq]

end Inner

/-! ### Theorem 31.5: Moreau's decomposition -/

section Moreau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} [IsContinuousInnerPairing B] [IsCompatiblePairing B] {f : E → EReal}

/-- Reindexing an infimum over a group by `x ↦ z - x`. -/
private theorem iInf_comp_sub {α : Type*} [AddCommGroup α] (φ : α → EReal) (z : α) :
    (⨅ x, φ (z - x)) = ⨅ y, φ y :=
  le_antisymm
    (le_iInf fun y => le_trans (iInf_le (fun x => φ (z - x)) (z - y))
      (le_of_eq (by rw [sub_sub_cancel])))
    (le_iInf fun x => iInf_le φ (z - x))

/-- Reindexing an infimum over a group by negation. -/
private theorem iInf_comp_neg {α : Type*} [AddCommGroup α] (φ : α → EReal) :
    (⨅ y, φ y) = ⨅ y, φ (-y) :=
  le_antisymm (le_iInf fun y => iInf_le φ (-y))
    (le_iInf fun y => le_trans (iInf_le (fun w => φ (-w)) (-y)) (le_of_eq (by rw [neg_neg])))

omit [IsContinuousInnerPairing B] [IsCompatiblePairing B] in
/-- The **Moreau envelope** in Rockafellar's orientation: `(f □ w) z = inf_x {f x + w(z - x)}`. -/
theorem infConv_quadFn_apply (hb : ∀ x, f x ≠ ⊥) (z : E) :
    infConv f (quadFn B) z = ⨅ x, (f x + quadFn B (z - x)) := by
  rw [infConv_apply hb (fun x => quadFn_ne_bot x) z,
    ← iInf_comp_sub (fun y => f (z - y) + quadFn B y) z]
  exact iInf_congr fun x => by rw [sub_sub_cancel]

/-- **Rockafellar, Theorem 31.5 (Moreau)**: infimal convolution with the quadratic splits the
quadratic between `f` and `f*`.

The proof is Theorem 27.1(a) applied to `f + w(z - ·)`, with `IsExactSum.conj_add_apply` splitting
the conjugate of that sum at the origin and `conj_quadFn_sub` evaluating the second factor. The
sign flip `y ↦ -y` produced by the splitting is exactly what turns `⟨z, y⟩ + w y` into
`w(z - y) - w z`. -/
theorem moreau_add (hf : ClosedProperConvexFn f) (z : E) :
    infConv f (quadFn B) z + infConv (conj B f) (quadFn B) z = quadFn B z := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.dom_nonempty
  obtain ⟨y₀, hy₀⟩ := (proper_conj hf (B := B)).dom_nonempty
  have hex : IsExactSum (B) f (fun x => quadFn B (z - x)) :=
    (IsExactSum.of_continuousAt (convexFn_quadFn_sub z) (proper_quadFn_sub z) hf.convex hf.proper
      (mem_dom.2 (lt_top_iff_ne_top.2 (quadFn_ne_top _))) hx₀
      (continuous_quadFn_sub z).continuousAt).symm
  have hD : infConv (conj B f) (quadFn B) z
      = ⨅ y, (conj B f y + quadFn B (z - y)) :=
    infConv_quadFn_apply (conj_ne_bot hf.proper.dom_nonempty) z
  have hP : infConv f (quadFn B) z
      = -(conj B (f + fun x => quadFn B (z - x)) 0) := by
    rw [infConv_quadFn_apply hf.proper.ne_bot z, ← iInf_eq_neg_conj_zero (B)]
    exact iInf_congr fun x => rfl
  have hstep : ∀ y : E,
      conj B f (0 - -y) + conj B (fun x => quadFn B (z - x)) (-y)
        = (conj B f y + quadFn B (z - y)) + ((-(B z z / 2) : ℝ) : EReal) := by
    intro y
    have hinner : B z (-y) = -B z y := by rw [map_neg]
    have hreal : B z (-y) + B y y / 2 = B (z - y) (z - y) / 2 + -(B z z / 2) := by
      rw [hinner]
      have h := self_pairing_sub (B := B) z y
      linarith
    rw [conj_quadFn_sub, zero_sub, neg_neg, quadFn_neg, quadFn_apply, quadFn_apply,
      ← _root_.EReal.coe_add, hreal, _root_.EReal.coe_add, ← add_assoc]
  have hQD : conj B (f + fun x => quadFn B (z - x)) 0
      = infConv (conj B f) (quadFn B) z + ((-(B z z / 2) : ℝ) : EReal) := by
    rw [hex.conj_add_apply 0,
      iInf_comp_neg fun y => conj B f (0 - y)
        + conj B (fun x => quadFn B (z - x)) y,
      hD, Tdaf.EReal.iInf_add_coe]
    exact iInf_congr hstep
  have hDt : infConv (conj B f) (quadFn B) z ≠ ⊤ := by
    rw [hD]
    obtain ⟨r, hr⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (conj_ne_bot hf.proper.dom_nonempty y₀) hy₀
    have hle : (⨅ y, (conj B f y + quadFn B (z - y)))
        ≤ conj B f y₀ + quadFn B (z - y₀) := iInf_le _ y₀
    rw [hr, quadFn_apply, ← _root_.EReal.coe_add] at hle
    exact ne_top_of_le_ne_top (_root_.EReal.coe_ne_top _) hle
  have hQb : conj B (f + fun x => quadFn B (z - x)) 0 ≠ ⊥ := by
    intro hc
    have hle := sub_le_conj B (f + fun x => quadFn B (z - x)) x₀ 0
    rw [hc, le_bot_iff, Tdaf.EReal.coe_sub_eq_bot_iff] at hle
    obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x₀) hx₀
    rw [Pi.add_apply, hp, quadFn_apply, ← _root_.EReal.coe_add] at hle
    exact absurd hle (_root_.EReal.coe_ne_top _)
  have hDb : infConv (conj B f) (quadFn B) z ≠ ⊥ := by
    intro hc
    rw [hc] at hQD
    simp only [_root_.EReal.bot_add] at hQD
    exact hQb hQD
  obtain ⟨d, hd⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hDb (lt_top_iff_ne_top.2 hDt)
  rw [hP, hQD, hd, ← _root_.EReal.coe_add, ← _root_.EReal.coe_neg, ← _root_.EReal.coe_add,
    quadFn_apply, _root_.EReal.coe_eq_coe_iff]
  ring

/-- `⊤ + u` is never a real number. -/
private theorem top_add_ne_coe (u : EReal) (r : ℝ) : ⊤ + u ≠ (r : EReal) := by
  rcases eq_or_ne u ⊥ with rfl | hu
  · rw [_root_.EReal.add_bot]
    exact (_root_.EReal.coe_ne_bot r).symm
  · rw [_root_.EReal.top_add_of_ne_bot hu]
    exact (_root_.EReal.coe_ne_top r).symm

/-- `⊥ + u` is never a real number. -/
private theorem bot_add_ne_coe (u : EReal) (r : ℝ) : ⊥ + u ≠ (r : EReal) := by
  rw [_root_.EReal.bot_add]
  exact (_root_.EReal.coe_ne_bot r).symm

/-- **Rockafellar, Theorem 31.5**: the Moreau envelope of a closed proper convex function is
finite. Both infima in Moreau's identity are real numbers, since their sum is. -/
theorem infConv_quadFn_ne_top (hf : ClosedProperConvexFn f) (z : E) :
    infConv f (quadFn B) z ≠ ⊤ := by
  intro hc
  have h := moreau_add (B := B) hf z
  rw [hc, quadFn_apply] at h
  exact top_add_ne_coe _ _ h

/-- **Rockafellar, Theorem 31.5**: the Moreau envelope never takes `-∞`. -/
theorem infConv_quadFn_ne_bot (hf : ClosedProperConvexFn f) (z : E) :
    infConv f (quadFn B) z ≠ ⊥ := by
  intro hc
  have h := moreau_add (B := B) hf z
  rw [hc, quadFn_apply] at h
  exact bot_add_ne_coe _ _ h

/-- **Rockafellar, Theorem 31.5**: the dual Moreau envelope is finite too. -/
theorem infConv_conj_quadFn_ne_top (hf : ClosedProperConvexFn f) (z : E) :
    infConv (conj B f) (quadFn B) z ≠ ⊤ := by
  intro hc
  have h := moreau_add (B := B) hf z
  rw [hc, _root_.EReal.add_top_of_ne_bot (infConv_quadFn_ne_bot (B := B) hf z), quadFn_apply] at h
  exact absurd h (_root_.EReal.coe_ne_top _).symm

/-- **Rockafellar, Theorem 31.5**: the dual Moreau envelope never takes `-∞`. -/
theorem infConv_conj_quadFn_ne_bot (hf : ClosedProperConvexFn f) (z : E) :
    infConv (conj B f) (quadFn B) z ≠ ⊥ := by
  intro hc
  have h := moreau_add (B := B) hf z
  rw [hc, _root_.EReal.add_bot, quadFn_apply] at h
  exact absurd h (_root_.EReal.coe_ne_bot _).symm

/-- A sum with a real constant that lands on a real number pins the other summand. -/
private theorem eq_coe_of_add_coe_eq_coe {S : EReal} {k m : ℝ}
    (h : S + (k : EReal) = (m : EReal)) : S = ((m - k : ℝ) : EReal) := by
  induction S with
  | bot =>
      rw [_root_.EReal.bot_add] at h
      exact absurd h.symm (_root_.EReal.coe_ne_bot m)
  | coe s =>
      rw [← _root_.EReal.coe_add, _root_.EReal.coe_eq_coe_iff] at h
      rw [_root_.EReal.coe_eq_coe_iff]
      linarith
  | top =>
      rw [_root_.EReal.top_add_of_ne_bot (_root_.EReal.coe_ne_bot k)] at h
      exact absurd h.symm (_root_.EReal.coe_ne_top m)

/-- Two summands neither of which is `⊥` and whose sum is real are both real. -/
private theorem finite_of_add_eq_coe {A C : EReal} (hA : A ≠ ⊥) (hC : C ≠ ⊥) {m : ℝ}
    (h : A + C = (m : EReal)) : A ≠ ⊤ ∧ C ≠ ⊤ := by
  induction A <;> induction C <;> simp_all

/-- **Rockafellar, Theorem 31.5**, the Kuhn–Tucker conditions: for a splitting `z = x + y`, the
pair `(x, y)` attains both infima exactly when `y` is a subgradient of `f` at `x`.

Rockafellar reads this off Theorem 31.3. Here it comes straight from `moreau_add`, because
`(f x + w y) + (f*(y) + w x) = (f x + f*(y)) + (w x + w y)` while `⟨x, y⟩ + w x + w y = w z`. So
Fenchel's inequality makes the left-hand side at least `w z`, which is exactly the sum of the two
infima; equality on the left therefore forces equality in each summand, and conversely.

What is missing from Rockafellar's statement is that such a splitting *exists* and is unique.
Existence is Theorem 27.2 in a Hilbert space, uniqueness is strict convexity of `w`. -/
theorem mem_subgradient_iff_infConv_eq (hf : ClosedProperConvexFn f) {x y z : E}
    (hz : x + y = z) :
    y ∈ subgradient (B) f x ↔
      f x + quadFn B y = infConv f (quadFn B) z ∧
        conj B f y + quadFn B x = infConv (conj B f) (quadFn B) z := by
  have hzx : z - x = y := by rw [← hz]; abel
  have hzy : z - y = x := by rw [← hz]; abel
  have hPle : infConv f (quadFn B) z ≤ f x + quadFn B y := by
    rw [infConv_quadFn_apply hf.proper.ne_bot z, ← hzx]
    exact iInf_le _ x
  have hDle : infConv (conj B f) (quadFn B) z ≤ conj B f y + quadFn B x := by
    rw [infConv_quadFn_apply (conj_ne_bot hf.proper.dom_nonempty) z, ← hzy]
    exact iInf_le _ y
  have hreal : B y y / 2 + B x x / 2 = B x x / 2 + B y y / 2 := by ring
  have hkey : (f x + quadFn B y) + (conj B f y + quadFn B x)
      = (f x + conj B f y) + ((B x x / 2 + B y y / 2 : ℝ) : EReal) := by
    rw [add_add_add_comm, quadFn_apply, quadFn_apply, ← _root_.EReal.coe_add, hreal]
  have hwz : ((B x y : ℝ) : EReal) + ((B x x / 2 + B y y / 2 : ℝ) : EReal) = quadFn B z := by
    rw [← _root_.EReal.coe_add, quadFn_apply, ← hz, _root_.EReal.coe_eq_coe_iff]
    have h := self_pairing_add (B := B) x y
    linarith
  constructor
  · intro hmem
    have hfen : f x + conj B f y = ((B x y : ℝ) : EReal) :=
      hf.proper.mem_subgradient_iff_add_conj_eq.1 hmem
    have hsum : (f x + quadFn B y) + (conj B f y + quadFn B x)
        = infConv f (quadFn B) z + infConv (conj B f) (quadFn B) z := by
      rw [hkey, hfen, hwz, moreau_add (B := B) hf z]
    obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (infConv_quadFn_ne_bot (B := B) hf z)
      (lt_top_iff_ne_top.2 (infConv_quadFn_ne_top (B := B) hf z))
    obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (infConv_conj_quadFn_ne_bot (B := B) hf z)
      (lt_top_iff_ne_top.2 (infConv_conj_quadFn_ne_top (B := B) hf z))
    have hAb : f x + quadFn B y ≠ ⊥ := by
      intro hcon
      rw [hcon, le_bot_iff, hp] at hPle
      exact absurd hPle (_root_.EReal.coe_ne_bot p)
    have hCb : conj B f y + quadFn B x ≠ ⊥ := by
      intro hcon
      rw [hcon, le_bot_iff, hq] at hDle
      exact absurd hDle (_root_.EReal.coe_ne_bot q)
    obtain ⟨hAt, hCt⟩ := finite_of_add_eq_coe hAb hCb
      (m := p + q) (by rw [hsum, hp, hq, ← _root_.EReal.coe_add])
    obtain ⟨a, ha⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hAb (lt_top_iff_ne_top.2 hAt)
    obtain ⟨c, hcc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hCb (lt_top_iff_ne_top.2 hCt)
    rw [hp, ha, _root_.EReal.coe_le_coe_iff] at hPle
    rw [hq, hcc, _root_.EReal.coe_le_coe_iff] at hDle
    rw [ha, hcc, hp, hq, ← _root_.EReal.coe_add, ← _root_.EReal.coe_add,
      _root_.EReal.coe_eq_coe_iff] at hsum
    refine ⟨?_, ?_⟩
    · rw [ha, hp, _root_.EReal.coe_eq_coe_iff]
      linarith
    · rw [hcc, hq, _root_.EReal.coe_eq_coe_iff]
      linarith
  · rintro ⟨h1, h2⟩
    have hsum : (f x + conj B f y) + ((B x x / 2 + B y y / 2 : ℝ) : EReal)
        = ((B z z / 2 : ℝ) : EReal) := by
      rw [← hkey, h1, h2, moreau_add hf z, quadFn_apply]
    rw [hf.proper.mem_subgradient_iff_add_conj_eq, eq_coe_of_add_coe_eq_coe hsum,
      _root_.EReal.coe_eq_coe_iff, ← hz]
    have h := self_pairing_add (B := B) x y
    linarith

end Moreau

end Tdaf.ConvexAnalysis
