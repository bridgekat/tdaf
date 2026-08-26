/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Exact
import Tdaf.Analysis.Convex.Subgradient.Defs

/-!
# Subgradient calculus

Rockafellar's §23.8–§23.10: how `∂` interacts with sums and with linear maps.

Both rules have the same shape. One inclusion is unconditional — a subgradient of each piece
assembles into a subgradient of the whole — and the reverse inclusion, which is the useful one,
needs exactly the constraint qualification that makes the corresponding conjugacy rule exact. So
both are stated against the [`IsExactSum`/`IsExactImage`](../Duality/Exact.lean) interfaces of §16.
Rockafellar's `ri` versions of Theorems 23.8 and 23.9 are these two theorems composed with
[`of_relint`](../Duality/Relint.lean); the polyhedral version (§20) and the continuity version
(§10) will follow the same way once those constructors exist.

## Main results

* `subgradient_add_subset`, `IsExactSum.subgradient_add` — **Theorem 23.8** for two summands.
* `subgradient_finsetSum_subset`, `IsExactFinsetSum.subgradient_finsetSum` — **Theorem 23.8** in
  the book's own `m`-ary form.
* `image_subgradient_subset`, `IsExactImage.subgradient_compLin` — **Theorem 23.9**.
* `subgradient_coe_mul`, `subgradient_zero_mul`, `subgradient_coe_affineMap`,
  `subgradient_coe_mul_affineMap` — the scaling rules: `∂(cf) = c ∂f` for `c > 0` and for
  *arbitrary* `c` when `f` is affine, together with the two singletons those two collapse to.
* `normalCone_add_subset`, `IsExactSum.normalCone_inter` — **Corollary 23.8.1**, the indicator
  instance.
* `subgradient_add_normalCone_dom_subset`, `normalCone_dom_eq_zero_of_subgradient_eq_singleton` —
  the normal cone to `dom f`, and what a *unique* subgradient does to it.

## Design notes

**Theorem 23.5 does all the work.** `mem_subgradient_iff_add_conj_le` says `y ∈ ∂f x` is
`f x + f* y ≤ ⟨x, y⟩`, unconditionally — Fenchel's inequality holding *with equality*, written so
that no `∞ - ∞` can arise. Both calculus rules then reduce to arithmetic on that one inequality, and
neither proof ever mentions an epigraph, a directional derivative or a separating hyperplane.

**The sum rule needs a genuine `EReal` fact, the image rule does not.** For sums the exact-sum
hypothesis gives one *joint* equality in Fenchel's inequality, and splitting it into the two
separate equalities is `Tdaf.EReal.le_coe_of_add_le_coe_add` — two slack inequalities whose sum is
tight must each be tight; for `m` summands it is `Tdaf.EReal.le_coe_of_sum_le_coe_sum`, which is a
lemma in its own right because the two-summand version does not iterate (there is no subtraction on
`EReal` to peel a summand off with). That is where the properness in `IsExactSum` is spent. The
image rule has
no splitting to do, and spends its properness on a single point instead: it must know `g (A x) ≠ ⊥`
to see that `(g A)* y` is finite, which is what unlocks the `< ⊤`-guarded `IsExactImage.exact_le`.

**The scaling rules pay for their singletons with a separation hypothesis.** `∂(cf) = c ∂f` for
`c > 0` needs nothing at all — it is a reversible inequality. The two statements that name a
*single point*, `subgradient_zero_mul` and `subgradient_coe_affineMap`, need `B.flip` injective,
because without it `{y | ∀ w, B w y = 0}` is a subspace rather than the origin. That hypothesis is
free in every normed space (`separatingRight_flip_of_separatingDual`), and it is the same one
`subgradient_eq_singleton_of_dirDeriv_eq` takes one file up.

**Theorem 23.10 is in `Subgradient/Existence.lean`.** It asks for `∂f x ≠ ∅` at every point of
`dom f` for polyhedral `f`, which is a *nonemptiness* statement rather than a calculus rule, so it
belongs with Theorem 23.4 (`subgradient_nonempty_of_polyhedralFn`,
`polyhedral_subgradient_of_polyhedralFn`).

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §23 (Theorem 23.8,
  Corollary 23.8.1, Theorem 23.9).
-/

open Pointwise

namespace Tdaf.ConvexAnalysis

/-! ### Theorem 23.8: sums -/

section Add

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- **Rockafellar, Theorem 23.8**, the unconditional inclusion: a subgradient of `f` plus a
subgradient of `g` is a subgradient of `f + g`.

No hypothesis at all — the two subgradient inequalities simply add. -/
theorem subgradient_add_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) (x : E) :
    subgradient B f x + subgradient B g x ⊆ subgradient B (f + g) x := by
  rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩ z
  have h₁ := hy₁ z
  have h₂ := hy₂ z
  rw [Pi.add_apply, Pi.add_apply, map_add, _root_.EReal.coe_add, add_add_add_comm]
  exact add_le_add h₁ h₂

/-- **Rockafellar, Theorem 23.8**: `∂(f + g) x = ∂f x + ∂g x` whenever the sum is exact.

The reverse inclusion is `subgradient_add_subset` and needs nothing. For this one, `y ∈ ∂(f+g) x`
makes Fenchel's inequality tight for `f + g` at `y`, exactness produces a splitting `y = y₁ + y₂`
whose conjugate values already add up to `(f+g)* y`, and the two Fenchel inequalities for `f` at
`y₁` and for `g` at `y₂` then have no room left to be strict. -/
theorem IsExactSum.subgradient_add (h : IsExactSum B f g) (x : E) :
    subgradient B (f + g) x = subgradient B f x + subgradient B g x := by
  refine Set.Subset.antisymm (fun y hy => ?_) (subgradient_add_subset B f g x)
  obtain ⟨y₁, y₂, rfl, hle⟩ := h.exact_le y
  have hy' := mem_subgradient_iff_add_conj_le.1 hy
  rw [Pi.add_apply] at hy'
  have hkey : (f x + conj B f y₁) + (g x + conj B g y₂)
      ≤ ((B x y₁ + B x y₂ : ℝ) : EReal) := by
    calc (f x + conj B f y₁) + (g x + conj B g y₂)
        = (f x + g x) + (conj B f y₁ + conj B g y₂) := (add_add_add_comm _ _ _ _).symm
      _ ≤ (f x + g x) + conj B (f + g) (y₁ + y₂) := add_le_add le_rfl hle
      _ ≤ ((B x (y₁ + y₂) : ℝ) : EReal) := hy'
      _ = ((B x y₁ + B x y₂ : ℝ) : EReal) := by rw [map_add]
  have hkey' : (g x + conj B g y₂) + (f x + conj B f y₁)
      ≤ ((B x y₂ + B x y₁ : ℝ) : EReal) := by
    rw [add_comm (g x + conj B g y₂), add_comm (B x y₂)]
    exact hkey
  have hf := h.proper_left.le_add_conj (B := B) x y₁
  have hg := h.proper_right.le_add_conj (B := B) x y₂
  exact ⟨y₁, mem_subgradient_iff_add_conj_le.2
      (Tdaf.EReal.le_coe_of_add_le_coe_add hf hg hkey),
    y₂, mem_subgradient_iff_add_conj_le.2
      (Tdaf.EReal.le_coe_of_add_le_coe_add hg hf hkey'), rfl⟩

end Add

/-! ### Theorem 23.8 for `m` summands -/

section FinsetAdd

variable {ι E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Finset ι} {f : ι → E → EReal}

/-- **Rockafellar, Theorem 23.8** in the book's own `m`-ary form, unconditional inclusion:
`∂f₁ x + ⋯ + ∂fₘ x ⊆ ∂(f₁ + ⋯ + fₘ) x`.

No hypothesis at all — the `m` subgradient inequalities simply add. Over the empty `Finset` the
left side is `{0}` and the right side is `∂(0) x`, which contains `0`. -/
theorem subgradient_finsetSum_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Finset ι)
    (f : ι → E → EReal) (x : E) :
    ∑ i ∈ s, subgradient B (f i) x ⊆ subgradient B (∑ i ∈ s, f i) x := by
  induction s using Finset.cons_induction with
  | empty =>
    intro y hy
    simp only [Finset.sum_empty, Set.mem_zero] at hy
    subst hy
    simp [mem_subgradient]
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (Set.add_subset_add_left ih).trans (subgradient_add_subset B (f i) _ x)

/-- **Rockafellar, Theorem 23.8**: `∂(f₁ + ⋯ + fₘ) x = ∂f₁ x + ⋯ + ∂fₘ x` whenever the family adds
exactly.

This is the form Rockafellar states, and it is **not** the binary rule iterated. Going through
`IsExactSum.subgradient_add` would mean re-deriving properness and the constraint qualification for
every partial sum `f₁ + ⋯ + fₖ`, which is exactly what `IsExactFinsetSum.cons` exists to do once;
the argument below is run for the family, in one pass.

That argument is Rockafellar's own. Exactness hands back a splitting `y = y₁ + ⋯ + yₘ` whose
conjugate values already sum to `(∑ fᵢ)* y`; Fenchel's inequality gives `⟨x, yᵢ⟩ ≤ fᵢ x + fᵢ* yᵢ`
for each `i`; and `y ∈ ∂(∑ fᵢ) x` makes the *sum* of those `m` inequalities tight, so
`Tdaf.EReal.le_coe_of_sum_le_coe_sum` makes each of them tight. That lemma is the `m`-ary form of
the `EReal` fact the binary rule spends its properness on. -/
theorem IsExactFinsetSum.subgradient_finsetSum (h : IsExactFinsetSum B s f) (x : E) :
    subgradient B (∑ i ∈ s, f i) x = ∑ i ∈ s, subgradient B (f i) x := by
  refine Set.Subset.antisymm (fun y hy => ?_) (subgradient_finsetSum_subset B s f x)
  obtain ⟨y', hy', hle⟩ := h.exact_le y
  have hfen : ∀ i ∈ s, ((B x (y' i) : ℝ) : EReal) ≤ f i x + conj B (f i) (y' i) :=
    fun i hi => (h.proper i hi).le_add_conj x (y' i)
  have hsum : ∑ i ∈ s, (f i x + conj B (f i) (y' i))
      ≤ ((∑ i ∈ s, B x (y' i) : ℝ) : EReal) := by
    calc ∑ i ∈ s, (f i x + conj B (f i) (y' i))
        = (∑ i ∈ s, f i) x + ∑ i ∈ s, conj B (f i) (y' i) := by
          rw [Finset.sum_add_distrib, Finset.sum_apply]
      _ ≤ (∑ i ∈ s, f i) x + conj B (∑ i ∈ s, f i) y := add_le_add le_rfl hle
      _ ≤ ((B x y : ℝ) : EReal) := mem_subgradient_iff_add_conj_le.1 hy
      _ = ((∑ i ∈ s, B x (y' i) : ℝ) : EReal) := by rw [← hy', map_sum]
  have hmem : ∀ i ∈ s, y' i ∈ subgradient B (f i) x := fun i hi =>
    mem_subgradient_iff_add_conj_le.2
      (Tdaf.EReal.le_coe_of_sum_le_coe_sum (c := fun i => B x (y' i))
        (u := fun i => f i x + conj B (f i) (y' i)) hfen hsum hi)
  have hgoal := Set.finsetSum_mem_finsetSum s (fun i => subgradient B (f i) x) y' hmem
  rwa [hy'] at hgoal

end FinsetAdd

/-! ### Theorem 23.9: linear maps -/

section Image

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

/-- **Rockafellar, Theorem 23.9**, the unconditional inclusion: the transpose carries subgradients
of `g` at `A x` to subgradients of `g A` at `x`.

Only the adjointness datum is used; `g` is arbitrary. -/
theorem image_subgradient_subset (hA : IsAdjointPair B B' A A') (g : G → EReal) (x : E) :
    A' '' subgradient B' g (A x) ⊆ subgradient B (compLin g A) x := by
  rintro _ ⟨z, hz, rfl⟩ w
  have hw := hz (A w)
  rwa [compLin_apply, compLin_apply, ← hA (w - x) z, map_sub]

/-- **Rockafellar, Theorem 23.9**: `∂(g A) x = A' (∂g (A x))` whenever the pullback is exact.

Unlike the sum rule this direction needs no splitting and no `EReal` case analysis on the *values*:
exactness hands back a single `z` in the fibre with `g* z ≤ (g A)* (A' z)`, and that inequality
slots straight into Fenchel's. The one piece of work is discharging the `< ⊤` guard on
`IsExactImage.exact_le`: a subgradient at `x` forces `(g A)* y` to be finite, because `g (A x)` is
never `⊥` and `⊥ ≠ g (A x) + ⊤ ≤ ⟨x, y⟩` is impossible. -/
theorem IsExactImage.subgradient_compLin {hA : IsAdjointPair B B' A A'}
    (h : IsExactImage B B' A A' hA g) (x : E) :
    subgradient B (compLin g A) x = A' '' subgradient B' g (A x) := by
  refine Set.Subset.antisymm (fun y hy => ?_) (image_subgradient_subset hA g x)
  have hne : compLin g A x ≠ ⊥ := by rw [compLin_apply]; exact h.proper.ne_bot (A x)
  have hfin : conj B (compLin g A) y < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    have hsub := mem_subgradient_iff_add_conj_le.1 hy
    rw [htop, _root_.EReal.add_top_of_ne_bot hne, top_le_iff] at hsub
    exact absurd hsub (_root_.EReal.coe_ne_top _)
  obtain ⟨z, rfl, hle⟩ := h.exact_le y hfin
  refine ⟨z, mem_subgradient_iff_add_conj_le.2 ?_, rfl⟩
  calc g (A x) + conj B' g z
      ≤ g (A x) + conj B (compLin g A) (A' z) := add_le_add le_rfl hle
    _ = compLin g A x + conj B (compLin g A) (A' z) := by rw [compLin_apply]
    _ ≤ ((B x (A' z) : ℝ) : EReal) := mem_subgradient_iff_add_conj_le.1 hy
    _ = ((B' (A x) z : ℝ) : EReal) := by rw [hA x z]

end Image

/-! ### Scalar multiples -/

section Smul

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

/-- **`∂(cf) x = c ∂f x` for `c > 0`**, with no hypothesis on `f` whatever.

Rockafellar uses this without comment at §28, line 11169, where `c` is the Lagrange multiplier of
an inequality constraint. The whole content is `Tdaf.EReal.coe_mul_add_coe_le_coe_mul_iff`:
multiplying the subgradient inequality through by `c > 0` is reversible even on `EReal`, and the
pairing scales in its second argument by linearity.

Positivity is essential in both directions. At `c = 0` the left side is `{y | ∀ w, B w y = 0}`,
which is `{0}` for a separating pairing (`subgradient_zero_mul`) and has nothing to do with
`∂f x`; for `c < 0` the scaled inequality reverses and `cf` is *concave* where `f` is convex.
The negative case survives only when `f` is affine — `subgradient_coe_mul_affineMap`. -/
theorem subgradient_coe_mul {c : ℝ} (hc : 0 < c) (f : E → EReal) (x : E) :
    subgradient B (fun y => (c : EReal) * f y) x = c • subgradient B f x := by
  ext v
  constructor
  · intro hv
    refine ⟨c⁻¹ • v, fun z => ?_, ?_⟩
    swap
    · change c • (c⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    have h1 := hv z
    have hp : B (z - x) (c⁻¹ • v) = c⁻¹ * B (z - x) v := by rw [map_smul, smul_eq_mul]
    rw [hp]
    refine (Tdaf.EReal.coe_mul_add_coe_le_coe_mul_iff hc (f x) (f z) _).1 ?_
    rw [show c * (c⁻¹ * B (z - x) v) = B (z - x) v from by field_simp]
    exact h1
  · rintro ⟨w, hw, rfl⟩
    intro z
    have hp : B (z - x) (c • w) = c * B (z - x) w := by rw [map_smul, smul_eq_mul]
    rw [hp]
    exact (Tdaf.EReal.coe_mul_add_coe_le_coe_mul_iff hc (f x) (f z) _).2 (hw z)

/-- **`∂(0 · f) x = {0}`**: the zero function has the origin as its only subgradient.

This is what Rockafellar's parenthesis "(Omit terms with `λᵢ = 0`.)" in Theorem 28.3 (c) means, and
it is why the omission is not cosmetic: `∂fᵢ x` may be *empty* at a boundary point of `dom fᵢ`, so
the term `0 · ∂fᵢ x` that the parenthesis drops would be `∅` rather than `{0}` and would empty the
whole sum.

`Function.Injective B.flip` is exactly what turns `{y | ∀ w, B w y = 0}` into a single point; it is
the hypothesis `subgradient_eq_singleton_of_dirDeriv_eq` (`Subgradient/Gradient.lean`) takes, and
it is free in a normed space — `LinearMap.separatingRight_iff_flip_ker_eq_bot` applied to
`separatingRight_flip_of_separatingDual` (`Duality/Level.lean`). -/
theorem subgradient_zero_mul (hB : Function.Injective B.flip) (f : E → EReal) (x : E) :
    subgradient B (fun y => ((0 : ℝ) : EReal) * f y) x = {(0 : F)} := by
  have hz : (fun y => ((0 : ℝ) : EReal) * f y) = fun _ : E => (0 : EReal) := by
    funext y; rw [_root_.EReal.coe_zero, zero_mul]
  rw [hz]
  ext v
  rw [Set.mem_singleton_iff]
  constructor
  · intro hv
    have hle : ∀ w : E, B w v ≤ 0 := by
      intro w
      have h := hv (x + w)
      rw [add_sub_cancel_left, zero_add] at h
      have h' : ((B w v : ℝ) : EReal) ≤ (0 : EReal) := h
      exact_mod_cast h'
    refine hB (LinearMap.ext fun w => ?_)
    change B w v = B w 0
    rw [map_zero]
    refine le_antisymm (hle w) ?_
    have hneg := hle (-w)
    rw [map_neg B w, LinearMap.neg_apply] at hneg
    linarith
  · rintro rfl
    intro z
    rw [zero_add, map_zero]
    exact le_of_eq (by norm_num)

/-- **The subdifferential of an affine function is one point**, namely the vector `b` representing
its linear part through the pairing.

This is the affine case of Rockafellar's Theorem 23.2 — where a function is differentiable its
subdifferential is the singleton of its gradient — and here no differentiation is needed: `b` is
handed in, together with the Riesz identity `⟨w, b⟩ = a.linear w` that names it. A normed caller
gets `b` from `InnerProductSpace.toDual` or from `exists_linFn`; nothing in the statement mentions
a topology.

Both hypotheses are used exactly once: the identity, to see that `b` *is* a subgradient, and the
injectivity of `B.flip`, to see that nothing else is. -/
theorem subgradient_coe_affineMap (hB : Function.Injective B.flip) (a : E →ᵃ[ℝ] ℝ) {b : F}
    (hb : ∀ w : E, B w b = a.linear w) (x : E) :
    subgradient B (fun y => ((a y : ℝ) : EReal)) x = {b} := by
  have hdec : ∀ z : E, a z - a x = a.linear (z - x) := by
    intro z
    have h1 : ∀ y : E, a y = a.linear y + a 0 := fun y => congrFun (AffineMap.decomp a) y
    rw [h1 z, h1 x, map_sub]
    ring
  ext v
  rw [Set.mem_singleton_iff]
  constructor
  · intro hv
    have hle : ∀ w : E, B w v ≤ a.linear w := by
      intro w
      have h := hv (w + x)
      rw [add_sub_cancel_right, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at h
      have hd := hdec (w + x)
      rw [add_sub_cancel_right] at hd
      linarith
    refine hB (LinearMap.ext fun w => ?_)
    change B w v = B w b
    rw [hb w]
    refine le_antisymm (hle w) ?_
    have hneg := hle (-w)
    rw [map_neg B w, LinearMap.neg_apply, map_neg a.linear w] at hneg
    linarith
  · rintro rfl
    intro z
    rw [← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff, hb (z - x)]
    linarith [hdec z]

/-- **`∂(ca) x = c ∂a x` for an *arbitrary* real `c`, when `a` is affine.**

`subgradient_coe_mul` needs `0 < c` because scaling reverses the subgradient inequality. An affine
function satisfies that inequality with *equality*, so nothing reverses, and the equality-constraint
multipliers of §28 — which may be negative — are covered. Both sides are computed rather than
compared: each is a singleton, by `subgradient_coe_affineMap` applied to `a` and to `c • a`. -/
theorem subgradient_coe_mul_affineMap (hB : Function.Injective B.flip) (c : ℝ) (a : E →ᵃ[ℝ] ℝ)
    {b : F} (hb : ∀ w : E, B w b = a.linear w) (x : E) :
    subgradient B (fun y => (c : EReal) * ((a y : ℝ) : EReal)) x
      = c • subgradient B (fun y => ((a y : ℝ) : EReal)) x := by
  have hfun : (fun y => (c : EReal) * ((a y : ℝ) : EReal))
      = fun y => (((c • a) y : ℝ) : EReal) := by
    funext y
    rw [Tdaf.EReal.coe_mul_coe]
    rfl
  have hb' : ∀ w : E, B w (c • b) = (c • a).linear w := by
    intro w
    rw [map_smul, smul_eq_mul, hb w]
    rfl
  rw [hfun, subgradient_coe_affineMap hB (c • a) hb' x, subgradient_coe_affineMap hB a hb x,
    Set.smul_set_singleton]

end Smul

/-! ### Corollary 23.8.1: normal cones to an intersection -/

section NormalCone

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C D : Set E} {x : E}

/-- **Rockafellar, Corollary 23.8.1**, the unconditional inclusion. Proved directly rather than
through indicators, so that it needs neither `x ∈ C` nor `x ∈ D`. -/
theorem normalCone_add_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C D : Set E) (x : E) :
    normalCone B C x + normalCone B D x ⊆ normalCone B (C ∩ D) x := by
  rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩ z hz
  rw [map_add]
  exact add_nonpos (hy₁ z hz.1) (hy₂ z hz.2)

/-- **Rockafellar, Corollary 23.8.1**: the normal cone to an intersection is the sum of the normal
cones, under the exact-sum hypothesis for the two indicators.

This is Theorem 23.8 read through `indicatorFn_add` (`δ(·|C) + δ(·|D) = δ(·|C ∩ D)`, with no side
condition) and `subgradient_indicatorFn`. -/
theorem IsExactSum.normalCone_inter (h : IsExactSum B (indicatorFn C) (indicatorFn D))
    (hC : x ∈ C) (hD : x ∈ D) :
    normalCone B (C ∩ D) x = normalCone B C x + normalCone B D x := by
  have hsum := h.subgradient_add x
  rwa [indicatorFn_add, subgradient_indicatorFn (Set.mem_inter hC hD),
    subgradient_indicatorFn hC,
    subgradient_indicatorFn hD] at hsum

end NormalCone

/-! ### The normal cone to the effective domain -/

section NormalConeDom

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E}

/-- **A normal to the effective domain may be added to a subgradient.** This is the elementary
inclusion behind Rockafellar's `∂f x + N_{dom f}(x) = ∂f x`, and it needs neither convexity nor a
topology: outside `dom f` the subgradient inequality reads `≤ ⊤`, and inside it the added term is
`≤ 0`. -/
theorem subgradient_add_normalCone_dom_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) :
    subgradient B f x + normalCone B (dom f) x ⊆ subgradient B f x := by
  rintro _ ⟨y, hy, n, hn, rfl⟩ z
  by_cases hz : z ∈ dom f
  · have hle : ((B (z - x) (y + n) : ℝ) : EReal) ≤ ((B (z - x) y : ℝ) : EReal) := by
      rw [map_add, _root_.EReal.coe_le_coe_iff]
      linarith [hn z hz]
    exact (add_le_add (le_refl (f x)) hle).trans (hy z)
  · rw [top_le_iff.1 (not_lt.1 fun h => hz (mem_dom.2 h))]
    exact le_top

/-- **A lone subgradient leaves no room for a normal direction.** If `∂f x` is the single point
`y₀` then `y₀ + n` is again a subgradient for every `n` normal to `dom f` at `x`, so `n = 0`.

This is the step that turns uniqueness of the subgradient into an *interior* statement: with
`mem_interior_of_normalCone_eq_zero` it says that a convex function with a unique subgradient at
`x` has `x` interior to its effective domain. -/
theorem normalCone_dom_eq_zero_of_subgradient_eq_singleton {y₀ : F}
    (h : subgradient B f x = {y₀}) : normalCone B (dom f) x = {0} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨fun z _ => by simp, fun n hn => ?_⟩
  have hy₀ : y₀ ∈ subgradient B f x := by rw [h]; rfl
  have hmem := subgradient_add_normalCone_dom_subset B f x (Set.add_mem_add hy₀ hn)
  rw [h, Set.mem_singleton_iff] at hmem
  simpa using hmem

end NormalConeDom

end Tdaf.ConvexAnalysis
