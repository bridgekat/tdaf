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

* `subgradient_add_subset`, `IsExactSum.subgradient_add` — **Theorem 23.8**.
* `image_subgradient_subset`, `IsExactImage.subgradient_compLin` — **Theorem 23.9**.
* `normalCone_add_subset`, `IsExactSum.normalCone_inter` — **Corollary 23.8.1**, the indicator
  instance.

## Design notes

**Theorem 23.5 does all the work.** `mem_subgradient_iff_add_conj_le` says `y ∈ ∂f x` is
`f x + f* y ≤ ⟨x, y⟩`, unconditionally — Fenchel's inequality holding *with equality*, written so
that no `∞ - ∞` can arise. Both calculus rules then reduce to arithmetic on that one inequality, and
neither proof ever mentions an epigraph, a directional derivative or a separating hyperplane.

**The sum rule needs a genuine `EReal` fact, the image rule does not.** For sums the exact-sum
hypothesis gives one *joint* equality in Fenchel's inequality, and splitting it into the two
separate equalities is `Tdaf.EReal.le_coe_of_add_le_coe_add` — two slack inequalities whose sum is
tight must each be tight. That is where the properness in `IsExactSum` is spent. The image rule has
no splitting to do, and spends its properness on a single point instead: it must know `g (A x) ≠ ⊥`
to see that `(g A)* y` is finite, which is what unlocks the `< ⊤`-guarded `IsExactImage.exact_le`.

**Theorem 23.10 is not here.** It asks for `∂f x ≠ ∅` at every point of `dom f` for polyhedral `f`,
and `PolyhedralFn` (§19) does not exist yet. It is a *nonemptiness* statement rather than a calculus
rule, and belongs with Theorem 23.4.

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

end Tdaf.ConvexAnalysis
