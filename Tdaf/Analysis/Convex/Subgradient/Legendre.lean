/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Subgradient.Gradient

/-!
# The Legendre transformation

Rockafellar's §26. The Legendre conjugate of a differentiable convex function `f` on an open set
`C` is the pair `(D, g)` with `D = ∇f(C)` and `g(y) = ⟨x, y⟩ - f x` for any `x` with `∇f x = y`.
**Theorem 26.4** says that this is well-defined and that `g` is nothing but the restriction of the
Fenchel conjugate `f*` to `D`.

## Main results

* `legendreDom` — Rockafellar's `D`, the image of the gradient mapping.
* `HasGradientAt.add_conj_eq` — **Theorem 26.4**, the engine: Fenchel's inequality is an equality
  at `(x, ∇f x)`.
* `conj_eq_of_hasGradientAt` — **Theorem 26.4**, the formula `f*(∇f x) = ⟨x, ∇f x⟩ - f x`. Since
  the right-hand side is *defined* to be the Legendre conjugate at `∇f x`, this is the statement
  "`g` is the restriction of `f*` to `D`", and it makes `g` well-defined at a stroke.
* `sub_eq_sub_of_hasGradientAt` — **Theorem 26.4**, well-definedness spelt out: `⟨x, y⟩ - f x` does
  not depend on which `x` in `(∇f)⁻¹ y` is used.
* `legendreDom_subset_dom_conj` — **Theorem 26.4**: `D ⊆ dom f*`.

## Design notes

**There is no `legendreConj` definition here, on purpose.** Rockafellar's `g` is
`y ↦ ⟨(∇f)⁻¹ y, y⟩ - f ((∇f)⁻¹ y)`, a formula that is only well-defined *because* of Theorem 26.4;
writing it down in Lean would need a choice function and would then have to be proved equal to
`conj B f` on `D` anyway. `conj_eq_of_hasGradientAt` is that equality, stated without the detour,
and it is the form every application uses.

**`f x` is finite wherever `∇f x` exists**, by `HasGradientAt.exists_coe`, so the real-valued
statements carry an explicit `hr : f x = (r : EReal)` rather than a `toReal`.

## What is not here

**Theorem 26.1 is blocked, and with it the rest of §26.** "∂f single-valued ⟺ `f` essentially
smooth" needs two things this backbone does not have:

* `∂f x` a singleton ⇒ `f` differentiable at `x`. This is the sufficiency half of Theorem 25.2,
  i.e. Gâteaux ⇒ Fréchet, which is genuinely finite-dimensional (see `Gradient.lean`).
* at a boundary point of `int (dom f)` with `∂f x ≠ ∅`, a sequence `xᵢ → x` with `∇f xᵢ` bounded.
  Rockafellar gets this from **Theorem 25.6**, which rests on Theorem 25.5 (Rademacher) and on
  §24's convergence theory (Theorems 10.6–10.9), none of which is done.

Consequently `EssentiallySmooth`, `EssentiallyStrictlyConvex` and `LegendreType` are **not defined
here**. Definitions whose theorems are all out of reach cannot be tested, and §18 already showed
what an untested guess costs: `IsExtreme` was assumed to be Rockafellar's *face* and is not. They
belong in the same commit as Theorem 26.1. Theorem 26.3 (essential strict convexity ⟺ conjugate
essentially smooth), Corollaries 26.3.1–26.3.3, Corollary 26.4.1, Theorem 26.5 (the involutory
Legendre correspondence) and Theorem 26.6 with Lemma 26.7 all route through Theorem 26.1.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §26 (Theorem 26.4).
-/

open Set Filter Topology

namespace Tdaf.ConvexAnalysis

section Legendre

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {x : E}
  {y : StrongDual ℝ E}

/-- Solving `r + c = s` for `c` in `EReal`, where `r` and `s` are real: the two infinities are
excluded by the equation itself. -/
private theorem eq_coe_of_coe_add_eq_coe {c : EReal} {r s : ℝ}
    (h : ((r : ℝ) : EReal) + c = ((s : ℝ) : EReal)) : c = ((s - r : ℝ) : EReal) := by
  rcases eq_or_ne c ⊤ with rfl | hct
  · simp at h
  rcases eq_or_ne c ⊥ with rfl | hcb
  · simp at h
  obtain ⟨t, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hcb (lt_top_iff_ne_top.2 hct)
  rw [← _root_.EReal.coe_add, _root_.EReal.coe_eq_coe_iff] at h
  rw [_root_.EReal.coe_eq_coe_iff]
  linarith

/-- A function is finite wherever it has a gradient. -/
theorem HasGradientAt.exists_coe (h : HasGradientAt f y x) : ∃ r : ℝ, f x = ((r : ℝ) : EReal) := by
  obtain ⟨g, hfg, -⟩ := h
  exact ⟨g x, hfg.self_of_nhds⟩

/-- **Rockafellar, Theorem 26.4**, the engine: at a point where `f` is differentiable, Fenchel's
inequality holds with equality at `(x, ∇f x)`.

This is Theorem 23.5 (d) applied to `∇f x ∈ ∂f x`, which is Theorem 25.1. -/
theorem HasGradientAt.add_conj_eq (hf : ConvexFn f) (h : HasGradientAt f y x) :
    f x + conj (topDualPairing ℝ E).flip f y = ((y x : ℝ) : EReal) :=
  (h.proper hf).mem_subgradient_iff_add_conj_eq.1 (h.mem_subgradient hf)

/-- **Rockafellar, Theorem 26.4**: the Legendre conjugate at `∇f x` *is* `f*` at `∇f x`, and the
formula defining it is `⟨x, ∇f x⟩ - f x`. -/
theorem conj_eq_of_hasGradientAt (hf : ConvexFn f) (h : HasGradientAt f y x) {r : ℝ}
    (hr : f x = ((r : ℝ) : EReal)) :
    conj (topDualPairing ℝ E).flip f y = ((y x - r : ℝ) : EReal) :=
  eq_coe_of_coe_add_eq_coe (by rw [← hr]; exact h.add_conj_eq hf)

/-- **Rockafellar, Theorem 26.4**, well-definedness: `⟨x, y⟩ - f x` is the same for every `x` with
`∇f x = y`, because it is `f* y`. Rockafellar notes that `∇f` need not be one-to-one for the
Legendre conjugate to be single-valued, and this is why. -/
theorem sub_eq_sub_of_hasGradientAt (hf : ConvexFn f) {x₁ x₂ : E} {r₁ r₂ : ℝ}
    (h₁ : HasGradientAt f y x₁) (h₂ : HasGradientAt f y x₂)
    (hr₁ : f x₁ = ((r₁ : ℝ) : EReal)) (hr₂ : f x₂ = ((r₂ : ℝ) : EReal)) :
    y x₁ - r₁ = y x₂ - r₂ := by
  have he : ((y x₁ - r₁ : ℝ) : EReal) = ((y x₂ - r₂ : ℝ) : EReal) := by
    rw [← conj_eq_of_hasGradientAt hf h₁ hr₁, ← conj_eq_of_hasGradientAt hf h₂ hr₂]
  exact_mod_cast he

/-- The **domain of the Legendre conjugate**: Rockafellar's `D`, the image of `int (dom f)` under
the gradient mapping. Every gradient is attained at an interior point of `dom f`
(`HasGradientAt.mem_interior_dom`), so no interiority side condition is needed in the definition. -/
def legendreDom (f : E → EReal) : Set (StrongDual ℝ E) := {y | ∃ x, HasGradientAt f y x}

theorem mem_legendreDom_iff : y ∈ legendreDom f ↔ ∃ x, HasGradientAt f y x := Iff.rfl

theorem HasGradientAt.mem_legendreDom (h : HasGradientAt f y x) : y ∈ legendreDom f := ⟨x, h⟩

/-- Every point of `D` is `∇f x` for an `x` in the interior of `dom f`. -/
theorem exists_mem_interior_dom_of_mem_legendreDom (hy : y ∈ legendreDom f) :
    ∃ x ∈ interior (dom f), HasGradientAt f y x := by
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx.mem_interior_dom, hx⟩

/-- **Rockafellar, Theorem 26.4**: `D ⊆ dom f*`. -/
theorem legendreDom_subset_dom_conj (hf : ConvexFn f) :
    legendreDom f ⊆ dom (conj (topDualPairing ℝ E).flip f) := by
  rintro y ⟨x, hx⟩
  obtain ⟨r, hr⟩ := hx.exists_coe
  rw [mem_dom, conj_eq_of_hasGradientAt hf hx hr]
  exact _root_.EReal.coe_lt_top _

end Legendre

end Tdaf.ConvexAnalysis
