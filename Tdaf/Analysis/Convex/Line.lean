/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Function

/-!
# Convexity along a line

Restricting a function to a line through `x` in direction `d` — `t ↦ f (x + t • d)`, on the set of
steps that keep the point inside `S` — preserves convexity, and for convex `S` it **detects** it.

The forward direction is a one-line computation; the converse is what makes the reduction useful,
because it turns a statement about a function on a vector space into a statement about functions of
one real variable, where the whole calculus of a single derivative applies. That is how the
second-derivative criterion for convexity on `ℝⁿ` is proved from the one on an interval.

## Main results

* `convexOn_comp_line`, `concaveOn_comp_line` — the restriction stays convex, resp. concave.
* `convexOn_iff_lines`, `concaveOn_iff_lines` — for convex `S`, the restrictions detect convexity.
* `isOpen_line_steps` — the step set is open when `S` is.
* `continuousAt_comp_line_of_convexOn`, `…_of_concaveOn` — continuity along a line through an
  interior point.

## Design notes

**The step set is `{t | x + t • d ∈ S}`, not an interval.** It *is* an interval when `S` is convex,
but saying so requires the convexity hypothesis, and the forward lemmas do not need it. Leaving the
set in preimage form also makes `isOpen_line_steps` a one-liner.

**The converse takes the direction to be `y - x`.** Given two points of `S`, the segment between
them is the image of `[0, 1]` under `t ↦ x + t • (y - x)`, so a single line carries the whole
convexity inequality for that pair. No hypothesis on `d` is needed, and none is imposed.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970 — §4, where the reduction
  to lines is what carries the second-derivative criterion (Theorem 4.4) up to `ℝⁿ` (Theorem 4.5).
-/

namespace Tdaf.ConvexAnalysis

/-! ### The restriction to a line -/

section Line

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E} {f : E → ℝ} {x d : E}

/-- A convex function stays convex along a line: `t ↦ f (x + t • d)` is convex on the set of
steps that keep `x + t • d` inside `S`.

The proof is the identity `x + (a t₁ + b t₂) • d = a • (x + t₁ • d) + b • (x + t₂ • d)`, valid
because `a + b = 1`. -/
theorem convexOn_comp_line (hf : ConvexOn ℝ S f) (x d : E) :
    ConvexOn ℝ {t : ℝ | x + t • d ∈ S} fun t => f (x + t • d) := by
  have key : ∀ a b t₁ t₂ : ℝ, a + b = 1 →
      x + (a • t₁ + b • t₂) • d = a • (x + t₁ • d) + b • (x + t₂ • d) := by
    intro a b t₁ t₂ hab
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, hab, one_smul,
      smul_eq_mul, smul_eq_mul, ← add_smul]
  constructor
  · intro t₁ h₁ t₂ h₂ a b ha hb hab
    change x + (a • t₁ + b • t₂) • d ∈ S
    rw [key a b t₁ t₂ hab]
    exact hf.1 h₁ h₂ ha hb hab
  · intro t₁ h₁ t₂ h₂ a b ha hb hab
    change f (x + (a • t₁ + b • t₂) • d) ≤ a • f (x + t₁ • d) + b • f (x + t₂ • d)
    rw [key a b t₁ t₂ hab]
    exact hf.2 h₁ h₂ ha hb hab

/-- A concave function stays concave along a line. This is `convexOn_comp_line` for `-f`. -/
theorem concaveOn_comp_line (hf : ConcaveOn ℝ S f) (x d : E) :
    ConcaveOn ℝ {t : ℝ | x + t • d ∈ S} fun t => f (x + t • d) :=
  neg_convexOn_iff.1 (convexOn_comp_line hf.neg x d)

/-- **The restrictions to lines detect convexity.** For convex `S`, `f` is convex on `S` exactly
when every line restriction is convex on its step set.

The converse direction is the useful one: it is what lets a criterion for convexity of a function
of one real variable be lifted to `E`. Given `x, y ∈ S`, the line through `x` in direction `y - x`
carries the convexity inequality for that pair, with steps `0` and `1`. -/
theorem convexOn_iff_lines (hS : Convex ℝ S) :
    ConvexOn ℝ S f ↔ ∀ x d : E, ConvexOn ℝ {t : ℝ | x + t • d ∈ S} fun t => f (x + t • d) := by
  refine ⟨fun hf x d => convexOn_comp_line hf x d,
    fun h => ⟨hS, fun {x} hx {y} hy a b ha hb hab => ?_⟩⟩
  have h0 : (0 : ℝ) ∈ {t : ℝ | x + t • (y - x) ∈ S} := by simpa using hx
  have h1 : (1 : ℝ) ∈ {t : ℝ | x + t • (y - x) ∈ S} := by simpa using hy
  -- The type ascription is what beta-reduces `(fun t => f (x + t • (y - x))) (a • 0 + b • 1)`;
  -- without it `rw` cannot see through the redex.
  have hmain : f (x + (a • (0 : ℝ) + b • (1 : ℝ)) • (y - x))
      ≤ a • f (x + (0 : ℝ) • (y - x)) + b • f (x + (1 : ℝ) • (y - x)) :=
    (h x (y - x)).2 h0 h1 ha hb hab
  have e1 : a • (0 : ℝ) + b • (1 : ℝ) = b := by simp
  have e2 : x + (0 : ℝ) • (y - x) = x := by simp
  have e3 : x + (1 : ℝ) • (y - x) = y := by simp
  rw [e1, e2, e3] at hmain
  have hpt : x + b • (y - x) = a • x + b • y := by
    have ha' : a = 1 - b := by linarith
    subst ha'
    module
  rwa [hpt] at hmain

/-- The concave form of `convexOn_iff_lines`. -/
theorem concaveOn_iff_lines (hS : Convex ℝ S) :
    ConcaveOn ℝ S f ↔ ∀ x d : E, ConcaveOn ℝ {t : ℝ | x + t • d ∈ S} fun t => f (x + t • d) :=
  ⟨fun hf x d => concaveOn_comp_line hf x d,
    fun h => neg_convexOn_iff.1 ((convexOn_iff_lines hS).2 fun x d => neg_convexOn_iff.2 (h x d))⟩

end Line

/-! ### Topology along a line -/

section LineTopology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E] {S : Set E} {f : E → ℝ} {x d : E}

/-- The steps `t` with `x + t • d ∈ S` form an open set when `S` is open. -/
theorem isOpen_line_steps (hS : IsOpen S) (x d : E) : IsOpen {t : ℝ | x + t • d ∈ S} :=
  hS.preimage (continuous_const.add (continuous_id.smul continuous_const))

/-- A convex function is continuous along a line through an interior point of the set on which it
is convex: this is the one-dimensional case of `ConvexOn.continuousOn`. -/
theorem continuousAt_comp_line_of_convexOn (hS : IsOpen S) (hf : ConvexOn ℝ S f) (hx : x ∈ S)
    (d : E) : ContinuousAt (fun t : ℝ => f (x + t • d)) 0 := by
  have hI : IsOpen {t : ℝ | x + t • d ∈ S} := isOpen_line_steps hS x d
  have h0 : (0 : ℝ) ∈ {t : ℝ | x + t • d ∈ S} := by simpa using hx
  exact ((convexOn_comp_line hf x d).continuousOn hI).continuousAt (hI.mem_nhds h0)

/-- A concave function is continuous along a line through an interior point. -/
theorem continuousAt_comp_line_of_concaveOn (hS : IsOpen S) (hf : ConcaveOn ℝ S f) (hx : x ∈ S)
    (d : E) : ContinuousAt (fun t : ℝ => f (x + t • d)) 0 := by
  have hI : IsOpen {t : ℝ | x + t • d ∈ S} := isOpen_line_steps hS x d
  have h0 : (0 : ℝ) ∈ {t : ℝ | x + t • d ∈ S} := by simpa using hx
  exact ((concaveOn_comp_line hf x d).continuousOn hI).continuousAt (hI.mem_nhds h0)

end LineTopology

end Tdaf.ConvexAnalysis
