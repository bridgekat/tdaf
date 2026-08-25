/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Subspaces: the affine hull of a set through the origin

A set containing the origin has the same affine hull and linear hull. Mathlib has the general
`vectorSpan_eq_span_vsub_set_right`, which subtracts a chosen base point; when that base point can
be taken to be `0` the subtraction disappears and the two hulls coincide on the nose.

This is a Mathlib gap, not convex analysis: nothing below mentions convexity, and it is stated for
an arbitrary module. It lives here rather than in `Analysis/Convex/` because the duality theory is
not the only consumer — a cone, a subspace and an affine set all reach for it, and the surface layer
needs it in `§1` before any convexity has been introduced.

## Main results

* `vectorSpan_eq_span_of_zero_mem` — `vectorSpan ℝ C = Submodule.span ℝ C` when `0 ∈ C`.
* `vectorSpan_eq_of_affineSpan_eq` — equal affine hulls give equal directions, hence equal
  dimensions.

## Not here

**Extending an isomorphism between two subspaces to the ambient space is Mathlib's**
`Submodule.exists_linearEquiv_restrict_eq` (`Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`):
given `f : W ≃ₗ[K] W'` with `W` finite-dimensional it produces `g : V ≃ₗ[K] V` with `f x = g x` on
`W`. It was independently rewritten in the surface layer before anyone found it — the name contains
neither "extend" nor "automorphism", so only a semantic search finds it. See
`docs/plans/convex-analysis/gotchas.md` DEP4.
-/

namespace Tdaf

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- For a set containing the origin the affine hull and the linear hull agree.

This is **Rockafellar, Theorem 1.1** in the form its consumers use it: the affine sets through the
origin are exactly the subspaces. -/
theorem vectorSpan_eq_span_of_zero_mem {C : Set E} (h0 : (0 : E) ∈ C) :
    vectorSpan K C = Submodule.span K C := by
  rw [vectorSpan_eq_span_vsub_set_right K h0]
  congr 1
  ext x
  simp

/-- **Sets with the same affine hull have the same direction.** The affine hull determines the
`vectorSpan` — it *is* its direction — so this is one `congrArg`, and it is the step behind every
"these two sets have the same dimension" argument: `finrank` of both sides then agrees.

Rockafellar's Corollary 6.3.1 (`cl C` and `ri C` have the same dimension as `C`) is this lemma
applied to the affine-hull equalities that Theorem 6.3 supplies. -/
theorem vectorSpan_eq_of_affineSpan_eq {S T : Set E}
    (h : affineSpan K S = affineSpan K T) : vectorSpan K S = vectorSpan K T := by
  rw [← direction_affineSpan K S, ← direction_affineSpan K T, h]

end Tdaf
