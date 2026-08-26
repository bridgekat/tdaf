/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Closure
import Tdaf.Analysis.Convex.Operations.Image

/-!
# Closedness of the functional operations

The inverse image of a closed function under a continuous linear map is closed: the closedness half
of Rockafellar's Theorem 5.7, whose convexity half is `convexFn_compLin`. The supporting
`lowerSemicontinuous_comp` precomposes a lower semicontinuous `g` with a continuous `φ`; Mathlib's
`Continuous.comp_lowerSemicontinuous` composes on the other side.

Closedness is not lower semicontinuity — `ClosedFn` also admits the constant `⊥` — and that branch
survives precomposition because `(fun _ => ⊥) ∘ A` is again constant.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §5, §7.
-/

namespace Tdaf.ConvexAnalysis

section Comp

variable {E G : Type*} [TopologicalSpace E] [TopologicalSpace G] {g : G → EReal}

/-- Lower semicontinuity is preserved by precomposition with a continuous map. -/
theorem lowerSemicontinuous_comp (hg : LowerSemicontinuous g) {φ : E → G} (hφ : Continuous φ) :
    LowerSemicontinuous (g ∘ φ) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  exact (hg.isOpen_preimage y).preimage hφ

end Comp

section CompLin

variable {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace G] [IsTopologicalAddGroup G]
  {A : E →ₗ[ℝ] G} {g : G → EReal}

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup G] in
theorem lowerSemicontinuous_compLin (hg : LowerSemicontinuous g) (hA : Continuous A) :
    LowerSemicontinuous (compLin g A) :=
  lowerSemicontinuous_comp hg hA

/-- The inverse image of a closed function under a continuous linear map is closed: the closedness
half of **Rockafellar, Theorem 5.7**. -/
theorem closedFn_compLin (hg : ClosedFn g) (hA : Continuous A) : ClosedFn (compLin g A) := by
  rcases closedFn_iff.1 hg with rfl | ⟨hlsc, hne⟩
  · exact closedFn_iff.2 (Or.inl rfl)
  · exact closedFn_iff.2 (Or.inr ⟨lowerSemicontinuous_compLin hlsc hA, fun x => hne (A x)⟩)

end CompLin

end Tdaf.ConvexAnalysis
