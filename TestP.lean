import Tdaf.Analysis.Convex.Duality.Level

open Tdaf.ConvexAnalysis

section
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B]

example : LocallyConvexSpace ℝ (ℝ × E) := inferInstance
example : IsTopologicalAddGroup (ℝ × E) := inferInstance
example : ContinuousSMul ℝ (ℝ × E) := inferInstance
example : IsCompatiblePairing (innerₗ ℝ) := inferInstance
example : IsCompatiblePairing (prodPairing (innerₗ ℝ) B) := inferInstance
example : IsCompatiblePairing (prodPairing (innerₗ ℝ) B).flip.flip := inferInstance
example (a b : ℝ) : innerₗ ℝ a b = a * b := by simp
end
