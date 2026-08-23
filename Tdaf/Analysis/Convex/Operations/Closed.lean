/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Closure
import Tdaf.Analysis.Convex.Operations.Image

/-!
# Closedness of the functional operations

`Operations/Image.lean` is a layer-A file: it knows `mapLin` and `compLin` but no topology. This
file is its layer-B companion, and currently carries one fact — that taking the **inverse image**
of a closed function under a continuous linear map gives a closed function.

## Main results

* `lowerSemicontinuous_comp` — the composition `g ∘ φ` of a lower semicontinuous `g` with a
  *continuous* `φ` is lower semicontinuous.
* `closedFn_compLin` — `ClosedFn g → Continuous A → ClosedFn (compLin g A)`.

## Design notes

**Mathlib has the other composition.** `Continuous.comp_lowerSemicontinuous` composes on the
*outside*: `g ∘ f` is lower semicontinuous when `f` is lower semicontinuous and `g` is continuous
and monotone. What is needed here is composition on the *inside*, `g ∘ φ` with `φ` continuous and
`g` lower semicontinuous, which is not in Mathlib and is three lines from
`lowerSemicontinuous_iff_isOpen_preimage` — the preimage of `g ⁻¹' Ioi y` under `φ` is open.

**Closedness is not lower semicontinuity, so the constant `⊥` needs its own branch.**
`closedFn_iff` splits into "`g` is the constant `⊥`" and "`g` is lower semicontinuous and never
`⊥`"; both branches survive precomposition, the first because `(fun _ => ⊥) ∘ A` is again constant.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §5 (Theorem 5.7) and §7.
-/

namespace Tdaf.ConvexAnalysis

section Comp

variable {E G : Type*} [TopologicalSpace E] [TopologicalSpace G] {g : G → EReal}

/-- **Lower semicontinuity is preserved by precomposition with a continuous map.** Mathlib has the
opposite composition (`Continuous.comp_lowerSemicontinuous`), not this one. -/
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

/-- **The inverse image of a closed function under a continuous linear map is closed.** This is the
closedness half of Rockafellar's Theorem 5.7; `convexFn_compLin` is the convexity half. -/
theorem closedFn_compLin (hg : ClosedFn g) (hA : Continuous A) : ClosedFn (compLin g A) := by
  rcases closedFn_iff.1 hg with rfl | ⟨hlsc, hne⟩
  · exact closedFn_iff.2 (Or.inl rfl)
  · exact closedFn_iff.2 (Or.inr ⟨lowerSemicontinuous_compLin hlsc hA, fun x => hne (A x)⟩)

end CompLin

end Tdaf.ConvexAnalysis
