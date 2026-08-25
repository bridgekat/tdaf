/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Continuity
import Tdaf.Analysis.Convex.Convergence
import Tdaf.Analysis.Convex.Duality.Conjugate
import Tdaf.Analysis.Convex.Duality.InnerPairing
import Tdaf.Analysis.Convex.Duality.Relint
import Tdaf.Analysis.Convex.Operations.Basic
import Tdaf.Analysis.Convex.Recession.Cone
import Tdaf.Analysis.Convex.Simplicial
import Tdaf.Analysis.Convex.Subgradient.Defs
import Tdaf.LinearAlgebra.Subspace
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.TFAE

/-!
# The Euclidean instantiation shared by every `ℝⁿ` surface

`Rn n` is `EuclideanSpace ℝ (Fin n)` and `pairing n` is its own inner product read as a bilinear
map. Together they instantiate all four generality layers of the backbone at once, which is why a
textbook written in `ℝⁿ` can state everything without qualification.

This module is **not** tied to any one book. Rockafellar's surface, Boyd–Vandenberghe's and any
other `ℝⁿ` text want the same ambient setting and the same instance discharge; putting it here means
a gap gets closed once rather than once per surface.

## Main definitions

* `Rn n` — the ambient space.
* `pairing n` — the self-pairing `⟨x, y⟩`, as a `LinearMap` so that the backbone's duality applies.

## Main results

* `pairing_apply` — the pairing is the inner product.
* `flip_pairing` — the pairing is its own flip, so no statement needs `(pairing n).flip` in a form
  instance search cannot see.
* `conj_flip_pairing`, `subgradient_flip_pairing`, `supportSet_flip_pairing`,
  `supportFn_flip_pairing`, `polarCone_flip_pairing`, `polarSet_flip_pairing` — the places a
  `.flip` survives into a statement, rewritten away once here rather than at every call site. On a
  self-paired space every bipolar theorem hands one back, and `flip_pairing` is a `simp` lemma but
  not a `rfl`, so `exact` fails where these make it succeed.
* `linFn`, `exists_linFn` — the Fréchet–Riesz translation between the book's vector `b` and the
  backbone's continuous linear functional.

## Design notes

**A textbook in `ℝⁿ` identifies a space with its dual**, writing `x*` for a vector of the same
space. This module honours that by taking both sides of the pairing to be `Rn n`, so the `*` of the
book becomes a naming convention and not a type distinction. That identification is exactly what the
backbone refuses to make — `Duality/Pairing.lean` keeps `E` and `F` apart precisely so the general
theory cannot silently use self-duality — and it is safe to make *here*, where the book has made it.

**Everything below is `inferInstance`.** The section is an assertion, not a construction: it records
which classes are available, so that a later change to the backbone that breaks one of them fails
here, in a twelve-line file, rather than in whichever surface statement happened to need it. Two of
these were genuine gaps found by the plan review and closed in `Duality/Pairing.lean`: the negated
pairings `-B`, `(-B).flip`, and the sign-flipped product pairing `negFst (prodPairing Bu Bx)` that
§30's adjoint is conjugated against.

**The import list is the surface's shared header, not a minimal one.** A section that needs a
Mathlib or backbone module the four original imports did not reach used to import it itself, and
five of the ten sections written so far did. The ones that recurred are here: `Continuity`,
`Convergence`, `Simplicial` and `Operations.Basic` from the backbone; `Mathlib.Tactic.TFAE`, which
any section transcribing a book "the following are equivalent" needs; `Mathlib.Analysis.Convex.Join`
for `Convex.convexHull_union`; and `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional`, which
every section that counts dimensions wants. Adding one here costs a rebuild of the surface and
saves a section from discovering an "unknown constant" that is really a missing import.

**`pairingProd` is not `Rn (m + n)`.** Rockafellar moves freely between `ℝᵐ × ℝⁿ` and `ℝᵐ⁺ⁿ`; those
are different types here, and the transport between them is separate work (remediation §4.8). What
this module supplies is the pairing on the *product*, which is what the backbone's bifunction
theory is stated against.
-/

namespace Tdaf.Surface

open Tdaf.ConvexAnalysis

/-- The ambient space of a finite-dimensional real surface: `ℝⁿ` with its Euclidean structure. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The **standard inner product** on `Rn n`, as a bilinear map, which is the form the backbone's
duality theory takes. A book that writes `⟨x, x*⟩` for vectors of one space means this.

`abbrev`, not `def`: instance search does not unfold a plain `def`, and every pairing class the
surface needs is stated about `innerₗ`. As a `def` this module does not even get
`IsInnerPairing (pairing n)`. -/
noncomputable abbrev pairing (n : ℕ) : Rn n →ₗ[ℝ] Rn n →ₗ[ℝ] ℝ := innerₗ (Rn n)

@[simp] theorem pairing_apply {n : ℕ} (x y : Rn n) : pairing n x y = inner ℝ x y := rfl

/-- The pairing is symmetric, hence its own flip. Every backbone statement that asks for
`B.flip` therefore asks for `pairing n` again, and this is the rewrite that says so. -/
@[simp] theorem flip_pairing (n : ℕ) : (pairing n).flip = pairing n :=
  flip_eq_self (pairing n)

/-- The **product pairing** on `Rn m × Rn n`, which is what a bifunction from `ℝᵐ` to `ℝⁿ` is
conjugated against. -/
noncomputable abbrev pairingProd (m n : ℕ) : (Rn m × Rn n) →ₗ[ℝ] (Rn m × Rn n) →ₗ[ℝ] ℝ :=
  prodPairing (pairing m) (pairing n)

/-- The **sign-flipped product pairing** of §30: the one Rockafellar's adjoint `F*` of a convex
bifunction is stated against. -/
noncomputable abbrev pairingAdjoint (m n : ℕ) : (Rn m × Rn n) →ₗ[ℝ] (Rn m × Rn n) →ₗ[ℝ] ℝ :=
  negFst (pairingProd m n)

/-! ### Instance discharge

Each `example` asserts that a class the surface will need is found by instance search with no
hypothesis. They are not used; they are the regression test for the instantiation. -/

section Instances

variable {m n : ℕ}

-- Ambient structure on `Rn n`.
noncomputable example : NormedAddCommGroup (Rn n) := inferInstance
noncomputable example : InnerProductSpace ℝ (Rn n) := inferInstance
noncomputable example : NormedSpace ℝ (Rn n) := inferInstance
example : FiniteDimensional ℝ (Rn n) := inferInstance
example : CompleteSpace (Rn n) := inferInstance
example : ProperSpace (Rn n) := inferInstance
example : T2Space (Rn n) := inferInstance
example : LocallyConvexSpace ℝ (Rn n) := inferInstance
example : IsTopologicalAddGroup (Rn n) := inferInstance
example : ContinuousSMul ℝ (Rn n) := inferInstance
example : TopologicalSpace.SeparableSpace (Rn n) := inferInstance
example : SeparatingDual ℝ (Rn n) := inferInstance

-- The self-pairing, and the flips the backbone asks for.
example : IsInnerPairing (pairing n) := inferInstance
example : IsContinuousInnerPairing (pairing n) := inferInstance
example : IsContinuousPairing (pairing n) := inferInstance
example : IsCompatiblePairing (pairing n) := inferInstance
example : IsContinuousPairing (pairing n).flip := inferInstance
example : IsCompatiblePairing (pairing n).flip := inferInstance
example : IsCompatiblePairing (pairing n).flip.flip := inferInstance

-- Negated pairings: §34 and §37 conjugate against these.
example : IsContinuousPairing (-pairing n) := inferInstance
example : IsCompatiblePairing (-pairing n) := inferInstance
example : IsCompatiblePairing (-pairing n).flip := inferInstance

-- Product pairings: §29–§30, §37.
example : IsInnerPairing (pairingProd m n) := inferInstance
example : IsContinuousPairing (pairingProd m n) := inferInstance
example : IsCompatiblePairing (pairingProd m n) := inferInstance
example : IsContinuousPairing (pairingProd m n).flip := inferInstance
example : IsCompatiblePairing (pairingProd m n).flip := inferInstance

-- The adjoint pairing of §30, the last gap the plan review found.
example : IsContinuousPairing (pairingAdjoint m n) := inferInstance
example : IsCompatiblePairing (pairingAdjoint m n) := inferInstance
example : IsContinuousPairing (pairingAdjoint m n).flip := inferInstance
example : IsCompatiblePairing (pairingAdjoint m n).flip := inferInstance

end Instances

/-! ### Rewriting `.flip` away

`flip_pairing` is a `simp` lemma, but a `.flip` inside a `conj` or a `subgradient` sits under a
binder that `simp` will not always reach in a surface proof. These are the two forms that occur. -/

section Flip

variable {n : ℕ}

@[simp] theorem conj_flip_pairing (f : Rn n → EReal) :
    conj (pairing n).flip f = conj (pairing n) f := by
  rw [flip_pairing]

@[simp] theorem subgradient_flip_pairing (f : Rn n → EReal) (x : Rn n) :
    subgradient (pairing n).flip f x = subgradient (pairing n) f x := by
  rw [flip_pairing]

@[simp] theorem supportSet_flip_pairing (f : Rn n → EReal) :
    supportSet (pairing n).flip f = supportSet (pairing n) f := by
  rw [flip_pairing]

@[simp] theorem supportFn_flip_pairing (s : Set (Rn n)) :
    supportFn (pairing n).flip s = supportFn (pairing n) s := by
  rw [flip_pairing]

@[simp] theorem polarCone_flip_pairing (K : Set (Rn n)) :
    polarCone (pairing n).flip K = polarCone (pairing n) K := by
  rw [flip_pairing]

@[simp] theorem polarSet_flip_pairing (C : Set (Rn n)) :
    polarSet (pairing n).flip C = polarSet (pairing n) C := by
  rw [flip_pairing]

end Flip

/-! ### The vector picture of a linear function

A textbook in `ℝⁿ` writes a linear function as `⟨·, b⟩` and quantifies over the vector `b`; the
backbone quantifies over a continuous linear functional, because that is what separation theory
produces in general. `linFn` and `exists_linFn` are the Fréchet–Riesz translation between the two,
and every surface statement about a hyperplane pays exactly one round trip through them. -/

section LinFn

variable {n : ℕ}

/-- The vector `b` read as the linear function `⟨·, b⟩`. -/
noncomputable def linFn (b : Rn n) : Rn n →L[ℝ] ℝ := innerSL ℝ b

@[simp] theorem linFn_apply (b x : Rn n) : linFn b x = pairing n x b := by
  simp only [linFn, pairing_apply]
  exact real_inner_comm x b

/-- `⟨·, b⟩` is the zero function exactly when `b` is the zero vector: this is what makes `b ≠ 0`
and "`{x | ⟨x, b⟩ = β}` is a hyperplane" the same condition. -/
theorem linFn_eq_zero_iff {b : Rn n} : linFn b = 0 ↔ b = 0 := by
  constructor
  · intro h
    have hb : pairing n b b = 0 := by rw [← linFn_apply b b, h]; rfl
    exact inner_self_eq_zero.1 hb
  · rintro rfl
    ext x
    simp

/-- **Every continuous linear function on `ℝⁿ` is `⟨·, b⟩`.** This is the Fréchet–Riesz
identification, and it is what lets a surface statement quantify over vectors while its proof
quantifies over functionals. -/
theorem exists_linFn (f : Rn n →L[ℝ] ℝ) : ∃ b : Rn n, linFn b = f :=
  ⟨(InnerProductSpace.toDual ℝ (Rn n)).symm f, by
    ext x
    exact InnerProductSpace.toDual_symm_apply (x := x)⟩

end LinFn

/-! ### The canonical adjoint

The backbone keeps the adjoint as *data* (design decision D3): between arbitrarily paired spaces a
transpose need not exist, so `IsAdjointPair B B' A A'` is a hypothesis and `A'` is an argument. On
`ℝⁿ` the transpose does exist and is canonical, and it is Mathlib's `LinearMap.adjoint`.

**Nothing is needed here.** `Tdaf.ConvexAnalysis.isAdjointPair_adjoint`
(`Duality/Pairing.lean`) already states it for `innerₗ E` in finite dimension, and `pairing n` is
an `abbrev` for `innerₗ (Rn n)`, so it applies verbatim: a surface section writes Rockafellar's
`A*` as `LinearMap.adjoint A` and discharges the hypothesis with `isAdjointPair_adjoint A`. This
paragraph exists because the lemma was independently rewritten here once — `gotchas.md` LIB1. -/

end Tdaf.Surface
