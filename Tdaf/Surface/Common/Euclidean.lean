/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Continuity
import Tdaf.Analysis.Convex.Convergence
import Tdaf.Analysis.Convex.Duality.Conjugate
import Tdaf.Analysis.Convex.Duality.InnerPairing
import Tdaf.Analysis.Convex.Duality.GaugeLike
import Tdaf.Analysis.Convex.Duality.Level
import Tdaf.Analysis.Convex.Duality.Relint
import Tdaf.Analysis.Convex.EuclideanProd
import Tdaf.Analysis.Convex.HullDirections
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
  `supportFn_flip_pairing`, `polarCone_flip_pairing`, `polarSet_flip_pairing`,
  `polarGauge_flip_pairing`, `polarFn_flip_pairing` — the places a
  `.flip` survives into a statement, rewritten away once here rather than at every call site. On a
  self-paired space every bipolar theorem hands one back, and `flip_pairing` is a `simp` lemma but
  not a `rfl`, so `exact` fails where these make it succeed.
* `pairing_comm`, `forall_pairing_le_comm`, `forall_pairing_lt_comm` — the pairing is symmetric.
  A book writes a linear system as `⟨aᵢ, x⟩ ≤ αᵢ` and the backbone quantifies the other way round;
  these are the translation.
* `pairing_eq_sum`, `pairing_two` — the pairing in coordinates, `⟨u, v⟩ = ∑ᵢ uᵢvᵢ` and its `n = 2`
  instance. Every two-dimensional counterexample in a textbook opens with the second. Four
  sections had written one or the other `private` before they were put here.
* `continuous_coord` — each coordinate of `Rn n` is continuous. The companion to the two above:
  a counterexample that *cuts a region out* of `Rn n` with coordinate inequalities needs it to
  show the region is open. Also written `private` twice, at `Fin 1` and `Fin 2`.
* `separatingRight_pairing` — `(pairing n).SeparatingRight`, which several backbone theorems ask
  for as a hypothesis and which is otherwise re-derived, at every call site, from
  `separatingRight_flip_of_separatingDual`.
* `linFn`, `exists_linFn` — the Fréchet–Riesz translation between the book's vector `b` and the
  backbone's continuous linear functional.
* `linFn_eq_toDual`, `toDual_apply_eq_pairing` — that translation is `InnerProductSpace.toDual`,
  the map `Subgradient/{Rademacher,Reconstruction}.lean` state their gradient results against. A
  surface section that reads `∇f(x)` as a vector rewrites by these once per statement.

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
for `Convex.convexHull_union`; `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional`, which
every section that counts dimensions wants; `Duality.Level`, which is where the level-set duality
and `separatingRight_flip_of_separatingDual` live; and `HullDirections`, which is the module the
mixed points-and-directions modelling decision of §§8, 17, 18 and 19 runs on. Adding one here
costs a rebuild of the surface and saves a section from discovering an "unknown constant" that is
really a missing import.

**`pairingProd` is the pairing on the product, and `Rn (m + n)` is one module away.** Rockafellar
moves freely between `ℝᵐ × ℝⁿ` and `ℝᵐ⁺ⁿ`, and those are different types here.
`Tdaf/Analysis/Convex/EuclideanProd.lean` is the concatenation of coordinates that identifies them,
with the transport of `conj`, `subgradient` and `ri` across it; `pairingProd_euclideanProdEquiv`
below is the one line of it a surface statement usually needs, and says that `pairingProd` **is**
the inner product of `Rn (m + n)` read through the concatenation. What this module supplies on its
own is the pairing on the *product*, which is what the backbone's bifunction theory is stated
against.
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

/-- **The pairing is symmetric.** Rockafellar writes a linear system as `⟨aᵢ, x⟩ ≤ αᵢ`, with the
data on the left; the backbone's `B x y` puts the variable there. On a self-paired space the two
readings are the same number, and this is the lemma that says so. -/
theorem pairing_comm {n : ℕ} (x y : Rn n) : pairing n x y = pairing n y x := real_inner_comm y x

/-- A system of weak inequalities read in the book's orientation and in the backbone's. -/
theorem forall_pairing_le_comm {n : ℕ} {ι : Sort*} (a : ι → Rn n) (α : ι → ℝ) (x : Rn n) :
    (∀ i, pairing n (a i) x ≤ α i) ↔ ∀ i, pairing n x (a i) ≤ α i :=
  forall_congr' fun i => by rw [pairing_comm]

/-- A system of strict inequalities read in the book's orientation and in the backbone's. -/
theorem forall_pairing_lt_comm {n : ℕ} {ι : Sort*} (a : ι → Rn n) (α : ι → ℝ) (x : Rn n) :
    (∀ i, pairing n (a i) x < α i) ↔ ∀ i, pairing n x (a i) < α i :=
  forall_congr' fun i => by rw [pairing_comm]

/-- **The pairing in coordinates**: `⟨u, v⟩ = ∑ᵢ uᵢ vᵢ`. The inner product of
`EuclideanSpace ℝ (Fin n)` is the `RCLike` sum, and over `ℝ` the conjugation is the identity.

Every explicit computation a book performs on a named vector goes through this, so it is public
here rather than `private` in whichever section happened to need it first. -/
theorem pairing_eq_sum {n : ℕ} (u v : Rn n) : pairing n u v = ∑ i, u i * v i := by
  simp only [pairing_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **The pairing on `ℝ²` in coordinates**: `⟨u, v⟩ = u₀v₀ + u₁v₁`. Rockafellar's
counterexamples are two-dimensional almost without exception, and this is the first line of every
one of them. -/
theorem pairing_two (u v : Rn 2) : pairing 2 u v = u 0 * v 0 + u 1 * v 1 := by
  rw [pairing_eq_sum, Fin.sum_univ_two]

/-- **Each coordinate of `Rn n` is continuous.** `Rn n` is a `PiLp 2`, whose topology is the
product topology, so this is `PiLp.continuous_apply` with the exponent supplied.

Public here for the same reason as `pairing_eq_sum`: every counterexample that cuts a region out of
`Rn n` with coordinate inequalities opens by proving it, and it had been written `private` at
`Fin 1` and at `Fin 2` in two different sections. -/
theorem continuous_coord {n : ℕ} (i : Fin n) : Continuous fun x : Rn n => x i :=
  PiLp.continuous_apply (p := 2) (fun _ : Fin n => ℝ) i

/-- **`pairing n` separates on the right**, which is the hypothesis the backbone's level-set and
recession duality asks for in place of a book's `y ≠ 0`. It follows from
`separatingRight_flip_of_separatingDual` because `Rn n` is a `SeparatingDual` and the pairing is
its own flip — a two-line derivation that four call sites across §13 and §21 used to repeat. -/
theorem separatingRight_pairing (n : ℕ) : (pairing n).SeparatingRight := by
  have h := separatingRight_flip_of_separatingDual (pairing n)
  rwa [flip_pairing] at h

/-- The **product pairing** on `Rn m × Rn n`, which is what a bifunction from `ℝᵐ` to `ℝⁿ` is
conjugated against. -/
noncomputable abbrev pairingProd (m n : ℕ) : (Rn m × Rn n) →ₗ[ℝ] (Rn m × Rn n) →ₗ[ℝ] ℝ :=
  prodPairing (pairing m) (pairing n)

/-- The **sign-flipped product pairing** of §30: the one Rockafellar's adjoint `F*` of a convex
bifunction is stated against. -/
noncomputable abbrev pairingAdjoint (m n : ℕ) : (Rn m × Rn n) →ₗ[ℝ] (Rn m × Rn n) →ₗ[ℝ] ℝ :=
  negFst (pairingProd m n)

/-- **The product pairing is the pairing of `Rn (m + n)`, read through the concatenation of
coordinates** (`euclideanProdEquiv`, `Tdaf/Analysis/Convex/EuclideanProd.lean`). This is the
identification a text in `ℝⁿ` makes silently whenever it writes a point of `ℝᵐ × ℝⁿ` as a point of
`ℝᵐ⁺ⁿ`. -/
theorem pairingProd_euclideanProdEquiv {m n : ℕ} (p q : Rn m × Rn n) :
    pairingProd m n p q = pairing (m + n) (euclideanProdEquiv m n p) (euclideanProdEquiv m n q) :=
  (inner_euclideanProdEquiv p q).symm

/-! ### Dimension

`Module.finrank ℝ (Rn n) = n` is `finrank_euclideanSpace_fin`, and Mathlib does not mark it `simp`.
Every surface section that states one of the book's dimension counts needs it, and twenty-two sites
across §1, §13, §14, §17 and §21 rewrote it by hand — eleven in §21 alone. Give it the attribute
once, here. -/

attribute [simp] finrank_euclideanSpace_fin

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

@[simp] theorem polarGauge_flip_pairing (k : Rn n → EReal) :
    polarGauge (pairing n).flip k = polarGauge (pairing n) k := by
  rw [flip_pairing]

@[simp] theorem polarFn_flip_pairing (f : Rn n → EReal) :
    polarFn (pairing n).flip f = polarFn (pairing n) f := by
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

/-- **`linFn` is the Fréchet–Riesz map.** `linFn b = ⟨·, b⟩` is what
`InnerProductSpace.toDual ℝ (Rn n)` sends `b` to, so the surface's vector-to-functional
translation and the one the backbone's `Subgradient/{Rademacher,Reconstruction}.lean` use are the
same map. Every surface statement that reads a gradient as a *vector* pays one rewrite by this,
which is why it sits here beside the `*_flip_pairing` rewrites rather than in one section. -/
theorem linFn_eq_toDual (b : Rn n) : linFn b = InnerProductSpace.toDual ℝ (Rn n) b := by
  ext y
  simp [linFn]

/-- The Riesz representative of `v` evaluated at `x` is the book's `⟨x, v⟩`. Every backbone result
about `HasGradientAt` produces the left-hand side, and every surface statement wants the right.

`InnerProductSpace.toDual_apply` is not a name — it is `toDual_apply_apply`, and it is `rfl` — so
this is `real_inner_comm` and nothing more. -/
theorem toDual_apply_eq_pairing (v x : Rn n) :
    (InnerProductSpace.toDual ℝ (Rn n) v) x = pairing n x v :=
  real_inner_comm x v

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
