/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Operations.Basic
import Tdaf.Analysis.Convex.Operations.Hull

/-!
# The complete lattice of convex functions

Rockafellar, *Convex Analysis*, §5, the paragraph after Theorem 5.6:

> The collection of all convex functions on `Rⁿ`, regarded as a partially ordered set relative to
> the pointwise ordering, is a complete lattice. The greatest lower bound of a family of convex
> functions `f i` is `conv {f i | i ∈ I}` (relative to this particular partially ordered set!),
> while the least upper bound is `sup {f i | i ∈ I}`.

This file records that sentence as a `CompleteLattice` instance on
`ConvexFns E = {f : E → EReal // ConvexFn f}` and proves that the instance computes what
Rockafellar says it computes. Almost nothing is proved here: the mathematics is already in
`Tdaf/Analysis/Convex/Operations/Hull.lean` (`gci_val_convHullFn`, the coreflection of all
functions onto the convex ones) and in `Tdaf/Analysis/Convex/Operations/Basic.lean`
(`convexFn_iSup`, Theorem 5.5). This file is the assembly.

## Main definitions

* `ConvexFns E` — the convex functions on `E`, bundled as a type.
* `ConvexFns.instCompleteLattice` — the complete lattice structure, obtained from
  `gci_val_convHullFn` by `GaloisCoinsertion.liftCompleteLattice`.
* `ConvexFns.coeOrderEmbedding` — the coercion `ConvexFns E → (E → EReal)` as an
  `OrderEmbedding`: the order is the pointwise order and nothing else.
* `ConvexFns.coeSSupHom` — the same coercion as an `sSupHom`. There is deliberately no
  `sInfHom`, and `ConvexFns.not_coe_inf_eq_inf` says there cannot be one.

## Main results

* `ConvexFns.coe_sSup`, `ConvexFns.coe_iSup`, `ConvexFns.coe_sSup_apply`,
  `ConvexFns.coe_sup` — **the join is the pointwise supremum**, with no hull taken. This is
  Rockafellar's "`sup {f i}`", and it is exactly Theorem 5.5 (`convexFn_iSup`) that makes it
  work.
* `ConvexFns.coe_sInf`, `ConvexFns.coe_iInf`, `ConvexFns.coe_inf` — **the meet is
  the convex hull**: `⨅ i, f i` is `convFn` and `f ⊓ g` is `convFn₂`, not the pointwise
  infimum.
* `ConvexFns.coe_top`, `ConvexFns.coe_bot` — the extreme elements are the constants `⊤`
  and `⊥`, both of which are convex, so again no hull is taken.
* `ConvexFns.exists_coe_inf_lt_inf` and `ConvexFns.not_coe_inf_eq_inf` — **the meet
  really is not the pointwise infimum**, on the witness of `convFn₂_indicatorFn_lt_inf`.

## Design notes

**Why the meet is `conv` and not the pointwise infimum.** The pointwise infimum of convex functions
need not be convex, so it is not a candidate for a greatest lower bound *inside the convex
functions*: `convFn₂_indicatorFn_lt_inf` exhibits `δ(·|{0})` and `δ(·|{1})` on `ℝ`, whose
pointwise minimum is `⊤` at `1/2` while every convex function below both — for instance
`δ(·|[0,1])` — is `0` there. The greatest lower bound is therefore the greatest convex minorant,
which is `conv {f i}` by its universal property `isGreatest_convFn`. Rockafellar's parenthesis
"(relative to this particular partially ordered set!)" is precisely this warning. Suprema have no
such defect, by Theorem 5.5, which is why the coercion to `E → EReal` is an `sSupHom` but not an
`sInfHom`.

**Which Mathlib order class.** `CompleteLattice` is the right target, not `CompleteSemilatticeSup`:
the meets exist, they are simply not computed pointwise, and discarding them would discard exactly
the half of Rockafellar's sentence that carries content. Nor is
`ClosureOperator.Closeds`-style packaging appropriate: `conv` is *contracting*, so it is a closure
operator only on `(E → EReal)ᵒᵈ`, and the `OrderDual` transport does not simplify away
(`gotchas.md` LIB5, and the design note in `Operations/Hull.lean`). The honestly monotone
coreflection `gci_val_convHullFn` supplies `CompleteLattice` directly.

**Why an `abbrev`.** `ConvexFns E` is a reducible abbreviation for the very subtype that
`gci_val_convHullFn` is stated about, so the coinsertion applies to it on the nose, the
`PartialOrder` that `GaloisCoinsertion.liftCompleteLattice` consumes is Mathlib's
`Subtype.partialOrder`, and the resulting order is *definitionally* the pointwise order
(`ConvexFns.coeOrderEmbedding` is `OrderEmbedding.subtype`, with `Iff.rfl` for its map
condition). A `def` would sever all three and would need the order re-declared by hand.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §5 (Theorem 5.5,
  Theorem 5.6, and the discussion of the lattice structure following them).
-/

open Set

namespace Tdaf.ConvexAnalysis

/-! ### The type of convex functions -/

/-- The **convex functions on `E`**, bundled as a type so that Rockafellar's lattice structure
(§5, after Theorem 5.6) can be recorded on it.

This is a reducible abbreviation for the subtype `gci_val_convHullFn` is stated about, so the
coreflection applies to it verbatim and the order is Mathlib's `Subtype.partialOrder`, i.e. the
pointwise order. -/
abbrev ConvexFns (E : Type*) [AddCommGroup E] [Module ℝ E] := {f : E → EReal // ConvexFn f}

namespace ConvexFns

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Rockafellar §5, after Theorem 5.6.** The convex functions on `E`, pointwise ordered, form a
**complete lattice**.

The instance is not built by hand: it is the coreflection `gci_val_convHullFn` of all
`EReal`-valued functions onto the convex ones, transported by
`GaloisCoinsertion.liftCompleteLattice`. Consequently every field computes as the corresponding
operation on `E → EReal` followed by `convHullFn`, and the lemmas below simply evaluate that
hull: it is the identity on suprema (Theorem 5.5) and it is the content of the theory on
infima. -/
noncomputable instance instCompleteLattice : CompleteLattice (ConvexFns E) :=
  gci_val_convHullFn.liftCompleteLattice

/-- The coercion `ConvexFns E → (E → EReal)` is an **order embedding**: `f ≤ g` in the lattice of
convex functions means exactly `f x ≤ g x` for every `x`. -/
noncomputable def coeOrderEmbedding : ConvexFns E ↪o (E → EReal) := OrderEmbedding.subtype _

/-- `ConvexFns.coeOrderEmbedding` is the coercion. -/
@[simp]
theorem coe_coeOrderEmbedding :
    ⇑(coeOrderEmbedding : ConvexFns E ↪o (E → EReal)) = Subtype.val := rfl

/-- A convex function is a member of the lattice, and only convex functions are. -/
@[simp]
theorem mem_range_coe {g : E → EReal} :
    g ∈ Set.range (Subtype.val : ConvexFns E → (E → EReal)) ↔ ConvexFn g :=
  ⟨fun ⟨f, hf⟩ => hf ▸ f.2, fun h => ⟨⟨g, h⟩, rfl⟩⟩

/-! ### Suprema: the join is pointwise

Nothing is lost on the way up. `convexFn_iSup` (Theorem 5.5) says the pointwise supremum of
convex functions is convex, so the coreflector fixes it and the lifted `sSup` is the pointwise
one. -/

/-- **The least upper bound is the pointwise supremum** (Rockafellar's "`sup {f i}`"). -/
@[simp]
theorem coe_sSup (s : Set (ConvexFns E)) :
    ((sSup s : ConvexFns E) : E → EReal) = sSup (Subtype.val '' s) := by
  refine convHullFn_eq_self ?_
  have h : sSup (Subtype.val '' s) = fun x => ⨆ f : s, ((f : ConvexFns E) : E → EReal) x := by
    rw [sSup_image']
    exact funext fun x => iSup_apply
  rw [h]
  exact convexFn_iSup fun f : s => (f : ConvexFns E).2

/-- The indexed form of `ConvexFns.coe_sSup`: an `⨆` of convex functions is computed
pointwise. -/
theorem coe_iSup {ι : Sort*} (f : ι → ConvexFns E) :
    ((⨆ i, f i : ConvexFns E) : E → EReal) = ⨆ i, (f i : E → EReal) := by
  rw [iSup, coe_sSup, ← Set.range_comp]
  rfl

/-- Rockafellar's formula in its pointwise form: the join of a family is evaluated at `x` by taking
the supremum of the values there. -/
@[simp]
theorem coe_iSup_apply {ι : Sort*} (f : ι → ConvexFns E) (x : E) :
    ((⨆ i, f i : ConvexFns E) : E → EReal) x = ⨆ i, (f i : E → EReal) x := by
  rw [coe_iSup, iSup_apply]

/-- `ConvexFns.coe_sSup` evaluated at a point. -/
theorem coe_sSup_apply (s : Set (ConvexFns E)) (x : E) :
    ((sSup s : ConvexFns E) : E → EReal) x = ⨆ f ∈ s, (f : E → EReal) x := by
  rw [coe_sSup, sSup_image', iSup_apply, iSup_subtype]

/-- The binary case: the join of two convex functions is their pointwise maximum
(`ConvexFn.sup`). -/
@[simp]
theorem coe_sup (f g : ConvexFns E) :
    ((f ⊔ g : ConvexFns E) : E → EReal) = (f : E → EReal) ⊔ (g : E → EReal) :=
  convHullFn_eq_self (f.2.sup g.2)

/-- The coercion to `E → EReal` as an **`sSupHom`**: it preserves arbitrary suprema. There is no
companion `sInfHom` — see `ConvexFns.not_coe_inf_eq_inf`. -/
noncomputable def coeSSupHom : sSupHom (ConvexFns E) (E → EReal) where
  toFun := Subtype.val
  map_sSup' := coe_sSup

/-- `ConvexFns.coeSSupHom` is the coercion. -/
@[simp]
theorem coe_coeSSupHom : ⇑(coeSSupHom : sSupHom (ConvexFns E) (E → EReal)) = Subtype.val := rfl

/-! ### Infima: the meet is a convex hull

Going down, the pointwise infimum leaves the convex functions, and the coreflector has to be
applied. What comes out is Rockafellar's `conv {f i}`. -/

/-- **The greatest lower bound is a convex hull**, `conv` of the pointwise infimum. -/
theorem coe_sInf (s : Set (ConvexFns E)) :
    ((sInf s : ConvexFns E) : E → EReal) = convHullFn (sInf (Subtype.val '' s)) := rfl

/-- **Rockafellar's `conv {f i | i ∈ I}`.** The greatest lower bound of a family of convex
functions is their convex hull `convFn` — *not* their pointwise infimum, which is generally
not convex. -/
@[simp]
theorem coe_iInf {ι : Sort*} (f : ι → ConvexFns E) :
    ((⨅ i, f i : ConvexFns E) : E → EReal) = convFn (fun i => (f i : E → EReal)) := by
  rw [convFn_eq_convHullFn_iInf, iInf, coe_sInf, ← Set.range_comp]
  refine congrArg convHullFn (funext fun x => ?_)
  change (⨅ i, (f i : E → EReal)) x = ⨅ i, (f i : E → EReal) x
  exact iInf_apply

/-- The binary case: the meet of two convex functions is `convFn₂`, their binary convex
hull. -/
@[simp]
theorem coe_inf (f g : ConvexFns E) :
    ((f ⊓ g : ConvexFns E) : E → EReal) = convFn₂ (f : E → EReal) (g : E → EReal) :=
  convHullFn_inf _ _

/-- The meet lies below the pointwise infimum, and generally strictly:
`ConvexFns.exists_coe_inf_lt_inf`. -/
theorem coe_inf_le_inf (f g : ConvexFns E) :
    ((f ⊓ g : ConvexFns E) : E → EReal) ≤ (f : E → EReal) ⊓ (g : E → EReal) :=
  (coe_inf f g).trans_le (convFn₂_le_inf _ _)

/-! ### The extreme elements -/

/-- The greatest convex function is the constant `⊤`. -/
@[simp]
theorem coe_top : ((⊤ : ConvexFns E) : E → EReal) = ⊤ :=
  convHullFn_eq_self (convexFn_const ⊤)

/-- The least convex function is the constant `⊥`. -/
@[simp]
theorem coe_bot : ((⊥ : ConvexFns E) : E → EReal) = ⊥ :=
  convHullFn_eq_self (convexFn_const ⊥)

end Module

/-! ### The meet is not the pointwise infimum

`convFn₂_indicatorFn_lt_inf` is the machine-checked witness: on `ℝ`, the indicator functions
of `{0}` and `{1}` are convex, their pointwise minimum is `⊤` at `1 / 2`, and their meet in
`ConvexFns ℝ` — the indicator function of `[0, 1]` — is `0` there. -/

/-- **The meet of `ConvexFns` is strictly below the pointwise infimum, in general.** -/
theorem exists_coe_inf_lt_inf :
    ∃ (f g : ConvexFns ℝ) (x : ℝ),
      ((f ⊓ g : ConvexFns ℝ) : ℝ → EReal) x < ((f : ℝ → EReal) ⊓ (g : ℝ → EReal)) x := by
  refine ⟨⟨indicatorFn ({0} : Set ℝ), convexFn_indicatorFn.2 (convex_singleton 0)⟩,
    ⟨indicatorFn ({1} : Set ℝ), convexFn_indicatorFn.2 (convex_singleton 1)⟩, 1 / 2, ?_⟩
  rw [coe_inf, Pi.inf_apply]
  exact convFn₂_indicatorFn_lt_inf

/-- **The coercion `ConvexFns E → (E → EReal)` is not an `sInfHom`**, not even a lattice
homomorphism: it does not commute with binary meets. Contrast `ConvexFns.coeSSupHom`. -/
theorem not_coe_inf_eq_inf :
    ¬ ∀ f g : ConvexFns ℝ,
      ((f ⊓ g : ConvexFns ℝ) : ℝ → EReal) = (f : ℝ → EReal) ⊓ (g : ℝ → EReal) := by
  obtain ⟨f, g, x, hx⟩ := exists_coe_inf_lt_inf
  exact fun h => absurd (congrFun (h f g) x) hx.ne

end ConvexFns

end Tdaf.ConvexAnalysis
