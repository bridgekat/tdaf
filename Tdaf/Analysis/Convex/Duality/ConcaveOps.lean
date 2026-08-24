/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.ConcaveConj
import Tdaf.Analysis.Convex.Duality.Exact

/-!
# Supremal convolution, and Theorem 16.4 for concave functions

The concave mirror of `Operations/InfConv.lean` and of `IsExactSum.conj_add`. Where two convex
functions are combined by infimal convolution `f₁ □ f₂` and the conjugate of a *sum* is that
convolution (Rockafellar's Theorem 16.4), two concave functions are combined by **supremal**
convolution and the *concave* conjugate of a sum is that convolution. Rockafellar uses the same
symbol `□` for both and calls the second "the concave version of Theorem 16.4"; §38 needs it, for
the adjoint of `F₁ □ F₂`.

## Main definitions

* `supConv g h` — the supremal convolution `(g □ h)(x) = sup {g x₁ + h x₂ | x₁ + x₂ = x}`, defined
  as `-((-g) □ (-h))`.

## Main results

* `infConv_neg` — infimal convolution commutes with negating the argument.
* `supConv_apply` — the supremum formula, under the hypothesis that neither function reaches `+∞`.
* `concaveConj_add_of_isExactSum` — **the concave Theorem 16.4**: `(g₁ + g₂)* = g₁* □ g₂*` for
  concave `gᵢ`, under exactly the hypothesis `IsExactSum B (-g₁) (-g₂)`.

## Design notes

**`supConv` is `infConv` conjugated by negation of *values*, not of arguments.** Writing
`(g □ h)(x) = -((-g) □ (-h))(x)` keeps the point `x` fixed, and the definition inherits
commutativity, associativity and the effective-domain formula from `infConv` for free. The
reflection that *does* appear — `infConv_neg` — comes from the sign dictionary between `conj` and
`concaveConj`, which reflects on the *dual* side (`neg_concaveConj`: `-(g*(y)) = (-g)*(-y)`), and
it has to be crossed once inside the proof of the concave Theorem 16.4.

**The hypothesis is `IsExactSum B (-g₁) (-g₂)`, and it is exactly Rockafellar's.** His proof of
Theorem 38.2 splits on whether `x* ∈ dom F₁* ∩ dom F₂*`, which is precisely the condition that
neither concave function `gᵢ` takes the value `+∞` — i.e. that `-gᵢ` is proper, which is two of the
three fields of `IsExactSum`. The relative-interior condition supplies the third
(`IsExactSum.of_relint`). So no case distinction survives into the statement.

**Negation distributes over an `EReal` sum in two dual situations.**
`Tdaf.EReal.neg_add_of_ne_top` covers the convex-to-concave direction; `neg_add_of_ne_bot` here is
its mirror and is what turns `⨅ (-g₁ + -g₂)` into `⨆ (g₁ + g₂)`. It is *not* obtainable by `simp`
(gotcha 9), and it is derived from the existing lemma by negating both arguments.

## What is not here

The concave orientation of the *other* rows of §16 — `smulRight`, `compLin`, the image rule — and
the concave `IsExactSum` interface as a structure. Only the sum row has a consumer.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §16 and §38.
-/

open Pointwise

namespace Tdaf.ConvexAnalysis

/-! ### `EReal` bookkeeping -/

/-- Negation distributes over an `EReal` sum as soon as neither summand is `⊥`. This is the mirror
of `Tdaf.EReal.neg_add_of_ne_top`, obtained from it by negating both arguments; the two together
are the whole sign dictionary for sums. -/
theorem neg_add_of_ne_bot {u v : EReal} (hu : u ≠ ⊥) (hv : v ≠ ⊥) : -(u + v) = -u + -v := by
  have h := Tdaf.EReal.neg_add_of_ne_top (u := -u) (v := -v) (by simpa using hu) (by simpa using hv)
  rw [neg_neg, neg_neg] at h
  rw [← h, neg_neg]

/-! ### Infimal convolution and reflection -/

section InfConvNeg

variable {E : Type*} [AddCommGroup E]

/-- **Infimal convolution commutes with negating the argument**: `(f ∘ -) □ (g ∘ -) = (f □ g) ∘ -`.

Both sides are `ofEpi` of a sum of epigraphs, and negation in the first coordinate is an additive
bijection of `E × ℝ`, so it carries the sum of the epigraphs to the sum of their images. The proof
is the resulting membership equivalence, one splitting at a time. -/
theorem infConv_neg (f g : E → EReal) (x : E) :
    infConv (fun w => f (-w)) (fun w => g (-w)) x = infConv f g (-x) := by
  have key : ∀ μ : ℝ, ((x, μ) : E × ℝ) ∈ epi (fun w => f (-w)) + epi (fun w => g (-w))
      ↔ ((-x, μ) : E × ℝ) ∈ epi f + epi g := by
    intro μ
    constructor
    · rintro ⟨⟨a, α⟩, ha, ⟨b, β⟩, hb, hab⟩
      have hab' : ((a, α) : E × ℝ) + (b, β) = (x, μ) := hab
      rw [Prod.mk_add_mk, Prod.mk.injEq] at hab'
      refine ⟨(-a, α), mk_mem_epi.2 (mk_mem_epi.1 ha), (-b, β),
        mk_mem_epi.2 (mk_mem_epi.1 hb), ?_⟩
      change ((-a, α) : E × ℝ) + (-b, β) = (-x, μ)
      rw [Prod.mk_add_mk, ← neg_add, hab'.1, hab'.2]
    · rintro ⟨⟨a, α⟩, ha, ⟨b, β⟩, hb, hab⟩
      have hab' : ((a, α) : E × ℝ) + (b, β) = (-x, μ) := hab
      rw [Prod.mk_add_mk, Prod.mk.injEq] at hab'
      refine ⟨(-a, α), ?_, (-b, β), ?_, ?_⟩
      · exact mk_mem_epi.2 (by rw [neg_neg]; exact mk_mem_epi.1 ha)
      · exact mk_mem_epi.2 (by rw [neg_neg]; exact mk_mem_epi.1 hb)
      · change ((-a, α) : E × ℝ) + (-b, β) = (x, μ)
        rw [Prod.mk_add_mk, ← neg_add, hab'.1, neg_neg, hab'.2]
  exact le_antisymm (le_ofEpi fun μ hμ => ofEpi_apply_le ((key μ).2 hμ))
    (le_ofEpi fun μ hμ => ofEpi_apply_le ((key μ).1 hμ))

end InfConvNeg

/-! ### Supremal convolution -/

section SupConv

variable {E : Type*} [AddCommGroup E]

/-- **Supremal convolution** of two concave functions, Rockafellar's `□` in its concave
orientation: `(g □ h)(x) = sup {g x₁ + h x₂ | x₁ + x₂ = x}`.

Defined as `-((-g) □ (-h))` so that every property of `infConv` transfers by one negation; the
supremum formula is `supConv_apply`, and like `infConv_apply` it needs the hypothesis that rules
out `∞ - ∞` — here that neither function reaches `+∞`. -/
noncomputable def supConv (g h : E → EReal) : E → EReal :=
  fun x => -(infConv (fun w => -(g w)) (fun w => -(h w)) x)

theorem supConv_def (g h : E → EReal) :
    supConv g h = fun x => -(infConv (fun w => -(g w)) (fun w => -(h w)) x) := rfl

@[simp] theorem neg_supConv (g h : E → EReal) (x : E) :
    -(supConv g h x) = infConv (fun w => -(g w)) (fun w => -(h w)) x := neg_neg _

/-- Supremal convolution is commutative, because infimal convolution is. -/
theorem supConv_comm (g h : E → EReal) : supConv g h = supConv h g :=
  funext fun x => congrArg Neg.neg (congrFun (infConv_comm _ _) x)

/-- **Rockafellar's formula for the concave `□`**: `(g □ h)(x) = sup {g (x - y) + h y | y}`.

The hypotheses mirror those of `infConv_apply`: without them the summand is `∞ - ∞` at the points
where one function is `+∞` and the other `-∞`, and `EReal` resolves it on the wrong side. -/
theorem supConv_apply {g h : E → EReal} (hg : ∀ x, g x ≠ ⊤) (hh : ∀ x, h x ≠ ⊤) (x : E) :
    supConv g h x = ⨆ y, g (x - y) + h y := by
  have h1 : infConv (fun w => -(g w)) (fun w => -(h w)) x
      = ⨅ y, -(g (x - y)) + -(h y) :=
    infConv_apply (fun z => by simpa using hg z) (fun z => by simpa using hh z) x
  change -(infConv (fun w => -(g w)) (fun w => -(h w)) x) = _
  rw [h1, Tdaf.EReal.neg_iInf]
  refine iSup_congr fun y => ?_
  rw [neg_add_of_ne_bot (by simpa using hg (x - y)) (by simpa using hh y), neg_neg, neg_neg]

end SupConv

/-! ### Theorem 16.4, concave orientation -/

section ConcaveThm164

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **Rockafellar's Theorem 16.4 for concave functions**: the concave conjugate of a sum is the
supremal convolution of the concave conjugates, `(g₁ + g₂)* = g₁* □ g₂*`.

The hypothesis is the convex `IsExactSum` interface applied to `-g₁` and `-g₂`; its two properness
fields say exactly that neither `gᵢ` takes the value `+∞`, which is where Rockafellar's proof of
Theorem 38.2 case-splits.

Design decision D2 forbids obtaining the concave statement by `simp`-normalising through negation,
and here is why: the sign dictionary `neg_concaveConj` reflects the *dual* variable, so the proof
crosses `infConv_neg` once. Everything else is `Tdaf.EReal.neg_add_of_ne_top` on the primal side
and `IsExactSum.conj_add`. -/
theorem concaveConj_add_of_isExactSum {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {g₁ g₂ : E → EReal}
    (hex : IsExactSum B (fun x => -(g₁ x)) (fun x => -(g₂ x))) :
    concaveConj B (fun x => g₁ x + g₂ x)
      = supConv (concaveConj B g₁) (concaveConj B g₂) := by
  have hg₁ : ∀ x, g₁ x ≠ ⊤ := fun x hx => hex.proper_left.ne_bot x (by simp [hx])
  have hg₂ : ∀ x, g₂ x ≠ ⊤ := fun x hx => hex.proper_right.ne_bot x (by simp [hx])
  have hsum : (fun x => -(g₁ x + g₂ x)) = (fun x => -(g₁ x)) + (fun x => -(g₂ x)) :=
    funext fun x => Tdaf.EReal.neg_add_of_ne_top (hg₁ x) (hg₂ x)
  funext v
  have step1 : concaveConj B (fun x => g₁ x + g₂ x) v
      = -(conj B ((fun x => -(g₁ x)) + (fun x => -(g₂ x))) (-v)) := by
    rw [← hsum]
    exact concaveConj_eq_neg_conj_neg B (fun x => g₁ x + g₂ x) v
  have step2 : conj B ((fun x => -(g₁ x)) + (fun x => -(g₂ x))) (-v)
      = infConv (conj B fun x => -(g₁ x)) (conj B fun x => -(g₂ x)) (-v) :=
    congrFun hex.conj_add (-v)
  have step3 : infConv (conj B fun x => -(g₁ x)) (conj B fun x => -(g₂ x)) (-v)
      = infConv (fun w => -(concaveConj B g₁ w)) (fun w => -(concaveConj B g₂ w)) v := by
    have e₁ : (fun w => -(concaveConj B g₁ w)) = fun w => (conj B fun x => -(g₁ x)) (-w) :=
      funext fun w => neg_concaveConj B g₁ w
    have e₂ : (fun w => -(concaveConj B g₂ w)) = fun w => (conj B fun x => -(g₂ x)) (-w) :=
      funext fun w => neg_concaveConj B g₂ w
    rw [e₁, e₂]
    exact (infConv_neg _ _ v).symm
  change concaveConj B (fun x => g₁ x + g₂ x) v
      = -(infConv (fun w => -(concaveConj B g₁ w)) (fun w => -(concaveConj B g₂ w)) v)
  rw [step1, step2, step3]

end ConcaveThm164

end Tdaf.ConvexAnalysis
