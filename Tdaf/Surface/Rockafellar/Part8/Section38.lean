/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Bifunction.Cofinite
import Tdaf.Surface.Rockafellar.Part6.Section30

/-!
# Rockafellar, §38: The Algebra of Bifunctions

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §38, pp. 401–412: addition, scalar
multiplication, application and composition of convex bifunctions, and how each behaves under
taking adjoints.

All twelve numbered results are here: `Theorem 38.1`, Theorems 38.2–38.5, 38.7, Lemma 38.6, and
Corollaries 38.2.1, 38.4.1, 38.5.1, 38.7.1 and `Corollary 38.7.2`. Two of the twelve labels are
**mixed case** in the book (`Theorem 38.1` at 16211 and `Corollary 38.7.2` at 16673) and are
dropped by a case-sensitive extractor; both are real numbered results and both are below.

## Contents

| label | declaration |
|---|---|
| §38 definitions | `convexAdd`, `concaveAdd`, `HasInnerProduct`, `innerProduct` |
| Theorem 38.1 | `theorem_38_1_convex`, `theorem_38_1_dom`, `theorem_38_1_bracket`,
  `theorem_38_1_bracket_concave` |
| §38 remark, 16239 | `infConvBifun_comm'`, `infConvBifun_assoc'` |
| Theorem 38.2 | `theorem_38_2` |
| Corollary 38.2.1 | `corollary_38_2_1_closed`, `corollary_38_2_1_adjoint` |
| Theorem 38.3 | `theorem_38_3_convex`, `theorem_38_3_bracket`, `theorem_38_3_closed`,
  `theorem_38_3_proper`, `theorem_38_3_adjoint` |
| Theorem 38.4 | `theorem_38_4_convex`, `theorem_38_4_conj`, `theorem_38_4_attained` |
| Corollary 38.4.1 | `corollary_38_4_1_closed`, `corollary_38_4_1_attained`,
  `corollary_38_4_1_conj` |
| §38 remark, 16428 | `inverseBifun_compBifun'` |
| Theorem 38.5 | `theorem_38_5_convex`, `theorem_38_5_adjoint`, `theorem_38_5_attained` |
| Corollary 38.5.1 | `corollary_38_5_1_closed`, `corollary_38_5_1_attained`,
  `corollary_38_5_1_adjoint` |
| Lemma 38.6 | `lemma_38_6_exists`, `lemma_38_6` |
| Theorem 38.7 | `theorem_38_7`, `theorem_38_7_third` |
| Corollary 38.7.1 | `corollary_38_7_1_exists`, `corollary_38_7_1` |
| `Corollary 38.7.2` | `corollary_38_7_2_exists`, `corollary_38_7_2_first`,
  `corollary_38_7_2_second` |
| §38 closing discussion, 16693–16729 | `cofiniteBifun_bracket_finite`,
  `cofinite_iff_forall_bracket_finite`, `cofiniteBifun_bracket_eq`,
  `cofinite_infConvBifun'`, `cofinite_adjoint_infConvBifun`, `cofinite_smulRightBifun'`,
  `cofiniteBifun_of_domBifun_eq_univ'` |

## The section's own vocabulary

Rockafellar defines six things here. Five of them are the backbone's, at the Euclidean pairing:

| book | here |
|---|---|
| `F₁ □ F₂` (16203) | `infConvBifun F₁ F₂` |
| `Fλ` (16325) | `smulRightBifun F l` |
| `Ff` (16365) | `imageBifun F f` |
| `GF` (16413) | `compBifun G F` |
| `F*` (§30) | `dualProgram F`, i.e. `adjointBifun (pairing m) (pairing n) F` |
| `F⁎`, `F⁎*` (§30, §38) | `inverseBifun F`, `lowerAdjointBifun (pairing m) (pairing n) F` |
| co-finite (16693) | `CofiniteBifun F` |

The sixth, `⟨f, g⟩` (16515–16527), is **a partial operation**, and this file keeps it partial:
`HasInnerProduct f g` says the sup side and the inf side agree, `innerProduct f g` is the common
value, and **every result below carries `HasInnerProduct` as an explicit hypothesis** rather than
silently reading `innerProduct` off the inf side. Rockafellar states the definedness condition in
prose ("If the quantities are not equal, `⟨f, g⟩` is undefined") and then writes `⟨f, g⟩` freely;
the point of naming the predicate is that a reader can see where that fluency is hiding a
hypothesis.

## The two `∞ − ∞` conventions of Theorem 38.1

Theorem 38.1's inner-product identity is stated "if one sets `∞ − ∞ = −∞ + ∞ = −∞`", and its
parenthetical adds "(Similarly for concave bi-functions, but with `∞ − ∞ = −∞ + ∞ = +∞`.)"
(16223). **These are two different binary operations on `EReal`, and this file names them
separately**: `convexAdd`, which is `EReal`'s own addition, and `concaveAdd`, which is not.
`convexAdd_top_bot`, `concaveAdd_top_bot` and `convexAdd_ne_concaveAdd` are the proof that letting
one notation carry both would be a mistranslation: `theorem_38_1_bracket_concave` is **false**
with `convexAdd` in place of `concaveAdd`.

This is the fourth overloading of `⟨·, ·⟩` in the book — the first three are in §33 — and the
fourth distinct `∞ − ∞` rule.

## Divergences from the book recorded in docstrings

* **`□` is unconditionally commutative and associative here** (`infConvBifun_comm'`,
  `infConvBifun_assoc'`), where Rockafellar hedges with "to the extent that it is defined" (16239).
  `infConv` is a total operation on `EReal`, so the backbone's `infConvBifun_comm` and
  `infConvBifun_assoc` need no hypothesis at all; that is **stronger** than the book. See
  `gotchas.md` ER4: `EReal`'s totalisation is not Rockafellar's convention, and a surface statement
  that drops a properness hypothesis can silently prove something the book does not state — here it
  proves something the book *does* state, only more of it. `infConvFstBifun_comm` and
  `infConvFstBifun_assoc` are the same pair for the first-variable convolution.
* Rockafellar's caveat at 16507, "multiplication of convex bifunctions is plainly associative to
  the extent that it is defined", is a genuine restriction and **is not discharged here**: see
  `## What is not here`.
* **Theorem 38.1's domain formula is misprinted in the book.** 16214 reads
  `dom (F₁ ∩ F₂) = dom F₁ ∩ dom F₂`; the operation on the left is `□`, as the proof makes clear.
  `theorem_38_1_dom` states the intended identity.
* **Corollary 38.7.2's own proof is incomplete.** Rockafellar reduces it to a formula for
  `ri (dom (GF))` and then writes "We leave this to the reader as a pithy exercise in the calculus
  of relative interiors" (16691). `corollary_38_7_2_first` therefore carries the `IsExactSum` its
  proof consumes, which is what his relative-interior calculus was to have produced.

## Where the book's hypotheses had to change

**Every relative-interior hypothesis of §38 is carried as an `IsExactSum`.** Rockafellar's
conditions are always "`ri (dom …)` and `ri (dom …)` have a point in common", which is the
hypothesis of Theorem 16.4; the backbone's `IsExactSum` (`Duality/Exact.lean`) is that theorem's
conclusion, and `IsExactSum.of_relint` produces it from the relative-interior condition. Two
consequences are visible in the statements below and are *not* faithful to the book's phrasing:

* the exactness is demanded **once per dual vector**, where Rockafellar's single condition is
  uniform in it — his `ri (dom F₁) ∩ ri (dom F₂) ≠ ∅` becomes `∀ y, IsExactSum …` in
  `theorem_38_2`, and similarly in Theorem 38.5 and the two corollaries; and
* `IsExactSum` carries properness of both summands, which is exactly Rockafellar's *main branch*
  (`x* ∈ dom F₁* ∩ dom F₂*` in Theorem 38.2, `y ∈ dom F*` in Theorem 38.4). His degenerate branch
  is a separate backbone theorem, `conj_imageBifun_of_bracket_eq_top`.

Closing the gap between the two would need `adjointBifun_infConvBifun_of_relint` and its three
siblings in `Bifunction/Algebra.lean`; see the report for §38.

## What is not here

* **The associativity of bifunction multiplication** (16507), `H(GF) = (HG)F` "to the extent that
  it is defined". It is *omitted with a reason*: the backbone has no `compBifun_assoc`, and unlike
  `□` this one is genuinely conditional — `((HG)F u)(z) = ⨅_x ⨅_y ((Fu)(x) + (Gx)(y)) + (Hy)(z)`
  needs the inner infimum to distribute over the outer summand, which fails at `∞ − ∞`.
  Rockafellar's own remedy is to *extend* the definition of `GF` by the rule `∞ − ∞ = +∞`, i.e. by
  `concaveAdd`, which is a third product operation the backbone does not carry. Proving it in the
  surface would be proving a backbone theorem in the wrong place.
* **Two of the three facts in the closing co-finiteness discussion are now here**
  (`cofinite_smulRightBifun'` and `cofiniteBifun_of_domBifun_eq_univ'`, added to
  `Bifunction/Cofinite.lean` with this section); the third, that the *product* `GF` of two
  co-finite bifunctions is co-finite, and that `F*` is co-finite, is **deferred by scope**. The
  product needs the co-finite specialisation of Theorem 38.5 with `IsExactSum` instances over four
  spaces; `F*` needs a `CofiniteConcaveBifun` predicate, since `CofiniteBifun` is a property of
  *convex* bifunctions and `lowerAdjointBifun` is the wrong reindexing of `F*`. Both are recorded
  in `Bifunction/Cofinite.lean`'s own `## What is not here`, with the declarations wanted.
* **The two semigroup claims** (16239 and 16513) — that the convex bifunctions from `ℝᵐ` to `ℝⁿ`
  form a commutative semigroup under the extended `□` with the indicator of `0` as identity, and
  that those from `ℝⁿ` to itself form a non-commutative semigroup under the extended product with
  the indicator of `id` as identity. Both are about the *extended* operations of the previous item
  and are *omitted for the same reason*.
* **Theorem 38.7's middle member** `−⟨f*, F⁎ g⟩` of the four-term chain. `theorem_38_7` carries the
  first equality and `theorem_38_7_third` the last; the middle one is Theorem 38.7 applied to the
  inverse bifunction `F⁎`, which the backbone does not state separately, and Rockafellar's own text
  breaks off mid-sentence at 16631 ("Thus ⟨f*, F⁎g⟩ exists, ⟨f, F*g*⟩ exists and" — the display
  that should follow appears two paragraphs later, after "By definition,").
* **Lemma 38.6's second assertion**, that `⟨cl f, cl g⟩` then exists and equals `⟨f, g⟩`. It is
  Lemma 38.6 applied twice, and is *deferred by scope*: the second application needs
  `ProperConcave (concaveConj (pairing n) g)`, which the backbone does not have — the convex half,
  `proper_conj_of_proper`, is in `Duality/Relint.lean` and its concave mirror is missing.
* **The polyhedral sharpening** of 16729, "Most of the results in this section can be sharpened in
  the case of polyhedral bifunctions. However, we shall leave this to the reader." Nothing is
  stated, so there is nothing to transcribe.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §38, pp. 401–412.
-/

open Set

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

/-! ### The two `∞ − ∞` conventions of Theorem 38.1 -/

/-- **Rockafellar's convex `∞ − ∞` convention** (16223): `∞ − ∞ = −∞ + ∞ = −∞`, the rule under
which Theorem 38.1's inner-product identity holds for *convex* bifunctions.

On `EReal` this is the ambient addition, `⊤ + ⊥ = ⊥`; the definition exists so that the convention
has a name distinct from the concave one, not because the operation is new. -/
noncomputable def convexAdd (a b : EReal) : EReal := a + b

/-- **Rockafellar's concave `∞ − ∞` convention** (16223): `∞ − ∞ = −∞ + ∞ = +∞`, the rule under
which the concave orientation of Theorem 38.1 holds.

This is **not** `EReal`'s addition. It is addition read through negation, and it differs from
`convexAdd` at exactly the two collisions. -/
noncomputable def concaveAdd (a b : EReal) : EReal := -(-a + -b)

theorem convexAdd_apply (a b : EReal) : convexAdd a b = a + b := rfl

theorem concaveAdd_apply (a b : EReal) : concaveAdd a b = -(-a + -b) := rfl

/-- The convex convention resolves `∞ − ∞` downwards. -/
@[simp] theorem convexAdd_top_bot : convexAdd ⊤ ⊥ = ⊥ := by
  rw [convexAdd_apply, _root_.EReal.add_bot]

/-- The concave convention resolves `∞ − ∞` upwards. -/
@[simp] theorem concaveAdd_top_bot : concaveAdd ⊤ ⊥ = ⊤ := by
  rw [concaveAdd_apply, _root_.EReal.neg_top, _root_.EReal.neg_bot, _root_.EReal.bot_add,
    _root_.EReal.neg_bot]

/-- **The two conventions are genuinely different operations.** This is why the surface names them
apart instead of letting one notation carry both, as the book's `⟨·, ·⟩` does. -/
theorem convexAdd_ne_concaveAdd : convexAdd ⊤ ⊥ ≠ concaveAdd ⊤ ⊥ := by
  rw [convexAdd_top_bot, concaveAdd_top_bot]
  exact bot_ne_top

/-- **Away from the collisions the two conventions agree.** The hypotheses are exactly the two
`∞ − ∞` configurations ruled out. -/
theorem concaveAdd_eq_convexAdd {a b : EReal} (h₁ : a ≠ ⊤ ∨ b ≠ ⊥) (h₂ : a ≠ ⊥ ∨ b ≠ ⊤) :
    concaveAdd a b = convexAdd a b := by
  have hn₁ : -a ≠ ⊥ ∨ -b ≠ ⊤ := by
    rcases h₁ with h | h
    · exact Or.inl (by rw [Ne, _root_.EReal.neg_eq_bot_iff]; exact h)
    · exact Or.inr (by rw [Ne, _root_.EReal.neg_eq_top_iff]; exact h)
  have hn₂ : -a ≠ ⊤ ∨ -b ≠ ⊥ := by
    rcases h₂ with h | h
    · exact Or.inl (by rw [Ne, _root_.EReal.neg_eq_top_iff]; exact h)
    · exact Or.inr (by rw [Ne, _root_.EReal.neg_eq_bot_iff]; exact h)
  have hna : -(-a + -b) = - -a + - -b := _root_.EReal.neg_add hn₁ hn₂
  have hb₁ : (- -a : EReal) = a := neg_neg a
  have hb₂ : (- -b : EReal) = b := neg_neg b
  rw [concaveAdd_apply, convexAdd_apply, hna, hb₁, hb₂]

/-! ### The inner product `⟨f, g⟩` of a convex and a concave function -/

/-- **Rockafellar's inner product `⟨f, g⟩` exists** (16515–16527): the two extrema

`sup_x {g*(x) − f(x)}` and `inf_y {f*(y) − g(y)}`

agree. Rockafellar leaves `⟨f, g⟩` *undefined* when they do not, so this predicate is the
definedness side condition, and it appears explicitly in every statement below that mentions an
inner product.

Specialises `HasFenchelPairing` to the Euclidean self-pairing. -/
abbrev HasInnerProduct {n : ℕ} (f g : Rn n → EReal) : Prop :=
  HasFenchelPairing (pairing n) f g

/-- **The value of Rockafellar's `⟨f, g⟩`**, represented by the inf side. It is Rockafellar's inner
product only under `HasInnerProduct`; `hasInnerProduct_iff` is the definition of that predicate in
the book's own two extrema.

Specialises `fenchelPairing`. -/
noncomputable abbrev innerProduct {n : ℕ} (f g : Rn n → EReal) : EReal :=
  fenchelPairing (pairing n) f g

variable {m n k : ℕ}

/-- The inf side of `⟨f, g⟩`, in the book's own notation `inf_y {f*(y) − g(y)}` (16524). -/
theorem innerProduct_eq (f g : Rn n → EReal) :
    innerProduct f g = ⨅ y, (conj (pairing n) f y - g y) := rfl

/-- **The definedness condition in the book's own two extrema** (16518, 16524): `⟨f, g⟩` exists
exactly when `sup_x {g*(x) − f(x)} = inf_y {f*(y) − g(y)}`. -/
theorem hasInnerProduct_iff (f g : Rn n → EReal) :
    HasInnerProduct f g ↔
      (⨆ x, (concaveConj (pairing n) g x - f x)) = ⨅ y, (conj (pairing n) f y - g y) := by
  rw [← fenchelInf_apply (pairing n) f g]
  have h : (⨆ x, (concaveConj (pairing n) g x - f x)) = fenchelSup (pairing n) f g := by
    rw [fenchelSup_apply, flip_pairing]
  rw [h]
  exact Iff.rfl

/-- **Weak duality for the inner product**: the sup side never exceeds the inf side, with no
hypothesis. This is what makes every existence claim below a single inequality.

Specialises `fenchelSup_le_fenchelInf`. -/
theorem fenchelSup_le_innerProduct (f g : Rn n → EReal) :
    (⨆ x, (concaveConj (pairing n) g x - f x)) ≤ innerProduct f g := by
  have h : (⨆ x, (concaveConj (pairing n) g x - f x)) = fenchelSup (pairing n) f g := by
    rw [fenchelSup_apply, flip_pairing]
  rw [h]
  exact fenchelSup_le_fenchelInf (pairing n) f g

/-! ### Theorem 38.1 -/

/-- **Rockafellar, `Theorem 38.1`**, first assertion: the infimal convolution
`(F₁ □ F₂)u = F₁u □ F₂u` of two proper convex bifunctions from `ℝᵐ` to `ℝⁿ` is a convex
bifunction.

Rockafellar reads `F₁ □ F₂` as a *partial* infimal convolution of the graph functions, which are
proper convex functions, so the graph function of `F₁ □ F₂` is convex.

Specialises `convexBifun_infConvBifun`. -/
theorem theorem_38_1_convex {F₁ F₂ : Bifun (Rn m) (Rn n)} (hp₁ : Proper (graphFn F₁))
    (hp₂ : Proper (graphFn F₂)) (hc₁ : ConvexBifun F₁) (hc₂ : ConvexBifun F₂) :
    ConvexBifun (infConvBifun F₁ F₂) :=
  convexBifun_infConvBifun (fun u x => hp₁.ne_bot (u, x)) (fun u x => hp₂.ne_bot (u, x)) hc₁ hc₂

/-- **Rockafellar, `Theorem 38.1`**, second assertion:
`dom (F₁ □ F₂) = dom F₁ ∩ dom F₂`.

The book prints the left-hand side as `dom (F₁ ∩ F₂)` (16214); the operation meant is `□`, as its
own proof shows. No hypothesis is needed at all: `dom (f □ g) = dom f + dom g` is unconditional and
a sum of sets is non-empty exactly when both summands are.

Specialises `domBifun_infConvBifun`. -/
theorem theorem_38_1_dom (F₁ F₂ : Bifun (Rn m) (Rn n)) :
    domBifun (infConvBifun F₁ F₂) = domBifun F₁ ∩ domBifun F₂ :=
  domBifun_infConvBifun F₁ F₂

/-- **Rockafellar, `Theorem 38.1`**, the inner-product identity:

`⟨(F₁ □ F₂)u, x*⟩ = ⟨F₁u, x*⟩ + ⟨F₂u, x*⟩` for all `u` and `x*`,

**under the convex convention `∞ − ∞ = −∞`** (`convexAdd`). It needs no hypothesis: it is Theorem
16.4's unconditional row `conj_infConv` read slice by slice, and Rockafellar's convention is
`EReal`'s own `⊤ + ⊥ = ⊥`.

Specialises `bracket_infConvBifun`. -/
theorem theorem_38_1_bracket (F₁ F₂ : Bifun (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    bracket (pairing n) (infConvBifun F₁ F₂) u y
      = convexAdd (bracket (pairing n) F₁ u y) (bracket (pairing n) F₂ u y) :=
  congrFun (bracket_infConvBifun (pairing n) F₁ F₂ u) y

/-- **Rockafellar, `Theorem 38.1`**, concave orientation (the parenthetical at 16223): for concave
bifunctions `□` is *supremal* convolution and the inner-product identity holds **under the concave
convention `∞ − ∞ = +∞`** (`concaveAdd`),

`⟨(G₁ □ G₂)u, x*⟩ = ⟨G₁u, x*⟩ ⊕ ⟨G₂u, x*⟩`,

where `⟨Gu, x*⟩` is the *concave* conjugate of the slice. **The statement is false with
`convexAdd` in place of `concaveAdd`** (`convexAdd_ne_concaveAdd`), which is why the two
conventions are named apart.

Like its convex twin it is unconditional. Its proof is `conj_infConv` again, read through the sign
dictionary `neg_concaveConj`: the two reflections of the dictionary are exactly what turns
`EReal`'s `⊤ + ⊥ = ⊥` into the book's `+∞`. -/
theorem theorem_38_1_bracket_concave (G₁ G₂ : Bifun (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    concaveConj (pairing n) (supConv (G₁ u) (G₂ u)) y
      = concaveAdd (concaveConj (pairing n) (G₁ u) y) (concaveConj (pairing n) (G₂ u) y) := by
  have hneg : (fun x => -(supConv (G₁ u) (G₂ u) x))
      = infConv (fun w => -(G₁ u w)) (fun w => -(G₂ u w)) :=
    funext fun x => neg_supConv (G₁ u) (G₂ u) x
  rw [concaveAdd_apply, neg_concaveConj, neg_concaveConj, ← Pi.add_apply, ← conj_infConv,
    concaveConj_eq_neg_conj_neg, hneg]

/-! ### The algebra of `□` (16239) -/

/-- **Rockafellar, §38 (16239)**: `□` is commutative "in the class of convex bifunctions from `ℝᵐ`
to `ℝⁿ` to the extent that it is defined".

**Divergence from the book, recorded.** The hedge is unnecessary here and the statement carries no
hypothesis: `infConv` is a total operation on `EReal`, so `infConvBifun_comm` holds for *arbitrary*
bifunctions, improper ones included. That is strictly stronger than what Rockafellar claims.
`gotchas.md` ER4 warns that `EReal`'s totalisation is not his convention; the caveat at 16239 is
about bifunction *multiplication* (16507), not about `□`.

Specialises `infConvBifun_comm`. -/
theorem infConvBifun_comm' (F₁ F₂ : Bifun (Rn m) (Rn n)) :
    infConvBifun F₁ F₂ = infConvBifun F₂ F₁ :=
  infConvBifun_comm F₁ F₂

/-- **Rockafellar, §38 (16239)**: `□` is associative, again with no hypothesis — see
`infConvBifun_comm'` for the divergence this records.

Specialises `infConvBifun_assoc`. -/
theorem infConvBifun_assoc' (F₁ F₂ F₃ : Bifun (Rn m) (Rn n)) :
    infConvBifun (infConvBifun F₁ F₂) F₃ = infConvBifun F₁ (infConvBifun F₂ F₃) :=
  infConvBifun_assoc F₁ F₂ F₃

/-! ### Theorem 38.2 -/

/-- **Rockafellar, Theorem 38.2**: `(F₁ □ F₂)* = F₁* □ F₂*`, the bifunction generalisation of
`(A₁ + A₂)* = A₁* + A₂*`. The `□` on the right is *supremal* convolution, the concave orientation.

Rockafellar's hypothesis is that `ri (dom F₁)` and `ri (dom F₂)` have a point in common. Here it is
the `IsExactSum` interface of Theorem 16.4 applied to the two concave functions `u ↦ ⟨Fᵢu, x*⟩`,
one instance per `x*` — see `## Where the book's hypotheses had to change`. Its properness fields
are Rockafellar's main branch `x* ∈ dom F₁* ∩ dom F₂*`.

Specialises `adjointBifun_infConvBifun_eq_supConvBifun`. -/
theorem theorem_38_2 (F₁ F₂ : Bifun (Rn m) (Rn n))
    (hex : ∀ y : Rn n, IsExactSum (pairing m) (fun u => -(bracket (pairing n) F₁ u y))
      (fun u => -(bracket (pairing n) F₂ u y))) :
    dualProgram (infConvBifun F₁ F₂) = supConvBifun (dualProgram F₁) (dualProgram F₂) :=
  adjointBifun_infConvBifun_eq_supConvBifun (pairing m) (pairing n) F₁ F₂ hex

/-! ### Corollary 38.2.1 -/

/-- The `IsExactSum` that Corollary 38.2.1 consumes, in the surface's own `.flip`-free phrasing.
Rockafellar's condition is that `ri (dom F₁*)` and `ri (dom F₂*)` have a point in common. -/
abbrev IsExactSumCor3821 (F₁ F₂ : Bifun (Rn m) (Rn n)) : Prop :=
  ∀ u : Rn m, IsExactSum (pairing n)
    (concaveBracket (pairing m)
      (inverseBifun (lowerAdjointBifun (pairing m) (pairing n) F₁)) u)
    (concaveBracket (pairing m)
      (inverseBifun (lowerAdjointBifun (pairing m) (pairing n) F₂)) u)

/-- **Rockafellar, Corollary 38.2.1**, first assertion: for closed proper convex `F₁` and `F₂`
whose adjoints' effective domains have a relative interior point in common, `F₁ □ F₂` is closed.

The backbone's proof is not Rockafellar's: `F₁ □ F₂` is exhibited as a *lower adjoint*, and a lower
adjoint is closed with no hypothesis at all.

Specialises `closedBifun_infConvBifun`. -/
theorem corollary_38_2_1_closed {F₁ F₂ : Bifun (Rn m) (Rn n)} (hc₁ : ConvexBifun F₁)
    (hcl₁ : ClosedBifun F₁) (hc₂ : ConvexBifun F₂) (hcl₂ : ClosedBifun F₂)
    (hex : IsExactSumCor3821 F₁ F₂) : ClosedBifun (infConvBifun F₁ F₂) := by
  refine closedBifun_infConvBifun (Bu := pairing m) (Bx := pairing n) hc₁ hcl₁ hc₂ hcl₂ ?_
  simpa using hex

/-- **Rockafellar, Corollary 38.2.1**, last assertion: `(F₁ □ F₂)* = cl (F₁* □ F₂*)`.

Stated in the backbone's `F⁎*` packaging, in which the right-hand `□` is infimal convolution in the
*first* variable (`infConvFstBifun`) — that is what Rockafellar's concave `F₁* □ F₂*` becomes once
the two negations are moved outside, and it keeps the whole corollary between *convex*
bifunctions, so no concave closure operation is needed.

Specialises `lowerAdjointBifun_infConvBifun_eq_clBifun`. -/
theorem corollary_38_2_1_adjoint {F₁ F₂ : Bifun (Rn m) (Rn n)}
    (h₁ : ClosedProperConvexFn (graphFn F₁)) (h₂ : ClosedProperConvexFn (graphFn F₂))
    (hex : IsExactSumCor3821 F₁ F₂) :
    lowerAdjointBifun (pairing m) (pairing n) (infConvBifun F₁ F₂)
      = clBifun (infConvFstBifun (lowerAdjointBifun (pairing m) (pairing n) F₁)
          (lowerAdjointBifun (pairing m) (pairing n) F₂)) := by
  refine lowerAdjointBifun_infConvBifun_eq_clBifun (Bu := pairing m) (Bx := pairing n) h₁ h₂ ?_
  simpa using hex

/-! ### Theorem 38.3 -/

/-- **Rockafellar, Theorem 38.3**, first assertion: for `λ > 0` the scalar multiple `Fλ`, defined
by `((Fλ)u)(x) = λ (Fu)(λ⁻¹x)`, is a convex bifunction when `F` is.

The epigraph of the graph function of `Fλ` is the image of that of `F` under the one-to-one linear
map `(u, x, μ) ↦ (u, λx, λμ)`.

Specialises `convexBifun_smulRightBifun`. -/
theorem theorem_38_3_convex {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l)
    (hF : ConvexBifun F) : ConvexBifun (smulRightBifun F l) :=
  convexBifun_smulRightBifun hl hF

/-- **Rockafellar, Theorem 38.3**, the inner-product identity: `⟨(Fλ)u, x*⟩ = λ ⟨Fu, x*⟩`.

Specialises `bracket_smulRightBifun`, which is Theorem 16.1's row `conj_smulRight` slice by
slice. -/
theorem theorem_38_3_bracket {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l) (u : Rn m)
    (y : Rn n) :
    bracket (pairing n) (smulRightBifun F l) u y = (l : EReal) * bracket (pairing n) F u y :=
  congrFun (bracket_smulRightBifun hl (pairing n) F u) y

/-- **Rockafellar, Theorem 38.3**, the adjoint formula: `(Fλ)* = F*λ` for `λ > 0`.

Right scalar multiplication commutes with taking adjoints, with no hypothesis beyond `0 < λ`.

Specialises `adjointBifun_smulRightBifun`. -/
theorem theorem_38_3_adjoint {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l) :
    dualProgram (smulRightBifun F l) = smulRightBifun (dualProgram F) l :=
  funext fun y => funext fun v => adjointBifun_smulRightBifun hl (pairing m) (pairing n) F y v

/-- **Rockafellar, Theorem 38.3**, second assertion, closedness: `Fλ` is closed when `F` is
closed convex and `λ > 0`.

`Bifunction/Cofinite.lean` used to record this as missing. It is now `closedFn_smulRight`, which
exhibits `fλ` as the conjugate of `λ f*` (Theorem 16.1's row `conj_smul`), applied to the graph
function of `F` after the shear `(u, x) ↦ (λu, x)` — Rockafellar's own change of variables
`(u, x, μ) ↦ (u, λx, λμ)`. -/
theorem theorem_38_3_closed {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l) (hF : ConvexBifun F)
    (hcl : ClosedBifun F) : ClosedBifun (smulRightBifun F l) := by
  have hcont : Continuous (scaleFst (Rn n) l : Rn m × Rn n →ₗ[ℝ] Rn m × Rn n) := by
    change Continuous fun p : Rn m × Rn n => ((l • p.1, p.2) : Rn m × Rn n)
    exact (continuous_fst.const_smul l).prodMk continuous_snd
  refine closedBifun_iff.2 ?_
  rw [graphFn_smulRightBifun hl F]
  exact closedFn_smulRight (pairingProd m n) (convexFn_compLin _ hF)
    (closedFn_compLin (closedBifun_iff.1 hcl) hcont) hl

/-- **Rockafellar, Theorem 38.3**, second assertion, properness: `Fλ` is proper when `F` is and
`λ > 0`.

Specialises `proper_smulRight`, again through `graphFn_smulRightBifun`. -/
theorem theorem_38_3_proper {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l)
    (hp : Proper (graphFn F)) : Proper (graphFn (smulRightBifun F l)) := by
  rw [graphFn_smulRightBifun hl F]
  refine proper_smulRight ⟨?_, fun p => hp.ne_bot _⟩ hl
  obtain ⟨p₀, hp₀⟩ := hp.dom_nonempty
  refine ⟨(l⁻¹ • p₀.1, p₀.2), ?_⟩
  have hq : ((l • (l⁻¹ • p₀.1), p₀.2) : Rn m × Rn n) = p₀ := by
    rw [smul_inv_smul₀ hl.ne']
  change compLin (graphFn F) (scaleFst (Rn n) l) (l⁻¹ • p₀.1, p₀.2) < ⊤
  rw [compLin_apply, scaleFst_apply, hq]
  exact mem_dom.1 hp₀

/-! ### Theorem 38.4 -/

/-- **Rockafellar, Theorem 38.4**, first assertion: the image `Ff` of a proper convex function `f`
on `ℝᵐ` under a proper convex bifunction `F` from `ℝᵐ` to `ℝⁿ`, defined by
`(Ff)(x) = inf_u {f(u) + (Fu)(x)}`, is a convex function on `ℝⁿ`.

`(u, x) ↦ f(u) + (Fu)(x)` is convex on `ℝᵐ⁺ⁿ` (Theorem 5.2) and `Ff` is its image under the
projection `(u, x) ↦ x` (Theorem 5.7).

Specialises `convexFn_imageBifun`. -/
theorem theorem_38_4_convex {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : Proper (graphFn F)) (hfp : Proper f) (hF : ConvexBifun F) (hf : ConvexFn f) :
    ConvexFn (imageBifun F f) :=
  convexFn_imageBifun (fun u x => hFp.ne_bot (u, x)) hfp.ne_bot hF hf

/-- **Rockafellar, Theorem 38.4**, the conjugacy formula: `(Ff)* = F⁎* f*`.

Rockafellar's hypothesis is that `ri (dom f)` and `ri (dom F)` have a point in common; here it is
the `IsExactSum` of Theorem 16.4 for `f` and the concave function `u ↦ ⟨Fu, x*⟩`, whose properness
field is his side condition `x* ∈ dom F*`.

Specialises `conj_imageBifun_eq_imageBifun`. -/
theorem theorem_38_4_conj {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : Proper (graphFn F)) (hf : Proper f) {y : Rn n}
    (hex : IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    conj (pairing n) (imageBifun F f) y
      = imageBifun (lowerAdjointBifun (pairing m) (pairing n) F) (conj (pairing m) f) y :=
  conj_imageBifun_eq_imageBifun (fun u x => hFp.ne_bot (u, x)) hf hex

/-- **Rockafellar, Theorem 38.4**, the attainment clause: under the same hypothesis the infimum
defining `(F⁎* f*)(x*)` is attained for each `x*`.

Specialises `exists_conj_imageBifun_eq`. -/
theorem theorem_38_4_attained {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : Proper (graphFn F)) (hf : Proper f) {y : Rn n}
    (hex : IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    ∃ v : Rn m, conj (pairing m) f v - dualProgram F y v
      = conj (pairing n) (imageBifun F f) y :=
  exists_conj_imageBifun_eq (fun u x => hFp.ne_bot (u, x)) hf hex

/-! ### Corollary 38.4.1 -/

/-- The `IsExactSum` that Corollary 38.4.1 consumes, in the surface's `.flip`-free phrasing.
Rockafellar's condition is that `ri (dom f*)` meets `ri (dom F⁎*)`. -/
abbrev IsExactSumCor3841 (F : Bifun (Rn m) (Rn n)) (f : Rn m → EReal) : Prop :=
  ∀ x : Rn n, IsExactSum (pairing m) (conj (pairing m) f)
    (fun v => -(bracket (pairing n) (lowerAdjointBifun (pairing m) (pairing n) F) v x))

/-- **Rockafellar, Corollary 38.4.1**, first assertion: `Ff` is closed, for a closed proper convex
bifunction `F` and a closed proper convex `f`. It is a conjugate.

Specialises `closedFn_imageBifun`. -/
theorem corollary_38_4_1_closed {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal} (hF : ConvexBifun F)
    (hFcl : ClosedBifun F) {u₀ : Rn m} {x₀ : Rn n} (hFp : F u₀ x₀ ≠ ⊤)
    (hf : ClosedProperConvexFn f) (hex : IsExactSumCor3841 F f) : ClosedFn (imageBifun F f) := by
  refine closedFn_imageBifun (Bu := pairing m) (Bx := pairing n) hF hFcl hFp hf ?_
  simpa using hex

/-- **Rockafellar, Corollary 38.4.1**, middle assertion: the infimum in the definition of
`(Ff)(x)` is attained for each `x`.

Specialises `exists_imageBifun_eq`. -/
theorem corollary_38_4_1_attained {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hF : ConvexBifun F) (hFcl : ClosedBifun F) {u₀ : Rn m} {x₀ : Rn n} (hFp : F u₀ x₀ ≠ ⊤)
    (hf : ClosedProperConvexFn f) (hex : IsExactSumCor3841 F f) {x : Rn n} :
    ∃ u : Rn m, f u + F u x = imageBifun F f x := by
  refine exists_imageBifun_eq (Bu := pairing m) (Bx := pairing n) hF hFcl hFp hf ?_
  simpa using hex x

/-- **Rockafellar, Corollary 38.4.1**, last assertion: `(Ff)* = cl (F⁎* f*)`.

Specialises `conj_imageBifun_eq_clFn`. -/
theorem corollary_38_4_1_conj {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal} (hF : ConvexBifun F)
    (hFcl : ClosedBifun F) {u₀ : Rn m} {x₀ : Rn n} (hFp : F u₀ x₀ ≠ ⊤)
    (hf : ClosedProperConvexFn f) (hex : IsExactSumCor3841 F f) :
    conj (pairing n) (imageBifun F f)
      = clFn (imageBifun (lowerAdjointBifun (pairing m) (pairing n) F) (conj (pairing m) f)) := by
  refine conj_imageBifun_eq_clFn (Bu := pairing m) (Bx := pairing n) hF hFcl hFp hf ?_
  simpa using hex

/-! ### Theorem 38.5 -/

/-- **Rockafellar, §38 (16428)**: `(GF)⁎ = F⁎ G⁎`. Inversion reverses the order of a product, with
the concave orientation on the right.

Specialises `inverseBifun_compBifun`. -/
theorem inverseBifun_compBifun' (G : Bifun (Rn n) (Rn k)) (F : Bifun (Rn m) (Rn n))
    (hFp : Proper (graphFn F)) (hGp : Proper (graphFn G)) :
    inverseBifun (compBifun G F) = concaveCompBifun (inverseBifun G) (inverseBifun F) :=
  inverseBifun_compBifun G F (fun u x => hFp.ne_bot (u, x)) (fun x y => hGp.ne_bot (x, y))

/-- **Rockafellar, Theorem 38.5**, first assertion: the product `GF`, defined by
`((GF)u)(y) = inf_x {(Fu)(x) + (Gx)(y)}`, is a convex bifunction from `ℝᵐ` to `ℝᵖ`.

Specialises `convexBifun_compBifun`. -/
theorem theorem_38_5_convex {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hFp : Proper (graphFn F)) (hGp : Proper (graphFn G)) (hF : ConvexBifun F)
    (hG : ConvexBifun G) : ConvexBifun (compBifun G F) :=
  convexBifun_compBifun (fun u x => hFp.ne_bot (u, x)) (fun x y => hGp.ne_bot (x, y)) hF hG

/-- **Rockafellar, Theorem 38.5**, the adjoint formula: `(GF)* = F* G*`, the product on the right
being the concave one.

Rockafellar's hypothesis is that `ri (dom F⁎)` and `ri (dom G)` have a point in common; here it is
the `IsExactSum` of Theorem 16.4 for his `f(x) = ⟨u*, F⁎x⟩` and `g(x) = ⟨Gx, y*⟩`, one instance per
`(y*, u*)` — his single condition does not depend on them, and this is the friction recorded in
`## Where the book's hypotheses had to change`.

Specialises `adjointBifun_compBifun`. -/
theorem theorem_38_5_adjoint {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hFp : Proper (graphFn F)) {z : Rn k} {v : Rn m}
    (hex : IsExactSum (pairing n) (concaveBracket (pairing m) (inverseBifun F) v)
      (fun x => -(bracket (pairing k) G x z))) :
    dualProgram (compBifun G F) z v
      = concaveCompBifun (dualProgram G) (dualProgram F) z v := by
  refine adjointBifun_compBifun (pairing m) (pairing n) (pairing k)
    (fun u x => hFp.ne_bot (u, x)) ?_
  simpa using hex

/-- **Rockafellar, Theorem 38.5**, the attainment clause: the supremum in the definition of
`((F* G*)y*)(u*)` is attained for each `u*` and `y*`.

Specialises `exists_adjointBifun_compBifun_eq`. -/
theorem theorem_38_5_attained {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hFp : Proper (graphFn F)) {z : Rn k} {v : Rn m}
    (hex : IsExactSum (pairing n) (concaveBracket (pairing m) (inverseBifun F) v)
      (fun x => -(bracket (pairing k) G x z))) :
    ∃ x : Rn n, dualProgram G z x + dualProgram F x v = dualProgram (compBifun G F) z v := by
  refine exists_adjointBifun_compBifun_eq (pairing m) (pairing n) (pairing k)
    (fun u x => hFp.ne_bot (u, x)) ?_
  simpa using hex

/-! ### Corollary 38.5.1 -/

/-- The `IsExactSum` that Corollary 38.5.1 consumes, in the surface's `.flip`-free phrasing.
Rockafellar's condition is that `ri (dom F*)` and `ri (dom G⁎*)` have a point in common. -/
abbrev IsExactSumCor3851 (F : Bifun (Rn m) (Rn n)) (G : Bifun (Rn n) (Rn k)) : Prop :=
  ∀ (u : Rn m) (y : Rn k), IsExactSum (pairing n)
    (concaveBracket (pairing m) (inverseBifun (lowerAdjointBifun (pairing m) (pairing n) F)) u)
    (fun w => -(bracket (pairing k) (lowerAdjointBifun (pairing n) (pairing k) G) w y))

/-- **Rockafellar, Corollary 38.5.1**, first assertion: `GF` is closed, for closed proper convex
`F` and `G`. It is a lower adjoint.

Specialises `closedBifun_compBifun`. -/
theorem corollary_38_5_1_closed {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hF : ClosedProperConvexFn (graphFn F)) (hG : ClosedProperConvexFn (graphFn G))
    (hex : IsExactSumCor3851 F G) : ClosedBifun (compBifun G F) := by
  refine closedBifun_compBifun (Bu := pairing m) (Bx := pairing n) (By := pairing k) hF hG ?_
  intro u y
  simpa using hex u y

/-- **Rockafellar, Corollary 38.5.1**, middle assertion: the infimum in the definition of
`((GF)u)(y)` is always attained.

Specialises `exists_compBifun_eq`. -/
theorem corollary_38_5_1_attained {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hF : ClosedProperConvexFn (graphFn F)) (hG : ClosedProperConvexFn (graphFn G))
    (hex : IsExactSumCor3851 F G) {u : Rn m} {y : Rn k} :
    ∃ x : Rn n, F u x + G x y = compBifun G F u y := by
  refine exists_compBifun_eq (Bu := pairing m) (Bx := pairing n) (By := pairing k) hF hG ?_
  simpa using hex u y

/-- **Rockafellar, Corollary 38.5.1**, last assertion: `(GF)* = cl (F* G*)`, in the backbone's
`F⁎*` packaging `(GF)⁎* = cl (G⁎* F⁎*)`. Inversion reverses the order twice, so the product on the
right is taken in the same order as `GF`.

Specialises `lowerAdjointBifun_compBifun_eq_clBifun`. -/
theorem corollary_38_5_1_adjoint {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hF : ClosedProperConvexFn (graphFn F)) (hG : ClosedProperConvexFn (graphFn G))
    (hex : IsExactSumCor3851 F G) :
    lowerAdjointBifun (pairing m) (pairing k) (compBifun G F)
      = clBifun (compBifun (lowerAdjointBifun (pairing n) (pairing k) G)
          (lowerAdjointBifun (pairing m) (pairing n) F)) := by
  refine lowerAdjointBifun_compBifun_eq_clBifun (Bu := pairing m) (Bx := pairing n)
    (By := pairing k) hF hG ?_
  intro u y
  simpa using hex u y

/-! ### Lemma 38.6 -/

/-- **Rockafellar, Lemma 38.6**, first assertion: if `⟨f, g⟩` exists then so does `⟨f*, g*⟩`.

Rockafellar's proof is the four-term chain
`−⟨f, g⟩ ≤ ⟨f*, g*⟩_sup ≤ ⟨f*, g*⟩_inf ≤ −⟨f, g⟩`, whose middle link is weak duality
(`fenchelSup_le_innerProduct`); when the two ends coincide, all four terms do.

Specialises `hasFenchelPairing_conj`. -/
theorem lemma_38_6_exists {f g : Rn n → EReal} (hf : Proper f) (hg : ProperConcave g)
    (h : HasInnerProduct f g) :
    HasInnerProduct (conj (pairing n) f) (concaveConj (pairing n) g) := by
  simpa using hasFenchelPairing_conj (B := pairing n) hf hg h

/-- **Rockafellar, Lemma 38.6**, the value: `⟨f*, g*⟩ = −⟨f, g⟩`.

Specialises `fenchelPairing_conj`. -/
theorem lemma_38_6 {f g : Rn n → EReal} (hf : Proper f) (hg : ProperConcave g)
    (h : HasInnerProduct f g) :
    innerProduct (conj (pairing n) f) (concaveConj (pairing n) g) = -(innerProduct f g) := by
  simpa using fenchelPairing_conj (B := pairing n) hf hg h

/-! ### Theorem 38.7 and Corollary 38.7.1 -/

/-- **Rockafellar, Corollary 38.7.1**, existence: `⟨f, F*x*⟩` exists for every `x*`.

Weak duality supplies one inequality for free; the other is Theorem 38.4.

Specialises `hasFenchelPairing_adjointBifun`. -/
theorem corollary_38_7_1_exists {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : Proper (graphFn F)) (hf : Proper f) {y : Rn n}
    (hex : IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    HasInnerProduct f (dualProgram F y) :=
  hasFenchelPairing_adjointBifun (fun u x => hFp.ne_bot (u, x)) hf hex

/-- **Rockafellar, Corollary 38.7.1**: `⟨Ff, x*⟩ = ⟨f, F*x*⟩` — an adjoint moves across the inner
product.

The left-hand side is Rockafellar's `⟨Ff, x*⟩`, i.e. `(Ff)*(x*)`; the right-hand side is the inner
product of the convex `f` with the concave function `F*x*`.

Specialises `conj_imageBifun_eq_fenchelPairing`. -/
theorem corollary_38_7_1 {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : Proper (graphFn F)) (hf : Proper f) {y : Rn n}
    (hex : IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    conj (pairing n) (imageBifun F f) y = innerProduct f (dualProgram F y) :=
  conj_imageBifun_eq_fenchelPairing (fun u x => hFp.ne_bot (u, x)) hf hex

/-- **Rockafellar, Theorem 38.7**, first equality: `⟨Ff, g*⟩ = ⟨f, F*g*⟩`.

Rockafellar's hypothesis is that some `u` in `ri (dom f) ∩ ri (dom F)` has `ri (dom (Fu))` meeting
`ri (dom g)`; here it is the `IsExactSum` interface (one instance per `x*`) together with a common
point `(u₀, x₀)` at which `f`, `F` and `g` are all finite. Both sides are the *inf* sides of the two
inner products, each of which is Rockafellar's `⟨·, ·⟩` as soon as the corresponding pairing exists
— for the right-hand side that is `corollary_38_7_1_exists`.

Specialises `fenchelInf_imageBifun_eq_fenchelInf_concaveImageBifun`. -/
theorem theorem_38_7 {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal} {g : Rn n → EReal}
    (hFp : Proper (graphFn F)) (hf : Proper f) (hgd : (domConcave g).Nonempty) {u₀ : Rn m}
    {x₀ : Rn n} (hF : F u₀ x₀ ≠ ⊤) (hfu : f u₀ ≠ ⊤) (hgb : g x₀ ≠ ⊥) (hgt : g x₀ ≠ ⊤)
    (hex : ∀ y : Rn n, IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    innerProduct (imageBifun F f) (concaveConj (pairing n) g)
      = innerProduct f (concaveImageBifun (dualProgram F) (concaveConj (pairing n) g)) :=
  fenchelInf_imageBifun_eq_fenchelInf_concaveImageBifun (Bu := pairing m) (Bx := pairing n)
    (fun u x => hFp.ne_bot (u, x)) hf hgd hF hfu hgb hgt hex

/-- **Rockafellar, Theorem 38.7**, last equality: `⟨F⁎*f*, g⟩ = −⟨Ff, g*⟩`.

The left-hand side is the *sup* side of `⟨F⁎*f*, g⟩`; Rockafellar obtains the equality "by
definition", both sides unwinding to the same double extremum.

Specialises `fenchelSup_imageBifun_lowerAdjointBifun_eq_neg`. -/
theorem theorem_38_7_third {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal} {g : Rn n → EReal}
    (hFp : Proper (graphFn F)) (hf : Proper f) (hgd : (domConcave g).Nonempty) {u₀ : Rn m}
    {x₀ : Rn n} (hF : F u₀ x₀ ≠ ⊤) (hfu : f u₀ ≠ ⊤)
    (hex : ∀ y : Rn n, IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    fenchelSup (pairing n)
        (imageBifun (lowerAdjointBifun (pairing m) (pairing n) F) (conj (pairing m) f)) g
      = -(innerProduct (imageBifun F f) (concaveConj (pairing n) g)) := by
  have h := fenchelSup_imageBifun_lowerAdjointBifun_eq_neg (Bu := pairing m) (Bx := pairing n)
    (F := F) (f := f) (g := g) (fun u x => hFp.ne_bot (u, x)) hf hgd hF hfu hex
  rw [flip_pairing] at h
  exact h

/-! ### Corollary 38.7.2 -/

/-- **Rockafellar, `Corollary 38.7.2`**, the existence clause: `⟨Fu, G*y*⟩` exists.

Rockafellar derives his hypothesis — that `ri (dom (Fu))` meets `ri (dom G)` — from the condition
on `ri (dom F⁎) ∩ ri (dom G)` by a calculus of relative interiors he leaves to the reader (16691);
here it is the `IsExactSum` the proof consumes.

Specialises `hasFenchelPairing_adjointBifun_slice`. -/
theorem corollary_38_7_2_exists {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hGp : Proper (graphFn G)) {u : Rn m} (hFu : Proper (F u)) {z : Rn k}
    (hex : IsExactSum (pairing n) (F u) (fun x => -(bracket (pairing k) G x z))) :
    HasInnerProduct (F u) (dualProgram G z) :=
  hasFenchelPairing_adjointBifun_slice (pairing n) (pairing k)
    (fun x y => hGp.ne_bot (x, y)) hFu hex

/-- **Rockafellar, `Corollary 38.7.2`**, first equality: `⟨GFu, y*⟩ = ⟨Fu, G*y*⟩`.

This is Corollary 38.7.1 read at the slice `Fu`, since a slice of a product is the image of a
slice, `(GF)u = G(Fu)`.

Specialises `bracket_compBifun_eq_fenchelPairing`. -/
theorem corollary_38_7_2_first {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hGp : Proper (graphFn G)) {u : Rn m} (hFu : Proper (F u)) {z : Rn k}
    (hex : IsExactSum (pairing n) (F u) (fun x => -(bracket (pairing k) G x z))) :
    bracket (pairing k) (compBifun G F) u z = innerProduct (F u) (dualProgram G z) :=
  bracket_compBifun_eq_fenchelPairing (pairing n) (pairing k)
    (fun x y => hGp.ne_bot (x, y)) hFu hex

/-- **Rockafellar, `Corollary 38.7.2`**, second equality: `⟨GFu, y*⟩ = ⟨u, F*G*y*⟩`, valid at
every `u` in `ri (dom (GF))`.

This is Corollary 33.2.1 together with Theorem 38.5, and unlike the first equality it genuinely
needs the relative interior.

Specialises `bracket_compBifun_eq_concaveBracket_concaveCompBifun`. -/
theorem corollary_38_7_2_second {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hFp : Proper (graphFn F)) (hGF : ConvexBifun (compBifun G F)) {u : Rn m}
    (hu : u ∈ ri (domBifun (compBifun G F))) {z : Rn k}
    (hex : ∀ v : Rn m, IsExactSum (pairing n) (concaveBracket (pairing m) (inverseBifun F) v)
      (fun x => -(bracket (pairing k) G x z))) :
    bracket (pairing k) (compBifun G F) u z
      = concaveBracket (pairing m) (concaveCompBifun (dualProgram G) (dualProgram F)) u z := by
  refine bracket_compBifun_eq_concaveBracket_concaveCompBifun (pairing m) (pairing n) (pairing k)
    (fun u x => hFp.ne_bot (u, x)) hGF hu ?_
  intro v
  simpa using hex v

/-! ### The closing discussion: co-finite bifunctions (16693–16729) -/

/-- **Rockafellar, §38 (16695)**, forward: for a co-finite convex bifunction the inner product
`⟨Fu, x*⟩` is finite for all `u` and `x*`. This is Corollary 13.3.1 read at the slice `Fu`.

Specialises `CofiniteBifun.bracket_lt_top` and `CofiniteBifun.bracket_ne_bot`. -/
theorem cofiniteBifun_bracket_finite {F : Bifun (Rn m) (Rn n)} (hF : CofiniteBifun F) (u : Rn m)
    (y : Rn n) : bracket (pairing n) F u y ≠ ⊥ ∧ bracket (pairing n) F u y ≠ ⊤ :=
  ⟨CofiniteBifun.bracket_ne_bot (Bx := pairing n) hF u y,
    (CofiniteBifun.bracket_lt_top (Bx := pairing n) hF u y).ne⟩

/-- **Rockafellar, §38 (16695)**: a closed convex bifunction is co-finite **if and only if**
`⟨Fu, x*⟩` is finite for all `u` and `x*`.

Specialises `cofiniteBifun_of_forall_bracket_lt_top` and `CofiniteBifun.bracket_lt_top`. -/
theorem cofinite_iff_forall_bracket_finite {F : Bifun (Rn m) (Rn n)} (hF : ConvexBifun F)
    (hcl : ∀ u, ClosedProperConvexFn (F u)) :
    CofiniteBifun F ↔ ∀ (u : Rn m) (y : Rn n), bracket (pairing n) F u y < ⊤ :=
  ⟨fun h u y => CofiniteBifun.bracket_lt_top (Bx := pairing n) h u y,
    cofiniteBifun_of_forall_bracket_lt_top hF hcl⟩

/-- **Rockafellar, §38 (16698)**: for a co-finite `F` the two inner products agree at *every* `u`,
`⟨Fu, x*⟩ = ⟨u, F*x*⟩`. This is Corollary 33.2.1 with `ri (dom F) = ℝᵐ`.

Specialises `CofiniteBifun.bracket_eq_concaveBracket_adjointBifun`. -/
theorem cofiniteBifun_bracket_eq {F : Bifun (Rn m) (Rn n)} (hF : CofiniteBifun F) (u : Rn m)
    (y : Rn n) :
    bracket (pairing n) F u y = concaveBracket (pairing m) (dualProgram F) u y :=
  CofiniteBifun.bracket_eq_concaveBracket_adjointBifun (pairing m) (pairing n) hF u y

/-- **Rockafellar, §38 (16705)**: the infimal convolution of two co-finite convex bifunctions is
co-finite.

Specialises `cofiniteBifun_infConvBifun`. -/
theorem cofinite_infConvBifun' {F₁ F₂ : Bifun (Rn m) (Rn n)} (hF₁ : CofiniteBifun F₁)
    (hF₂ : CofiniteBifun F₂) : CofiniteBifun (infConvBifun F₁ F₂) :=
  cofiniteBifun_infConvBifun (pairing n) hF₁ hF₂

/-- **Rockafellar, §38 (16708)**: `(F₁ □ F₂)* = F₁* □ F₂*` for co-finite bifunctions, with
Theorem 38.2's relative-interior hypothesis discharged — the brackets are finite everywhere, so
`IsExactSum.of_relint` applies at the origin.

Specialises `adjointBifun_infConvBifun_of_cofinite`. -/
theorem cofinite_adjoint_infConvBifun {F₁ F₂ : Bifun (Rn m) (Rn n)} (hF₁ : CofiniteBifun F₁)
    (hF₂ : CofiniteBifun F₂) :
    dualProgram (infConvBifun F₁ F₂) = supConvBifun (dualProgram F₁) (dualProgram F₂) :=
  adjointBifun_infConvBifun_of_cofinite (pairing m) (pairing n) hF₁ hF₂

/-- **Rockafellar, §38 (16711)**: the operation `F ↦ Fλ`, `λ > 0`, likewise preserves
co-finiteness.

Specialises `cofiniteBifun_smulRightBifun`, one of the two co-finiteness facts added to
`Bifunction/Cofinite.lean` with this section (remediation §12.12). -/
theorem cofinite_smulRightBifun' {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hF : CofiniteBifun F)
    (hl : 0 < l) : CofiniteBifun (smulRightBifun F l) :=
  cofiniteBifun_smulRightBifun (pairing n) hF hl

/-- **Rockafellar, §38 (16701)**: a closed proper convex bifunction `F` from `ℝᵐ` to `ℝⁿ` is
co-finite **if and only if** `dom F = ℝᵐ` and `dom F* = ℝⁿ`.

Rockafellar cites Theorem 34.2 for this. The backbone's proof does not go through the
saddle-function correspondence: `dom F = ℝᵐ` is what makes every bracket `⟨Fu, x*⟩` finite below
and `dom F* = ℝⁿ` is what makes it finite above, and Corollary 13.3.1 slice by slice does the rest.

Specialises `cofiniteBifun_iff_domBifun_eq_univ`, the second of the two facts added to
`Bifunction/Cofinite.lean` with this section (remediation §12.12). -/
theorem cofiniteBifun_of_domBifun_eq_univ' {F : Bifun (Rn m) (Rn n)} (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hp : Proper (graphFn F)) :
    CofiniteBifun F ↔ domBifun F = univ ∧ domConcaveBifun (dualProgram F) = univ :=
  cofiniteBifun_iff_domBifun_eq_univ (Bu := pairing m) (Bx := pairing n) hF hcl hp

end Rockafellar
