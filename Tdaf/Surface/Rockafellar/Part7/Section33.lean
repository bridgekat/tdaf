/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Bifunction.ProcessDuality
import Tdaf.Analysis.Convex.Saddle.Conjugate
import Tdaf.Surface.Rockafellar.Part6.Section30

/-!
# Rockafellar, §33: Saddle-Functions

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §33, pp. 349–358: **concave-convex** and
**convex-concave** functions, the two partial closure operations `cl₁` and `cl₂`, and the
correspondence — "at the heart of the theory of saddle-functions" — between saddle-functions on
`ℝᵐ × ℝⁿ` and convex bifunctions from `ℝᵐ` to `ℝⁿ`.

All eleven numbered results are here: Theorems 33.1, 33.2, 33.3 and Corollaries 33.1.1, 33.1.2,
33.1.3, 33.2.1, 33.2.2, 33.3.1, 33.3.2, 33.3.3.

**This module is the vocabulary gate for §§34–37.** Every notion §33 introduces is exported from
here under the book's own name; the tables below are the contract the later sections read.

## The orientation convention, stated once

Rockafellar writes a concave-convex `K (u, v)`: **concave in `u`**, the first argument, and
**convex in `v`**, the second. The two closure operations are named after the *argument* they close,
not after the sense in which they close it:

| book | this module | backbone | closes | in which argument |
|---|---|---|---|---|
| `cl₁ K = cl_u K` | `cl₁` | `partialCl₁` | **concavely** | the **first**, the concave one |
| `cl₂ K = cl_v K` | `cl₂` | `partialCl₂` | **convexly** | the **second**, the convex one |

The book's own mnemonic (14409) fixes the derived pair: `K` is **lower closed** when
`cl₂ (cl₁ K) = K`, because lower closedness entails *lower* semicontinuity in the argument for which
that is natural — the **convex** one; `K` is **upper closed** when `cl₁ (cl₂ K) = K`, upper
semicontinuity in the **concave** argument. The backbone's `lowerCl = partialCl₂ ∘ partialCl₁` and
`upperCl = partialCl₁ ∘ partialCl₂` are exactly these, and `LowerClosedFn`, `UpperClosedFn` their
fixed points. `cl₁` therefore appears *innermost* in the lower closure and *outermost* in the upper
one. Reversing any of this silently swaps every statement of §§34–37.

For a *convex-concave* `K` the book exchanges the two words (14411); the backbone does not carry a
second pair of definitions for that case, because `saddleSwap K = fun (v, u) => -K (u, v)` turns a
convex-concave function into a concave-convex one and exchanges `cl₁` with `cl₂`
(`partialCl₁_saddleSwap`, `partialCl₂_saddleSwap`). `convexConcave_lowerClosed_iff` and
`convexConcave_upperClosed_iff` record the translation.

## The three brackets

Rockafellar overloads `⟨·, ·⟩` three ways in this section (and a fourth in §38). They are **distinct
names** here, never one:

| book | this module | meaning |
|---|---|---|
| `⟨f, x*⟩ = ⟨x*, f⟩ = f*(x*)` (14113) | `conjBracket` | the conjugate of a convex `f` |
| the same for concave `f` | `concaveConjBracket` | the concave conjugate |
| `⟨Fu, x*⟩ = (Fu)*(x*)` (14119) | `bifunBracket` | of a **convex** bifunction `F` |
| `⟨u, Gx*⟩ = (Gx*)*(u)` | `concaveBifunBracket` | of a **concave** bifunction `G` |
| `⟨u, F*x*⟩` | `adjointBracket` | the previous one at `G = F*` |

`bifunBracket F` and `adjointBracket F` are the pair `(K̲, K̄)` of Corollary 33.3.1; they are
uncurried, as functions of the pair `(u, x*)`, because that is the form every closure operation and
every closedness predicate is stated against.

## Contents

| label | declaration |
|---|---|
| §33 definitions, 14093 | `cl₁`, `cl₂` |
| §33 definitions, 14113–14127 | `conjBracket`, `concaveConjBracket`, `bifunBracket`,
  `concaveBifunBracket`, `adjointBracket`, `bifunOfSaddleFn`, `bifunBracket_apply`,
  `concaveBifunBracket_apply`, `bifunOfSaddleFn_apply`, `conjBracket_indicatorFn` |
| Theorem 33.1 | `theorem_33_1_concaveConvex`, `theorem_33_1_convexClosed`,
  `theorem_33_1_inversion`, `theorem_33_1_convexBifun`, `theorem_33_1_imageClosed`,
  `theorem_33_1_bracket_eq` |
| Corollary 33.1.1 | `corollary_33_1_1_cl₁_concaveConvex`, `corollary_33_1_1_cl₂_concaveConvex`,
  `corollary_33_1_1_cl₁_concaveClosed`, `corollary_33_1_1_cl₂_convexClosed` |
| §33 definition, 14205 | `imageClosedBifun_of_closedBifun` |
| Corollary 33.1.2 | `corollary_33_1_2`, `corollary_33_1_2_apply`, `corollary_33_1_2_symm_apply` |
| Corollary 33.1.3 | `corollary_33_1_3_convex`, `corollary_33_1_3_concave`,
  `corollary_33_1_3_inversion` |
| §33 remark, 14241 | `adjointBracket_concaveConvex`, `adjointBracket_concaveClosed` |
| Theorem 33.2 | `theorem_33_2_first`, `theorem_33_2_second` |
| Corollary 33.2.1 | `corollary_33_2_1_primal`, `corollary_33_2_1_dual` |
| Corollary 33.2.2 | `corollary_33_2_2`, `corollary_33_2_2_exceptional` |
| §33 definitions, 14371–14415 | `convexClosedFn_of_finite`, `fullyClosedFn_of_finite`,
  `fullyClosed_iff_lowerClosed_and_upperClosed`, `convexConcave_lowerClosed_iff`,
  `convexConcave_upperClosed_iff` |
| Theorem 33.3 | `theorem_33_3_lowerClosed`, `theorem_33_3` |
| Corollary 33.3.1 | `corollary_33_3_1`, `corollary_33_3_1_necessity_first`,
  `corollary_33_3_1_necessity_second`, `corollary_33_3_1_lowerClosed`,
  `corollary_33_3_1_upperClosed`, `corollary_33_3_1_le` |
| Corollary 33.3.2 | `corollary_33_3_2`, `corollary_33_3_2_apply`, `corollary_33_3_2_symm_apply` |
| Corollary 33.3.3 | `corollary_33_3_3_lowerClosed`, `corollary_33_3_3_upperClosed`,
  `corollary_33_3_3`, `corollary_33_3_3_bracket`, `corollary_33_3_3_adjointBracket`,
  `corollary_33_3_3_dom`, `corollary_33_3_3_domAdjoint`,
  `corollary_33_3_3_bifun_of_mem`, `corollary_33_3_3_bifun_of_notMem`,
  `corollary_33_3_3_adjoint_of_mem`, `corollary_33_3_3_adjoint_of_notMem` |

## What §33 exports, by book name

Everything below is the backbone's, used verbatim, unless a `Rockafellar.` name is given. The
`Rockafellar.` names are `abbrev`s — reducible, so they *are* the backbone object and not a copy —
introduced only where a Euclidean pairing has to be supplied, plus `cl₁` and `cl₂`, where the
book's name and the backbone's differ.

* concave-convex, convex-concave, saddle-function — `ConcaveConvexFn`, `ConvexConcaveFn`, `SaddleFn`
* lower / upper simple extension `K₁`, `K₂` — `lowerSimpleExt C D K`, `upperSimpleExt C D K`
* `cl₂ K` (convex closure), `cl₁ K` (concave closure) — `Rockafellar.cl₂`, `Rockafellar.cl₁`
* convex-closed, concave-closed — `ConvexClosedFn`, `ConcaveClosedFn`
* `⟨f, x*⟩` — `Rockafellar.conjBracket`, `Rockafellar.concaveConjBracket`
* `⟨Fu, x*⟩`, `⟨u, Gx*⟩`, `⟨u, F*x*⟩` — `Rockafellar.bifunBracket`,
  `Rockafellar.concaveBifunBracket`, `Rockafellar.adjointBracket`
* `Fu = K(u, ·)*` — `Rockafellar.bifunOfSaddleFn`
* image-closed bifunction — `ImageClosedBifun`
* fully closed — `FullyClosedFn`; lower closed, upper closed — `LowerClosedFn`, `UpperClosedFn`
* lower closure `cl₂ cl₁ K`, upper closure `cl₁ cl₂ K` — `lowerCl`, `upperCl` (§34's names, defined
  in `Saddle/Closure.lean`; §33 needs them to say what lower and upper closedness *are*)
* `F*` — `Rockafellar.dualProgram` (§30, `Part6/Section30.lean`)
* the orientation flip — `saddleSwap`, `swapReal` (`Saddle/{Closure,Kernel}.lean`)

## Where the book is defective

**Corollary 33.1.2 is printed with no proof, and with no terminating period on its label** (14207) —
it is one of the ten punctuation-damaged labels of the book. It is proved here, as an `Equiv`, from
the two halves of Theorem 33.1.

**Corollary 33.2.1's second assertion is proved by "applying the first fact to `F*`"** (14293). That
substitution is not available verbatim, because `F*` is a *concave* bifunction while the first
assertion is stated for a convex one; the honest route runs Theorem 33.2's second equation and the
convex — not concave — "a function agrees with its closure on `ri (dom)`". That is what
`corollary_33_2_1_dual` does, and it is why the book's hypothesis "`F` closed" is needed there and
nowhere else in the corollary.

**Theorem 33.3's proof asserts "for image-closed convex bifunctions `F`, the latter condition is
equivalent to `cl F = F`"** (14431) with no argument. It is `eq_of_bracket_eq`
(`Saddle/Correspondence.lean`), whose content is that the bracket sees only `cl (F u)`.

## What is not here

**Nothing numbered is omitted.** All eleven results have declarations.

The unnumbered material of the section is carried as follows. The bilinear motivating example
(14105) is `dualProgram_linearIndicatorBifun` in `Part6/Section30.lean`, already proved there. The
"oriented bifunction" device of 14143 is *omitted with a reason*: Rockafellar himself says it "is
not worth the effort in the present case", and the ambiguity it would resolve — an affine graph
function readable as convex or as concave — cannot arise here, because `bifunBracket` and
`concaveBifunBracket` are different names taking arguments of different types. The convex-program
reading of the inner-product equation (14335–14395), which identifies `⟨Fu, x*⟩ = ⟨u, F*x*⟩` with
normality of a translated dual pair `(Q), (Q*)`, is *deferred by scope*: it is a restatement of §30
in §33's notation, and each ingredient of it is already a numbered result of §30 — `theorem_30_3`
and `corollary_30_2_1_primal` in `Part6/Section30.lean`.

## Backbone friction

Two items, recorded in full in the section report.

* `dom₂_concaveBracket` does not exist, though its mirror `dom₁_bracket` does
  (`Saddle/Conjugate.lean`). `corollary_33_3_3_domAdjoint` needs it, and it is proved `private`
  here as `dom₂_concaveBifunBracket`.
* **Corollary 33.2.1's dual half lives in `Bifunction/ProcessDuality.lean`**, a §39 module, rather
  than in `Saddle/Kernel.lean` beside its primal half. That is the only reason this file imports a
  §39 backbone module.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §33, pp. 349–358.
-/

open Set

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

/-! ### The two partial closures

`cl₁` closes the **concave** argument, `cl₂` the **convex** one. See the module docstring; this is
the single convention the whole of Part VII rests on. -/

/-- **Rockafellar's `cl₂ K = cl_v K`** (14093), the **convex closure** of a saddle-function: close
`K (u, ·)` as a convex function of the **second** argument, for each fixed `u`.

A reducible `abbrev` for the backbone's `partialCl₂`, so this *is* that operator. -/
noncomputable abbrev cl₂ {m n : ℕ} (K : Rn m × Rn n → EReal) : Rn m × Rn n → EReal :=
  partialCl₂ K

/-- **Rockafellar's `cl₁ K = cl_u K`** (14093), the **concave closure** of a saddle-function: close
`K (·, v)` as a *concave* function of the **first** argument, for each fixed `v`.

A reducible `abbrev` for the backbone's `partialCl₁`. Note the asymmetry — `cl₁` is not `cl₂` with
the arguments exchanged; it is `cl₂` conjugated by negation as well (`partialCl₁_saddleSwap`). -/
noncomputable abbrev cl₁ {m n : ℕ} (K : Rn m × Rn n → EReal) : Rn m × Rn n → EReal :=
  partialCl₁ K

/-! ### The three brackets -/

section Brackets

variable {m n : ℕ}

/-- **Rockafellar's `⟨f, x*⟩ = ⟨x*, f⟩ = f*(x*)`** (14113) for a **convex** `f`: the conjugate,
written as an inner product so that the analogy with linear algebra can be pressed. -/
noncomputable abbrev conjBracket (f : Rn n → EReal) : Rn n → EReal := conj (pairing n) f

/-- **Rockafellar's `⟨f, x*⟩`** (14113) for a **concave** `f`: the *concave* conjugate. The book
uses one notation for both and disambiguates by context; two names are used here. -/
noncomputable abbrev concaveConjBracket (f : Rn n → EReal) : Rn n → EReal :=
  concaveConj (pairing n) f

/-- **Rockafellar's `⟨Fu, x*⟩ = (Fu)*(x*) = sup_x {⟨x, x*⟩ - (Fu)(x)}`** (14119) for a **convex**
bifunction `F`, read as a function of the pair `(u, x*)`.

This is the `K̲` of Corollary 33.3.1 and the lower closed member of every equivalence class of
§34. -/
noncomputable abbrev bifunBracket (F : Bifun (Rn m) (Rn n)) : Rn m × Rn n → EReal :=
  saddleOfBifun (pairing n) F

/-- **Rockafellar's `⟨u, Gx*⟩ = (Gx*)*(u) = inf_v {⟨u, v⟩ - (Gx*)(v)}`** (14127) for a **concave**
bifunction `G` from `ℝⁿ` to `ℝᵐ`, read as a function of the pair `(u, x*)`. -/
noncomputable abbrev concaveBifunBracket (G : Bifun (Rn n) (Rn m)) : Rn m × Rn n → EReal :=
  fun p => concaveBracket (pairing m) G p.1 p.2

/-- **Rockafellar's `⟨u, F*x*⟩`**: the concave bracket of the adjoint `F*` of a convex bifunction
(§30, `dualProgram`). This is the `K̄` of Corollary 33.3.1 and the upper closed member of the
class. -/
noncomputable abbrev adjointBracket (F : Bifun (Rn m) (Rn n)) : Rn m × Rn n → EReal :=
  concaveBifunBracket (dualProgram F)

/-- **The convex bifunction attached to a saddle-function**, `Fu = K (u, ·)*` — the second half of
Theorem 33.1 and the inverse map of Corollaries 33.1.2 and 33.3.2. -/
noncomputable abbrev bifunOfSaddleFn (K : Rn m × Rn n → EReal) : Bifun (Rn m) (Rn n) :=
  bifunOfSaddle (pairing n) K

/-- The book's defining formula for `⟨Fu, x*⟩` (14121): `sup_x {⟨x, x*⟩ - (Fu)(x)}`. -/
theorem bifunBracket_apply (F : Bifun (Rn m) (Rn n)) (p : Rn m × Rn n) :
    bifunBracket F p = ⨆ x : Rn n, ((pairing n x p.2 : ℝ) : EReal) - F p.1 x := rfl

/-- The book's defining formula for `⟨u, Gx*⟩` (14125): `inf_v {⟨u, v⟩ - (Gx*)(v)}`. -/
theorem concaveBifunBracket_apply (G : Bifun (Rn n) (Rn m)) (p : Rn m × Rn n) :
    concaveBifunBracket G p = ⨅ v : Rn m, ((pairing m p.1 v : ℝ) : EReal) - G p.2 v := rfl

/-- The book's defining formula for `Fu = K (u, ·)*` (14173). -/
theorem bifunOfSaddleFn_apply (K : Rn m × Rn n → EReal) (u : Rn m) (x : Rn n) :
    bifunOfSaddleFn K u x = ⨆ y : Rn n, ((pairing n x y : ℝ) : EReal) - K (u, y) := rfl

/-- **`⟨f, x*⟩ = ⟨x, x*⟩` when `f` is the indicator of the point `x`** (14115). This is
Rockafellar's justification for the inner-product notation: it extends the ordinary inner product
along the embedding of a point of `ℝⁿ` into the convex functions on `ℝⁿ`. -/
theorem conjBracket_indicatorFn (x y : Rn n) :
    conjBracket (indicatorFn ({x} : Set (Rn n))) y = ((pairing n x y : ℝ) : EReal) :=
  congrFun ((supportFn_eq_conj_indicatorFn (pairing n) {x}).symm.trans
    (supportFn_singleton (pairing n) x)) y

end Brackets

/-! ### Theorem 33.1 -/

section Thm331

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Rockafellar, Theorem 33.1**, first clause: for a convex bifunction `F`, `⟨Fu, x*⟩` is a
**concave-convex** function of `(u, x*)`.

Specialises `concaveConvexFn_bracket`. Convexity in `x*` is free — it is a conjugate; concavity in
`u` is the clause with content, and is Theorem 5.7 applied to the image of the graph function under
the projection `(u, x) ↦ u`. -/
theorem theorem_33_1_concaveConvex (hF : ConvexBifun F) : ConcaveConvexFn (bifunBracket F) :=
  concaveConvexFn_bracket hF (pairing n)

/-- **Rockafellar, Theorem 33.1**, second clause: `⟨Fu, x*⟩` is **convex-closed**, with no
hypothesis on `F` whatever.

Specialises `convexClosedFn_saddleOfBifun`. Each slice is a conjugate, and a conjugate is closed. -/
theorem theorem_33_1_convexClosed (F : Bifun (Rn m) (Rn n)) : ConvexClosedFn (bifunBracket F) :=
  convexClosedFn_saddleOfBifun

/-- **Rockafellar, Theorem 33.1**, the inversion formula:
`(cl (Fu))(x) = sup_{x*} {⟨x, x*⟩ - ⟨Fu, x*⟩}`.

Specialises `clFn_eq_conj_bracket`, which is Fenchel–Moreau (Theorem 12.2) uniformly in `u`. -/
theorem theorem_33_1_inversion (hF : ConvexBifun F) (u : Rn m) (x : Rn n) :
    clFn (F u) x = ⨆ y : Rn n, ((pairing n x y : ℝ) : EReal) - bifunBracket F (u, y) :=
  congrFun (clFn_eq_conj_bracket (Bx := pairing n) hF u) x

/-- **Rockafellar, Theorem 33.1**, converse: for a concave-convex `K`, the bifunction
`(Fu)(x) = sup_{x*} {⟨x, x*⟩ - K (u, x*)}` is **convex**.

Specialises `convexBifun_bifunOfSaddle`. The graph function is a pointwise supremum of jointly
convex functions of `(u, x)`, which is the whole of the book's argument. -/
theorem theorem_33_1_convexBifun (hK : ConcaveConvexFn K) : ConvexBifun (bifunOfSaddleFn K) :=
  convexBifun_bifunOfSaddle hK (pairing n)

/-- **Rockafellar, Theorem 33.1**, converse: that bifunction is **image-closed** — `Fu` is a closed
function on `ℝⁿ` for every `u`.

Specialises `imageClosedBifun_bifunOfSaddle`; each `Fu` is a conjugate. -/
theorem theorem_33_1_imageClosed (K : Rn m × Rn n → EReal) :
    ImageClosedBifun (bifunOfSaddleFn K) :=
  imageClosedBifun_bifunOfSaddle

/-- **Rockafellar, Theorem 33.1**, converse, the identity that closes the loop:
`⟨Fu, x*⟩ = (cl₂ K)(u, x*)`.

Specialises `bracket_bifunOfSaddle`. Note `cl₂`, the closure in the **convex** (second) argument. -/
theorem theorem_33_1_bracket_eq (hK : ConcaveConvexFn K) :
    bifunBracket (bifunOfSaddleFn K) = cl₂ K :=
  funext fun p => bracket_bifunOfSaddle (Bx := pairing n) hK p

end Thm331

/-! ### Corollary 33.1.1 -/

section Cor3311

variable {m n : ℕ} {K : Rn m × Rn n → EReal}

/-- **Rockafellar, Corollary 33.1.1**: `cl₁ K` is again concave-convex.

Specialises `concaveConvexFn_partialCl₁`. -/
theorem corollary_33_1_1_cl₁_concaveConvex (hK : ConcaveConvexFn K) :
    ConcaveConvexFn (cl₁ K) :=
  concaveConvexFn_partialCl₁ (pairing m) hK

/-- **Rockafellar, Corollary 33.1.1**: `cl₂ K` is again concave-convex.

Specialises `concaveConvexFn_partialCl₂`. -/
theorem corollary_33_1_1_cl₂_concaveConvex (hK : ConcaveConvexFn K) :
    ConcaveConvexFn (cl₂ K) :=
  concaveConvexFn_partialCl₂ (pairing n) hK

/-- **Rockafellar, Corollary 33.1.1**: `cl₁ K` is **concave-closed**.

Specialises `concaveClosedFn_partialCl₁`; the concave closure is idempotent. -/
theorem corollary_33_1_1_cl₁_concaveClosed (K : Rn m × Rn n → EReal) :
    ConcaveClosedFn (cl₁ K) :=
  concaveClosedFn_partialCl₁ K

/-- **Rockafellar, Corollary 33.1.1**: `cl₂ K` is **convex-closed**.

Specialises `convexClosedFn_partialCl₂`. -/
theorem corollary_33_1_1_cl₂_convexClosed (K : Rn m × Rn n → EReal) :
    ConvexClosedFn (cl₂ K) :=
  convexClosedFn_partialCl₂ K

end Cor3311


/-! ### Corollary 33.1.2

Rockafellar prints the statement with **no proof at all** (14207), and its label is one of the ten
in the book that a naive extractor loses — `COROLLARY 33.1.2` carries no terminating period. -/

section Cor3312

variable {m n : ℕ}

/-- **`F` closed implies `F` image-closed** (14205): a slice of a closed function is closed. This
is the parenthetical remark that accompanies the definition of image-closedness. -/
theorem imageClosedBifun_of_closedBifun {F : Bifun (Rn m) (Rn n)} (hF : ClosedBifun F) :
    ImageClosedBifun F :=
  hF.imageClosedBifun

/-- **Rockafellar, Corollary 33.1.2.** The relations `K (u, x*) = ⟨Fu, x*⟩` and `Fu = K (u, ·)*`
express a **one-to-one correspondence** between the convex-closed concave-convex functions `K` on
`ℝᵐ × ℝⁿ` and the image-closed convex bifunctions `F` from `ℝᵐ` to `ℝⁿ`.

Specialises `bifunSaddleEquiv`. The book gives no proof; the two round trips are the two halves of
Theorem 33.1, `theorem_33_1_bracket_eq` in one direction and `theorem_33_1_inversion` in the
other. -/
noncomputable def corollary_33_1_2 :
    {F : Bifun (Rn m) (Rn n) // ConvexBifun F ∧ ImageClosedBifun F} ≃
      {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ ConvexClosedFn K} :=
  bifunSaddleEquiv (Bx := pairing n)

/-- The forward relation of Corollary 33.1.2 is `K (u, x*) = ⟨Fu, x*⟩`. -/
theorem corollary_33_1_2_apply
    (F : {F : Bifun (Rn m) (Rn n) // ConvexBifun F ∧ ImageClosedBifun F}) :
    (corollary_33_1_2 F).1 = bifunBracket F.1 := rfl

/-- The inverse relation of Corollary 33.1.2 is `Fu = K (u, ·)*`. -/
theorem corollary_33_1_2_symm_apply
    (K : {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ ConvexClosedFn K}) :
    (corollary_33_1_2.symm K).1 = bifunOfSaddleFn K.1 := rfl

end Cor3312

/-! ### Corollary 33.1.3 -/

section Cor3313

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Rockafellar, Corollary 33.1.3**, first clause: for a polyhedral convex bifunction `F`,
`⟨Fu, x*⟩` is a **polyhedral convex** function of `x*` for each `u`.

Specialises `polyhedralFn_bracket`: it is Theorem 19.2 applied to the slice `Fu`, which
Theorem 29.2 makes polyhedral. -/
theorem corollary_33_1_3_convex (hF : PolyhedralBifun F) (u : Rn m) :
    PolyhedralFn fun y => bifunBracket F (u, y) :=
  polyhedralFn_bracket hF (pairing n) u

/-- **Rockafellar, Corollary 33.1.3**, second clause: `⟨Fu, x*⟩` is a **polyhedral concave**
function of `u` for each `x*`, i.e. its negative is polyhedral convex.

Specialises `polyhedralFn_neg_bracket`: the proof of Theorem 33.1's concavity clause, with
Corollary 19.3.1 in place of Theorem 5.7. -/
theorem corollary_33_1_3_concave (hF : PolyhedralBifun F) (y : Rn n) :
    PolyhedralFn fun u => -(bifunBracket F (u, y)) :=
  polyhedralFn_neg_bracket hF (pairing n) y

/-- **Rockafellar, Corollary 33.1.3**, third clause: a **proper** polyhedral convex bifunction is
recovered from its bracket, `(Fu)(x) = sup_{x*} {⟨x, x*⟩ - ⟨Fu, x*⟩}` — with no closure operation,
because a proper polyhedral convex function is already closed.

Specialises `eq_iSup_sub_bracket_of_polyhedralBifun`. -/
theorem corollary_33_1_3_inversion (hF : PolyhedralBifun F) (hp : Proper (graphFn F)) (u : Rn m)
    (x : Rn n) :
    F u x = ⨆ y : Rn n, ((pairing n x y : ℝ) : EReal) - bifunBracket F (u, y) :=
  eq_iSup_sub_bracket_of_polyhedralBifun (pairing n) hF hp u x

end Cor3313

/-! ### The adjoint bracket

Rockafellar's running text at 14241: the adjoint `F*` of a convex bifunction is a *closed concave*
bifunction, so `⟨u, F*x*⟩` is concave-convex and concave-closed. This is the `K̄` half of every
pair from here to the end of Part VII. -/

section AdjointBracket

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Rockafellar, §33 (14241)**: `⟨u, F*x*⟩` is a concave-convex function of `(u, x*)`, with no
hypothesis on `F` — the adjoint of *any* bifunction is concave.

Specialises `concaveConvexFn_concaveBracket` at `concaveBifun_adjointBifun`. -/
theorem adjointBracket_concaveConvex (F : Bifun (Rn m) (Rn n)) :
    ConcaveConvexFn (adjointBracket F) :=
  concaveConvexFn_concaveBracket (concaveBifun_adjointBifun (pairing m) (pairing n) F) (pairing m)

/-- **Rockafellar, §33 (14241)**: `⟨u, F*x*⟩` is **concave-closed**.

It is a `cl₁` — that is Theorem 33.2's first equation — and every `cl₁` is concave-closed by
Corollary 33.1.1. -/
theorem adjointBracket_concaveClosed (hF : ConvexBifun F) :
    ConcaveClosedFn (adjointBracket F) := by
  have h : adjointBracket F = cl₁ (bifunBracket F) :=
    (partialCl₁_bracket (pairing m) (pairing n) hF).symm
  rw [h]
  exact corollary_33_1_1_cl₁_concaveClosed _

end AdjointBracket

/-! ### Theorem 33.2 -/

section Thm332

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Rockafellar, Theorem 33.2**, first equation: `⟨u, F*x*⟩ = cl₁ ⟨Fu, x*⟩`.

`cl₁` closes the **concave** — first — argument. Specialises `partialCl₁_bracket`, which is
concave Fenchel–Moreau in `u` applied to the concave function `⟨F·, x*⟩` of Theorem 33.1. -/
theorem theorem_33_2_first (hF : ConvexBifun F) : adjointBracket F = cl₁ (bifunBracket F) :=
  (partialCl₁_bracket (pairing m) (pairing n) hF).symm

/-- **Rockafellar, Theorem 33.2**, second equation: `cl₂ ⟨u, F*x*⟩ = ⟨(cl F)u, x*⟩`.

`cl₂` closes the **convex** — second — argument. Specialises
`partialCl₂_concaveBracket_adjointBifun`: the first equation applied to the concave bifunction
`F*`, composed with Theorem 30.1's `F** = cl F`. -/
theorem theorem_33_2_second (hF : ConvexBifun F) :
    cl₂ (adjointBracket F) = bifunBracket (clBifun F) := by
  funext p
  exact congrFun
    (partialCl₂_concaveBracket_adjointBifun (Bu := pairing m) (Bx := pairing n) hF p.1) p.2

end Thm332

/-! ### Corollary 33.2.1 -/

section Cor3321

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Rockafellar, Corollary 33.2.1**, first assertion: if `u ∈ ri (dom F)` then
`⟨Fu, x*⟩ = ⟨u, F*x*⟩` for **every** `x*`.

Specialises `bracket_eq_concaveBracket_adjointBifun_of_mem_relint`. Theorem 33.2 says the two
differ by `cl₁`, the effective domain of the concave function `⟨F·, x*⟩` is `dom F` for every `x*`
(`domConcave_bracket`), and a concave function agrees with its closure on the relative interior of
its effective domain (Theorem 7.4). -/
theorem corollary_33_2_1_primal (hF : ConvexBifun F) {u : Rn m} (hu : u ∈ ri (domBifun F))
    (y : Rn n) : bifunBracket F (u, y) = adjointBracket F (u, y) :=
  bracket_eq_concaveBracket_adjointBifun_of_mem_relint (pairing m) (pairing n) hF hu y

/-- **Rockafellar, Corollary 33.2.1**, second assertion: if `F` is **closed** and
`x* ∈ ri (dom F*)` then `⟨Fu, x*⟩ = ⟨u, F*x*⟩` for every `u`.

Rockafellar proves this by "applying the first fact to `F*`" (14293). The substitution is not
literally available — `F*` is a concave bifunction and the first assertion is about a convex one —
so the route taken is Theorem 33.2's *second* equation together with the **convex** form of
Theorem 7.4. That is also where the closedness hypothesis is spent, and it is spent nowhere else.

Specialises `bracket_eq_concaveBracket_adjointBifun_of_mem_relint_domConcaveBifun`, which lives in
`Bifunction/ProcessDuality.lean` rather than beside its primal half. -/
theorem corollary_33_2_1_dual (hF : ConvexBifun F) (hcl : ClosedBifun F) (u : Rn m) {y : Rn n}
    (hy : y ∈ ri (domConcaveBifun (dualProgram F))) :
    bifunBracket F (u, y) = adjointBracket F (u, y) :=
  bracket_eq_concaveBracket_adjointBifun_of_mem_relint_domConcaveBifun
    (Bu := pairing m) (Bx := pairing n) hF hcl u hy

end Cor3321

/-! ### Corollary 33.2.2 -/

section Cor3322

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Rockafellar, Corollary 33.2.2.** For a **proper polyhedral** convex bifunction `F`,
`⟨Fu, x*⟩ = ⟨u, F*x*⟩` holds **except** when both `u ∉ dom F` and `x* ∉ dom F*`.

Specialises `bracket_eq_concaveBracket_adjointBifun_of_polyhedral`. A polyhedral function agrees
with its closure on the whole of its effective domain, not merely on the relative interior, so
Corollary 33.2.1's `ri` can be dropped on each side separately; the two halves together leave only
the exceptional pairs uncovered. -/
theorem corollary_33_2_2 (hF : PolyhedralBifun F) (hp : Proper (graphFn F)) (u : Rn m) (y : Rn n)
    (h : u ∈ domBifun F ∨ y ∈ domConcaveBifun (dualProgram F)) :
    bifunBracket F (u, y) = adjointBracket F (u, y) :=
  bracket_eq_concaveBracket_adjointBifun_of_polyhedral (pairing m) (pairing n) hF hp u y h

/-- **Rockafellar, Corollary 33.2.2**, the parenthetical: in the exceptional case one of the two
quantities is `+∞` and the other `-∞`. Neither polyhedrality nor properness is used.

Specialises `bracket_eq_bot_and_concaveBracket_eq_top`. -/
theorem corollary_33_2_2_exceptional {u : Rn m} (hu : u ∉ domBifun F) {y : Rn n}
    (hy : y ∉ domConcaveBifun (dualProgram F)) :
    bifunBracket F (u, y) = ⊥ ∧ adjointBracket F (u, y) = ⊤ :=
  bracket_eq_bot_and_concaveBracket_eq_top (pairing m) (pairing n) hu hy

end Cor3322


/-! ### Full, lower and upper closedness (14371–14415) -/

section Closedness

variable {m n : ℕ} {K : Rn m × Rn n → EReal}

/-- **Rockafellar, §33 (14371)**: a saddle-function that is **finite everywhere** is fully closed —
"inasmuch as a finite convex or concave function is continuous and hence closed". This is
Corollary 10.1.1 applied slice by slice, on both sides.

The concave half is the convex half at `saddleSwap`, which is exactly what that involution is for:
`partialCl₂_saddleSwap` turns `cl₂` of the swap into `cl₁` of the original. -/
theorem convexClosedFn_of_finite (hK : ConcaveConvexFn K) (hbot : ∀ p, K p ≠ ⊥)
    (htop : ∀ p, K p ≠ ⊤) : ConvexClosedFn K := by
  refine convexClosedFn_iff.2 fun u => ?_
  refine (closedFn_iff_lowerSemicontinuous fun x => hbot (u, x)).2 ?_
  refine Continuous.lowerSemicontinuous
    (ConvexFn.continuous_of_dom_eq_univ (hK.convex_snd u) ⟨⟨0, ?_⟩, fun x => hbot (u, x)⟩ ?_)
  · exact lt_top_iff_ne_top.2 (htop (u, 0))
  · exact Set.eq_univ_of_forall fun x => lt_top_iff_ne_top.2 (htop (u, x))

/-- **Rockafellar, §33 (14371)**: a saddle-function finite everywhere is **fully closed**. -/
theorem fullyClosedFn_of_finite (hK : ConcaveConvexFn K) (hbot : ∀ p, K p ≠ ⊥)
    (htop : ∀ p, K p ≠ ⊤) : FullyClosedFn K := by
  refine ⟨convexClosedFn_of_finite hK hbot htop, ?_⟩
  have hswap : ConvexClosedFn (saddleSwap K) :=
    convexClosedFn_of_finite (concaveConvexFn_saddleSwap hK)
      (fun q => by simpa [saddleSwap] using htop (q.2, q.1))
      (fun q => by simpa [saddleSwap] using hbot (q.2, q.1))
  have h : saddleSwap (partialCl₁ K) = saddleSwap K := by
    rw [← partialCl₂_saddleSwap]
    exact hswap
  exact saddleSwap_injective h

/-- **Rockafellar, §33 (14415)**: a saddle-function is **fully closed** if and only if it is both
**lower closed** and **upper closed**.

Specialises `fullyClosedFn_iff`. Both directions are the idempotence of `cl₁` and `cl₂`
(Corollary 33.1.1): `lowerCl K = cl₂ (cl₁ K)` and `upperCl K = cl₁ (cl₂ K)`. -/
theorem fullyClosed_iff_lowerClosed_and_upperClosed (K : Rn m × Rn n → EReal) :
    FullyClosedFn K ↔ LowerClosedFn K ∧ UpperClosedFn K :=
  fullyClosedFn_iff

/-- **Rockafellar, §33 (14411)**, the convex-concave convention, spelled out.

For a *convex-concave* `K` the book's `cl₁` closes **convexly** in the first argument and its `cl₂`
closes **concavely** in the second, so both are the operators of this module conjugated by
negation: `book-cl₁ K = -(cl₁ (-K))` and `book-cl₂ K = -(cl₂ (-K))`. Composing them,
`book-cl₁ (book-cl₂ K) = -(upperCl (-K))`, so the book's "`K` is **lower closed**" for a
convex-concave `K` is `UpperClosedFn (-K)` — with `-K` concave-convex.

This is the single most common way to invert every statement of §§34–37. -/
theorem convexConcave_lowerClosed_iff (K : Rn m × Rn n → EReal) :
    (fun p => -(upperCl (fun q => -(K q)) p)) = K ↔ UpperClosedFn fun p => -(K p) := by
  constructor
  · intro h
    funext p
    rw [← congrFun h p, neg_neg]
  · intro h
    funext p
    rw [congrFun h p, neg_neg]

/-- **Rockafellar, §33 (14411)**, the other half of the convex-concave convention: the book's
"`K` is **upper closed**" for a convex-concave `K`, `book-cl₂ (book-cl₁ K) = K`, is
`LowerClosedFn (-K)`. -/
theorem convexConcave_upperClosed_iff (K : Rn m × Rn n → EReal) :
    (fun p => -(lowerCl (fun q => -(K q)) p)) = K ↔ LowerClosedFn fun p => -(K p) := by
  constructor
  · intro h
    funext p
    rw [← congrFun h p, neg_neg]
  · intro h
    funext p
    rw [congrFun h p, neg_neg]

end Closedness

/-! ### Theorem 33.3 -/

section Thm333

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Rockafellar, Theorem 33.3**, one direction: the bracket `⟨Fu, x*⟩` of a **closed** convex
bifunction is a **lower closed** concave-convex function.

Specialises `lowerClosedFn_bracket`: `cl₁` of the bracket is `⟨u, F*x*⟩` and `cl₂` of that is
`⟨(cl F)u, x*⟩ = ⟨Fu, x*⟩`, both by Theorem 33.2. -/
theorem theorem_33_3_lowerClosed (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    LowerClosedFn (bifunBracket F) :=
  lowerClosedFn_bracket (pairing m) (pairing n) hF hcl

/-- **Rockafellar, Theorem 33.3.** The relations `K (u, x*) = ⟨Fu, x*⟩` and `Fu = K (u, ·)*` define
a **one-to-one correspondence** between the lower closed concave-convex functions `K` on
`ℝᵐ × ℝⁿ` and the **closed** convex bifunctions `F` from `ℝᵐ` to `ℝⁿ`.

Specialises `exists_unique_convexBifun_bracket_eq`. Rockafellar reduces it to Corollary 33.1.2 by
the unproved step "for image-closed convex bifunctions `F`, `⟨(cl F)u, x*⟩ = ⟨Fu, x*⟩` is
equivalent to `cl F = F`"; that step is `eq_of_bracket_eq`. -/
theorem theorem_33_3 (hK : ConcaveConvexFn K) (hlc : LowerClosedFn K) :
    ∃! F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedBifun F ∧ bifunBracket F = K :=
  exists_unique_convexBifun_bracket_eq (pairing m) (pairing n) hK hlc

end Thm333

/-! ### Corollary 33.3.1 -/

section Cor3331

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {Klow Kup : Rn m × Rn n → EReal}

/-- **Rockafellar, Corollary 33.3.1.** For concave-convex `K̲` and `K̄` on `ℝᵐ × ℝⁿ`, a closed
convex bifunction `F` with `K̲ (u, x*) = ⟨Fu, x*⟩` and `K̄ (u, x*) = ⟨u, F*x*⟩` exists — and is then
unique — **if and only if** `cl₁ K̲ = K̄` and `cl₂ K̄ = K̲`.

Specialises `exists_unique_bifun_of_closure_pair`; this direction is the sufficiency. The necessity
is `corollary_33_3_1_necessity_first` and `corollary_33_3_1_necessity_second`, both instances of
Theorem 33.2. -/
theorem corollary_33_3_1 (hK : ConcaveConvexFn Klow) (h1 : cl₁ Klow = Kup) (h2 : cl₂ Kup = Klow) :
    ∃! F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedBifun F ∧
      bifunBracket F = Klow ∧ adjointBracket F = Kup :=
  exists_unique_bifun_of_closure_pair (pairing m) (pairing n) hK h1 h2

/-- **Rockafellar, Corollary 33.3.1**, necessity, first relation: `cl₁ ⟨Fu, x*⟩ = ⟨u, F*x*⟩`. This
is Theorem 33.2's first equation and needs no closedness. -/
theorem corollary_33_3_1_necessity_first (hF : ConvexBifun F) :
    cl₁ (bifunBracket F) = adjointBracket F :=
  partialCl₁_bracket (pairing m) (pairing n) hF

/-- **Rockafellar, Corollary 33.3.1**, necessity, second relation: `cl₂ ⟨u, F*x*⟩ = ⟨Fu, x*⟩` for a
**closed** `F`. This is Theorem 33.2's second equation with `cl F = F`. -/
theorem corollary_33_3_1_necessity_second (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    cl₂ (adjointBracket F) = bifunBracket F :=
  partialCl₂_concaveBracket_adjoint (pairing m) (pairing n) hF hcl

/-- **Rockafellar, Corollary 33.3.1**, consequence: the closure relations imply `K̲` is **lower
closed**. Immediate: `lowerCl K̲ = cl₂ (cl₁ K̲) = cl₂ K̄ = K̲`. -/
theorem corollary_33_3_1_lowerClosed (h1 : cl₁ Klow = Kup) (h2 : cl₂ Kup = Klow) :
    LowerClosedFn Klow := by
  have e1 : partialCl₁ Klow = Kup := h1
  have e2 : partialCl₂ Kup = Klow := h2
  rw [lowerClosedFn_iff, lowerCl_def, e1, e2]

/-- **Rockafellar, Corollary 33.3.1**, consequence: the closure relations imply `K̄` is **upper
closed**. Immediate: `upperCl K̄ = cl₁ (cl₂ K̄) = cl₁ K̲ = K̄`. -/
theorem corollary_33_3_1_upperClosed (h1 : cl₁ Klow = Kup) (h2 : cl₂ Kup = Klow) :
    UpperClosedFn Kup := by
  have e1 : partialCl₁ Klow = Kup := h1
  have e2 : partialCl₂ Kup = Klow := h2
  rw [upperClosedFn_iff, upperCl_def, e2, e1]

/-- **Rockafellar, Corollary 33.3.1**, consequence: `K̲ ≤ K̄`. Only the `cl₂` relation is used,
because `cl₂` lowers. Specialises `le_of_partialCl₂_eq`. -/
theorem corollary_33_3_1_le (h2 : cl₂ Kup = Klow) : Klow ≤ Kup :=
  le_of_partialCl₂_eq h2

end Cor3331

/-! ### Corollary 33.3.2 -/

section Cor3332

variable {m n : ℕ}

/-- **Rockafellar, Corollary 33.3.2.** The relations `K̄ = cl₁ K̲` and `K̲ = cl₂ K̄` define a
**one-to-one correspondence** between the lower closed and the upper closed concave-convex
functions on `ℝᵐ × ℝⁿ`.

Specialises `lowerUpperClosedEquiv`. Both round trips are the definitions of `LowerClosedFn` and
`UpperClosedFn`; the content is that each operator lands in the other class. -/
noncomputable def corollary_33_3_2 :
    {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ LowerClosedFn K} ≃
      {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ UpperClosedFn K} :=
  lowerUpperClosedEquiv (pairing m) (pairing n)

/-- The forward relation of Corollary 33.3.2 is `K̄ = cl₁ K̲`. -/
theorem corollary_33_3_2_apply
    (K : {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ LowerClosedFn K}) :
    (corollary_33_3_2 K).1 = cl₁ K.1 := rfl

/-- The inverse relation of Corollary 33.3.2 is `K̲ = cl₂ K̄`. -/
theorem corollary_33_3_2_symm_apply
    (K : {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ UpperClosedFn K}) :
    (corollary_33_3_2.symm K).1 = cl₂ K.1 := rfl

end Cor3332

/-! ### Corollary 33.3.3

The two simple extensions of a finite continuous concave-convex function on a nonempty closed
`C × D` are a closure pair, so Corollary 33.3.1 applies to them.

**A divergence from the book's hypothesis.** Rockafellar asks for `K` "finite continuous" on
`C × D`, meaning jointly continuous. What the argument uses — and what the statements below ask
for — is continuity of each slice on its own set, `hcontD` and `hcontC`, which joint continuity
implies. The hypothesis here is therefore weaker than the book's. -/

section Cor3333

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **The second effective domain of `⟨u, Gx*⟩` is `dom G`**, the mirror of `dom₁_bracket`
(`Saddle/Conjugate.lean`), which the backbone does not carry. See the module docstring's
backbone-friction note. -/
private theorem dom₂_concaveBifunBracket (G : Bifun (Rn n) (Rn m)) :
    dom₂ (concaveBifunBracket G) = domConcaveBifun G := by
  ext y
  constructor
  · intro hy
    have h : y ∈ dom fun w => concaveBracket (pairing m) G (0 : Rn m) w := hy 0
    rwa [dom_concaveBracket] at h
  · intro hy u
    have h : y ∈ dom fun w => concaveBracket (pairing m) G u w := by
      rw [dom_concaveBracket]; exact hy
    exact h

/-- **Rockafellar, Corollary 33.3.3**, first clause: the **lower simple extension** `K̲` of a
finite continuous concave-convex function on a nonempty closed `C × D` is **lower closed**.

Specialises `lowerClosedFn_lowerSimpleExt`: `cl₁ K̲ = K̄` and `cl₂ K̄ = K̲`. -/
theorem corollary_33_3_3_lowerClosed (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    LowerClosedFn (lowerSimpleExt C D K) :=
  lowerClosedFn_lowerSimpleExt hCcl hDcl hCne hDne hcontD hcontC

/-- **Rockafellar, Corollary 33.3.3**, second clause: the **upper simple extension** `K̄` is
**upper closed**. Specialises `upperClosedFn_upperSimpleExt`. -/
theorem corollary_33_3_3_upperClosed (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    UpperClosedFn (upperSimpleExt C D K) :=
  upperClosedFn_upperSimpleExt hCcl hDcl hCne hDne hcontD hcontC

/-- **Rockafellar, Corollary 33.3.3**, main clause: there is a **unique** closed convex bifunction
`F` from `ℝᵐ` to `ℝⁿ` whose two brackets are the lower and the upper simple extension of `K`.

Specialises `exists_unique_bifun_of_simpleExt`, which is Corollary 33.3.1 at the closure pair
`partialCl₁_lowerSimpleExt` / `partialCl₂_upperSimpleExt`. -/
theorem corollary_33_3_3 (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    ∃! F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedBifun F ∧
      bifunBracket F = lowerSimpleExt C D K ∧ adjointBracket F = upperSimpleExt C D K :=
  exists_unique_bifun_of_simpleExt (pairing m) (pairing n) hC hCcl hDcl hCne hconv hconc hDne
    hcontD hcontC

/-- The bifunction Corollary 33.3.3 produces is `K̲ (u, ·)*`, and its bracket is `K̲` again. -/
theorem corollary_33_3_3_bracket (hC : Convex ℝ C) (hDcl : IsClosed D)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) :
    bifunBracket (bifunOfSaddleFn (lowerSimpleExt C D K)) = lowerSimpleExt C D K :=
  (theorem_33_1_bracket_eq (concaveConvexFn_lowerSimpleExt hC hconv hconc)).trans
    (partialCl₂_lowerSimpleExt hDcl hcontD)

/-- The adjoint bracket of that bifunction is `K̄`. -/
theorem corollary_33_3_3_adjointBracket (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    adjointBracket (bifunOfSaddleFn (lowerSimpleExt C D K)) = upperSimpleExt C D K := by
  rw [theorem_33_2_first
      (theorem_33_1_convexBifun (concaveConvexFn_lowerSimpleExt hC hconv hconc)),
    corollary_33_3_3_bracket hC hDcl hconv hconc hcontD]
  exact partialCl₁_lowerSimpleExt hCcl hCne hcontC

/-- **Rockafellar, Corollary 33.3.3**: `dom F = C`. -/
theorem corollary_33_3_3_dom (hC : Convex ℝ C) (hDcl : IsClosed D) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) :
    domBifun (bifunOfSaddleFn (lowerSimpleExt C D K)) = C := by
  have h1 : dom₁ (bifunBracket (bifunOfSaddleFn (lowerSimpleExt C D K)))
      = domBifun (bifunOfSaddleFn (lowerSimpleExt C D K)) :=
    dom₁_bracket (pairing n) _
  rw [← h1, corollary_33_3_3_bracket hC hDcl hconv hconc hcontD, dom₁_lowerSimpleExt hDne]

/-- **Rockafellar, Corollary 33.3.3**: `dom F* = D`. -/
theorem corollary_33_3_3_domAdjoint (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    domConcaveBifun (dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K))) = D := by
  have h2 : dom₂ (adjointBracket (bifunOfSaddleFn (lowerSimpleExt C D K)))
      = domConcaveBifun (dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K))) :=
    dom₂_concaveBifunBracket _
  rw [← h2, corollary_33_3_3_adjointBracket hC hCcl hDcl hCne hconv hconc hcontD hcontC,
    dom₂_upperSimpleExt hCne]

/-- **Rockafellar, Corollary 33.3.3**, the explicit formula for `F` off `C`: `(Fu)(x) = +∞`. -/
theorem corollary_33_3_3_bifun_of_notMem {u : Rn m} (hu : u ∉ C) (x : Rn n) :
    bifunOfSaddleFn (lowerSimpleExt C D K) u x = ⊤ := by
  rw [bifunOfSaddleFn_apply]
  refine le_antisymm le_top (le_iSup_of_le 0 ?_)
  rw [lowerSimpleExt_of_notMem_left (p := (u, (0 : Rn n))) hu]
  simp

/-- **Rockafellar, Corollary 33.3.3**, the explicit formula for `F` on `C`:
`(Fu)(x) = sup {⟨x, x*⟩ - K (u, x*) | x* ∈ D}`. -/
theorem corollary_33_3_3_bifun_of_mem {u : Rn m} (hu : u ∈ C) (x : Rn n) :
    bifunOfSaddleFn (lowerSimpleExt C D K) u x
      = ⨆ y ∈ D, (((pairing n x y : ℝ) : EReal) - ((K (u, y) : ℝ) : EReal)) := by
  rw [bifunOfSaddleFn_apply]
  refine iSup_congr fun y => ?_
  by_cases hy : y ∈ D
  · rw [lowerSimpleExt_of_mem (p := (u, y)) hu hy, iSup_pos hy]
  · rw [lowerSimpleExt_of_notMem_right (p := (u, y)) hu hy, iSup_neg hy]
    simp

/-- **Rockafellar, Corollary 33.3.3**, the explicit formula for `F*` on `D`:
`(F*x*)(u*) = inf {⟨u, u*⟩ - K (u, x*) | u ∈ C}`. -/
theorem corollary_33_3_3_adjoint_of_mem (hC : Convex ℝ C) (hDcl : IsClosed D)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) {y : Rn n} (hy : y ∈ D) (v : Rn m) :
    dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K)) y v
      = ⨅ u ∈ C, (((pairing m u v : ℝ) : EReal) - ((K (u, y) : ℝ) : EReal)) := by
  have hbr := congrFun (corollary_33_3_3_bracket hC hDcl hconv hconc hcontD)
  have h : dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K)) y v
      = concaveConj (pairing m)
        (fun u => bracket (pairing n) (bifunOfSaddleFn (lowerSimpleExt C D K)) u y) v :=
    adjointBifun_eq_concaveConj_bracket (pairing m) (pairing n) _ y v
  rw [h, concaveConj_apply]
  refine iInf_congr fun u => ?_
  rw [show bracket (pairing n) (bifunOfSaddleFn (lowerSimpleExt C D K)) u y
      = lowerSimpleExt C D K (u, y) from hbr (u, y)]
  by_cases hu : u ∈ C
  · rw [lowerSimpleExt_of_mem (p := (u, y)) hu hy, iInf_pos hu]
  · rw [lowerSimpleExt_of_notMem_left (p := (u, y)) hu, iInf_neg hu]
    simp

/-- **Rockafellar, Corollary 33.3.3**, the explicit formula for `F*` off `D`:
`(F*x*)(u*) = -∞`. -/
theorem corollary_33_3_3_adjoint_of_notMem (hC : Convex ℝ C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) {y : Rn n} (hy : y ∉ D) (v : Rn m) :
    dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K)) y v = ⊥ := by
  have hbr := congrFun (corollary_33_3_3_bracket hC hDcl hconv hconc hcontD)
  have h : dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K)) y v
      = concaveConj (pairing m)
        (fun u => bracket (pairing n) (bifunOfSaddleFn (lowerSimpleExt C D K)) u y) v :=
    adjointBifun_eq_concaveConj_bracket (pairing m) (pairing n) _ y v
  obtain ⟨u, hu⟩ := hCne
  rw [h, concaveConj_apply]
  refine le_antisymm (iInf_le_of_le u ?_) bot_le
  rw [show bracket (pairing n) (bifunOfSaddleFn (lowerSimpleExt C D K)) u y
      = lowerSimpleExt C D K (u, y) from hbr (u, y),
    lowerSimpleExt_of_notMem_right (p := (u, y)) hu hy]
  simp

end Cor3333

end Rockafellar
