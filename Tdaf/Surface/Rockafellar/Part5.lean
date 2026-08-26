/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Surface.Rockafellar.Part5.Section23
import Tdaf.Surface.Rockafellar.Part5.Section24
import Tdaf.Surface.Rockafellar.Part5.Section25
import Tdaf.Surface.Rockafellar.Part5.Section26

/-!
# Rockafellar, Part V: Differential Theory

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §§23–26. This module imports the four
section modules and adds nothing of its own.

| § | module | subject |
|---|---|---|
| 23 | `Part5.Section23` | Directional Derivatives and Subgradients |
| 24 | `Part5.Section24` | Differential Continuity and Monotonicity |
| 25 | `Part5.Section25` | Differentiability of Convex Functions |
| 26 | `Part5.Section26` | The Legendre Transformation |

**All 49 of Part V's numbered results have declarations**, in 249 of them: 72 for §23, 48 for §24,
40 for §25, 89 for §26. Nothing here is deferred by scope and nothing is blocked.

## The two ambient spaces

Theorems 24.1–24.3 are stated over **`ℝ` itself**, not over `Rn 1`. That is the book's own reading:
`R` is the real line, and a one-sided derivative, a non-decreasing function and a subset of `R²`
are real-analytic objects rather than coordinate ones. §§6 and 15 made the same choice, and
`Subgradient/OneDim.lean` is written that way. Everything else in the Part is over `Rn n` with
`pairing n`.

## What this Part settles about the backbone

**A complete non-decreasing curve is a maximal chain.** The book gives two descriptions in
succession — a definition as `Γ(φ) = {(x, x*) | φ₋(x) ≤ x* ≤ φ₊(x)}` (line 9181) and a
characterisation as the maximal totally ordered subsets of `R²` under the coordinatewise ordering
(line 9195). `Part5.Section24` takes the second, as `IsMaxChain (· ≤ ·)` from Mathlib's order
library with the product order on `ℝ × ℝ`, per design decision **D12**: order-theoretic duality is
not re-invented here. The first is the backbone's `monotoneCurve`, and
`isCompleteNonDecreasingCurve_monotoneCurve` is the implication between them. Theorem 24.3 is
stated in the order-theoretic form and is unaffected by the missing converse.

**Maximal cyclic monotonicity does not give maximal monotonicity**, and the two are kept apart.
Rockafellar warns at line 9631 that Corollary 31.5.2 does *not* follow from Theorem 24.9 plus
"cyclically monotone implies monotone", because a mapping maximal in the smaller class need not be
maximal in the larger. `theorem_24_9` is therefore about maximal *cyclic* monotonicity only, and
`isMonotoneRel_subgradientRel_rn` about plain monotonicity, with no bridge. On the line the two
classes do coincide (`isMonotoneRel_iff_isCyclicallyMonotone_line`), which is why Theorem 24.3 can
speak of maximal chains at all; that coincidence is one-dimensional.

**§25 is less finite-dimensional than the plan supposed.** Three of its eleven results are general:
Theorem 25.1's forward half (the gradient is the unique subgradient, for a convex function on any
normed space), both halves of Corollary 25.1.1, and Theorem 25.4's density clause. What is
genuinely finite-dimensional is Theorem 25.1's *converse*, which runs through Corollary 11.6.1 and
is false in infinite dimensions, together with Theorem 25.4's continuity and measure-zero clauses.

## Where the book is defective

* **Theorem 26.5 says "closed convex function" where its own proof needs "closed *proper* convex".**
  Its first assertion is deduced from Corollary 26.3.1 and its Legendre-conjugate clause from
  Corollary 26.4.1, both stated for proper functions. `theorem_26_5` carries `Proper f`. Nothing is
  lost: an improper closed convex function is `+∞` everywhere or `−∞` on `cl (dom f)`, and in
  neither case is it differentiable on a non-empty interior, so both sides of the equivalence fail.
* **Theorem 26.4's hypotheses are stronger than its proof needs.** Single-valuedness of `g` and the
  formula `g = f*` on `D` follow from convexity alone, at each point where a gradient happens to
  exist; `theorem_26_4_wellDefined` and `theorem_26_4_eq` carry only `ConvexFn f`. The book's
  closedness and global differentiability are what make the domain `D` interesting, not what make
  the value well defined.
* **Corollary 26.3.3's "`A` maps `ℝⁿ` onto `ℝᵐ`" is used only through injectivity of `A*`** — the
  book's own proof says so, parenthetically.
* **Theorem 23.5 (a), (b) and (c) need neither convexity nor properness**, and **Theorem 24.4 needs
  neither convexity nor closedness**, only lower semicontinuity and properness: the backbone writes
  the graph of `∂f` as an intersection of preimages of `epi f` and never uses convexity. In each
  case the surface states the book's hypotheses and records the difference rather than weakening
  the statement.

## The counterexamples

Part V is unusually rich in them and all four are transcribed as Lean definitions rather than
paraphrased in prose.

* **p. 218, `dom ∂f` need not be convex** — `nonsmoothMaxFn`, with
  `notConvex_domSubgradient_nonsmoothMaxFn` proving the sentence the book uses it for and
  `proper_convexFn_nonsmoothMaxFn` checking that the counterexample is to the statement the book
  makes.
* **pp. 253–254, essential strict convexity is not strict convexity on `dom f`, and strict
  convexity on `ri (dom f)` is not essential strict convexity** — `essStrictlyConvexFn` and
  `strictOnRelintFn`, each with its decisive half proved.
* **p. 257, the Legendre domain need not be convex and `f` need not be essentially smooth** —
  `halfPlaneFn`, whose parabola `D` is computed in full on `ℝ²`
  (`not_convex_legendreDomain_halfPlaneFn`, `not_essentiallySmooth_halfPlaneFn`).

There is deliberately **no naive involution lemma** for the Legendre transformation. The book is
explicit on p. 258 that the Legendre conjugate of the Legendre conjugate need not be the original
function, and Theorem 26.5 is the statement of exactly when it is.
-/
