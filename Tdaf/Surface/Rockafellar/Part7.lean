/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Surface.Rockafellar.Part7.Section33
import Tdaf.Surface.Rockafellar.Part7.Section34
import Tdaf.Surface.Rockafellar.Part7.Section35
import Tdaf.Surface.Rockafellar.Part7.Section36
import Tdaf.Surface.Rockafellar.Part7.Section37

/-!
# Rockafellar, Part VII: Saddle-Functions and Minimax Theory

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §§33–37. This module imports the five
section modules and adds nothing of its own.

| § | module | subject | declarations |
|---|---|---|---|
| 33 | `Part7.Section33` | Saddle-Functions | 66 |
| 34 | `Part7.Section34` | Closures and Equivalence Classes | 81 |
| 35 | `Part7.Section35` | Continuity and Differentiability of Saddle-Functions | 38 |
| 36 | `Part7.Section36` | Minimax Problems | 34 |
| 37 | `Part7.Section37` | Conjugate Saddle-Functions and Minimax Theorems | 86 |

**All 58 of Part VII's numbered results have declarations**, in 305 of them, together with all 12
of the Part's clause rows — the six of Theorem 34.3, the two of Theorem 37.3 and the four of
Theorem 37.5. Nothing is deferred by scope and nothing was blocked. Exactly one *half* of one
result is absent: the `C*` support-function formula of Theorem 37.2, whose `D*` half landed as
`theorem_37_2_dom₂`. It is recorded in `Section37.lean`'s `## What is not here` with the backbone
declaration it wants, `supportFn_dom₁_lowerConjSaddle` in `Saddle/Existence.lean`.

## Orientation is the whole difficulty of this Part

Three separate conventions, each load-bearing, each able to invert every statement downstream
silently. The plan for this Part named getting them wrong as the single most common source of
error in porting §§33–37, so each is stated *once*, where the book introduces it, and cited
thereafter rather than re-derived.

1. **`cl₁` closes the concave argument, `cl₂` the convex one** (§33, mnemonic at 14409). The table
   is in `Section33.lean`'s docstring, above any Lean.
2. **Minimise in the convex argument, maximise in the concave** (§36, declared at 15449 and in
   force for the rest of the book). The table is in `Section36.lean`'s docstring. Theorems 36.3–36.6
   and *all* of §37 are false verbatim under the opposite convention.
3. **The lower conjugate is `sup_v inf_u` and the upper `inf_u sup_v`** (15763, 15769), with
   `K̲* ≤ K̄*` by Lemma 36.1. Swapping the extrema swaps the two conjugates.

The sign that convention 2 forces is written down once, in §35, as
`mem_subgrad₁_iff_neg_mem_subgradient_neg`: `∂₁K` is a *concave* subdifferential and `∂₂K` a convex
one, so `∂K` is not the subdifferential of `K` read on `ℝᵐ⁺ⁿ`. That single `u* ↦ −u*` is what
Corollary 37.5.2 inserts to recover monotonicity, and §37 quotes it rather than re-deriving it.

One warning that the plan got backwards and the sections did not: **`saddleSwap` preserves the
concave-convex class rather than flipping it.** The translation for Rockafellar's convex-concave
convention is plain negation — the book's "lower closed" for convex-concave `K` is
`UpperClosedFn (-K)` — which is `convexConcave_lowerClosed_iff`. A surface-level swap would have
produced the mirrored `C*` statement in §37 without any error being reported.

## What this Part settles about the backbone

**The natural primitive is not a saddle-function.** It is the pair (lower closed `K̲`, upper closed
`K̄`) — equivalently a closed convex bifunction. Theorem 34.2 is what licenses this, so it opens
`Section34.lean` and Theorem 34.1 follows it rather than the other way round. `Rockafellar.Ω` is
that section's export, and the concave-convexity in it is **part of Rockafellar's definition and
cannot be dropped**: "`Ω (F)` is an equivalence class" is false for the bare order interval.

**Theorem 36.5 is the structural pay-off.** Lagrangians of convex programs are exactly the upper
closed concave-convex functions, so "regularized minimax problem" and "dual pair of convex
programs" are the same object; with Corollary 34.2.2's unique upper closed member per class, that
fixes the canonical representative.

**§31 is the source of Corollaries 37.5.1 and 37.5.2, not their consumer** — they come by
instantiating Corollaries 31.5.1 and 31.5.2 at `prodPairing (innerₗ U) (innerₗ X)`, which is what
generalizing `Optimization/Prox.lean` over a self-pairing bought.

**Three of the five sections asked for the same missing thing**: a bundled closed-proper-saddle-
function hypothesis. In `Section37.lean` four plumbing expressions account for 45 argument
occurrences. This is the Part's clearest signal about backbone shape, and it is recorded in the
remediation ledger rather than worked around here.

## Where the book is defective

* **Theorem 34.2's `dom K = dom F × dom F*` is a product identity only.** The printed proof argues
  the factors separately — "`u ∉ dom₁ K` iff `Fu ≡ +∞`" — and that step is **false for improper
  `F`**: with graph `≡ +∞`, `dom₁ K = ∅ = dom F` but `dom₂ K = ℝⁿ` while `dom F* = ∅`. Both
  products are empty, so the identity itself survives and only the factorwise reading fails.
  `theorem_34_2_dom₁` and `theorem_34_2_dom₂` carry the nonemptiness the book suppresses.
* **Theorem 34.1 needs no hypotheses at all** by the duality-free route (`lowerCl_idem`), which is
  strictly stronger than the book states it and puts the result at layer B rather than layer C.
* **Theorem 37.4's first sentence needs no hypothesis either** — not concave-convexity, not
  properness, not closedness; both sides are the same pair of inequalities with a real number moved
  across. The book states the whole theorem for a concave-convex `K`. The same holds of
  `theorem_37_5_c`, `theorem_37_5_d`, `lowerConj_le_upperConj`, `minimax_eq_neg_lowerConj_zero`
  and `maximin_eq_neg_upperConj_zero`.
* **Corollary 37.1.3 and Theorem 36.6 are printed with no proof**, and §36 ends at 36.6's
  statement. Corollary 37.1.3 is closed from the argument its own two displays sketch at
  15839–15841.
* **Corollaries 37.3.2 and 37.6.2 substitute boundedness for compactness.** Rockafellar asks that
  `C` (or `D`) be closed and bounded; the infinite-dimensional analogues — Kneser–Fan and Sion —
  need compactness, strictly stronger outside `ℝⁿ`. In `ℝⁿ` the two coincide by Heine–Borel and the
  substitution is invisible, which is why it must be written down. Corollary 37.6.2 is proved from
  Rockafellar's *own* unbounded machinery rather than from Mathlib's `Topology/Sion.lean`, because
  Theorem 37.6 and Corollary 37.6.1 are wanted in their own right.
* **Corollary 37.3.2's extrema are in `EReal`, not `ℝ`.** With only one of `C`, `D` bounded both
  iterated extrema can be infinite — `C = {0}`, `D = ℝ`, `K (u, v) = v` gives `sup inf = −∞` — so
  the book's implicit finiteness is unavailable. Corollary 37.6.2, with both bounded, keeps the
  book's real inequalities.
* **Corollary 37.5.1's homeomorphism has its second component's summands transposed**: the backbone
  produces `(u − u*, v* + v)` where the book prints `(u − u*, v + v*)`. Either way it is the
  asymmetric map, not a symmetric sum.
* **Corollaries 33.3.3, 34.2.4, 37.3.2 and 37.6.2 all weaken "continuous finite concave-convex on
  `C × D`"** from joint to *separate* convexity, concavity and continuity of each one-variable
  section on its own set — which is what `exists_bifunSaddleClass_lowerSimpleExt` actually
  consumes, and less than the book asks for.
* Two claims in §34's running text are unnumbered and uneven: 14909 leaves as an exercise that
  every saddle-function `⟨Fu, x*⟩` is simple — stated here as `simpleSaddleFn_bifunBracket`, but
  needing `ClosedBifun F` and properness that the book does not ask for — and 14915 asserts without
  proof that `int (dom K) ≠ ∅` implies simple, which is omitted, needing a §7/§10-style segment
  argument absent from `Saddle/`.

## The one gap that changed a proof

**`SaddleEquiv.saddleTilt` — `cl (f − ℓ) = cl f − ℓ` — is missing from the backbone entirely.**
Without it, Corollary 37.4.1 cannot be proved by Rockafellar's route and is proved from Theorem
37.5 instead, which costs a closedness hypothesis the book does not state; it is also why Theorem
37.5 (b) and Corollary 37.5.3 are stated for the canonical `upperConj K` rather than for an
arbitrary conjugate. Every such divergence is recorded in the affected docstring.
-/
