# Part VII — Saddle-functions and Minimax Theory (§33–§37)

`Tdaf/Surface/Rockafellar/Part7.lean` → `Part7/Section33.lean` … `Section37.lean`.

**58 numbered results: 24 G, 34 C**, plus 12 clause rows (Thm 34.3 has 6, Thm 37.5 has 4,
Thm 37.3 has 2).

| § | module | results | G/C | backbone it specialises |
|---|---|---|---|---|
| 33 | `Section33.lean` | 11 | 8/3 | `Saddle/{Defs,Correspondence,Kernel}.lean` |
| 34 | `Section34.lean` | 10 (+6) | 4/6 | `Saddle/{Closure,Equiv,Kernel}.lean` |
| 35 | `Section35.lean` | 12 | 1/11 | `Saddle/{Continuity,Differential,Rademacher}.lean` |
| 36 | `Section36.lean` | 7 | 4/3 | `Saddle/Minimax.lean` |
| 37 | `Section37.lean` | 18 (+6) | 7/11 | `Saddle/{Conjugate,Subgradient,Existence,Monotone}.lean` |

## Orientation is the whole difficulty of this Part

Three separate conventions, each load-bearing, each capable of silently inverting every statement
downstream:

1. **`cl₁` closes the *concave* argument, `cl₂` the convex one** (§33, mnemonic at 14409). Reverse
   it and every result in §§34–37 swaps.
2. **Minimise in the convex argument, maximise in the concave** (§36, declared at 15449, in force
   for the rest of the book). Theorems 36.3–36.6 and *all* of §37 are false verbatim under the
   opposite convention. This is *why* `∂K` mixes a concave subdifferential in the first argument
   with a convex one in the second (§35, 15155), hence why **Cor 37.5.2 must insert `u* ↦ −u*`** to
   obtain monotonicity and why **Cor 37.5.1's homeomorphism is the asymmetric `(u−u*, v+v*)`**
   rather than a symmetric sum. **Track the sign explicitly; do not try to derive it.**
3. The lower conjugate uses `sup_v inf_u` and the upper `inf_u sup_v` (15763, 15769), with
   `K̲* ≤ K̄*` by Lemma 36.1. Swapping the extrema swaps the two conjugates.

This is the single most common source of error in porting Part VII.

## Gated on [remediation](../../backbone/08-remediation.md)

* **§2.1 — `saddleSwap` over `Kernel.lean`'s SimpleExt block.** §33 specialises exactly those
  declarations, and the surface needs the lower and the upper simple extension side by side. Doing
  the transport first turns 184 backbone lines into 61 with no change of hypotheses, and — more
  importantly — leaves the surface *one* orientation-flipping lemma to cite rather than two parallel
  developments to keep aligned. Do this before `Section33.lean`.
* **§4.1 bundled adjoint** — §37's `⟨u*, F_*x⟩` and Thm 37.5's inverse correspondence read badly with
  `A*` as a loose argument plus an `IsAdjointPair` hypothesis.
* **§5.6 `SimpleSaddleFn` rename** — the word "simple" is Rockafellar's; it belongs in a surface
  docstring, not in a backbone identifier.

## Design consequences

* **The natural primitive is not a saddle-function.** It is the pair (lower closed `K̲`, upper
  closed `K̄`) — equivalently a closed convex bifunction. Theorem 34.2 is what licenses this, and
  should be stated first in `Section34.lean`.
* **Conjugacy depends only on the equivalence class** (Cor 37.1.1), so the surface should conjugate
  classes or bifunctions, never raw saddle-functions.
* **Thm 36.5 is the structural pay-off of the Part**: Lagrangians of convex programs are exactly the
  upper closed concave-convex functions, so "regularized minimax problem" and "dual pair of convex
  programs" are the same object. With Cor 34.2.2 (a unique upper closed member per class) it fixes
  the canonical representative.
* **Thm 35.6's splitting identity** — `K′(u,v;u′,v′) = K′(u,v;u′,0) + K′(u,v;0,v′)` — is the only
  fully general result in §35 and the pivot on which `∂K = ∂₁K × ∂₂K` rests. Get it in first.
* The `⟨·,·⟩` notation is overloaded three ways in §33 and a fourth in §38. Use distinct names; do
  not reproduce the overloading.

## Notes

* §34 is the technical heart and the hardest to formalize faithfully: the apparatus (equivalence
  class ↔ closed convex bifunction ↔ kernel on `ri (dom K)`) is intrinsically finite-dimensional.
* Line 14909 leaves as an exercise that every saddle-function of the form `⟨Fu, x*⟩` is simple;
  line 14915 asserts without proof that every saddle-function with `int (dom K) ≠ ∅` is simple.
* Cor 34.2.4's `+∞`/`−∞` pattern (14826) is orientation-sensitive and is the exact opposite of the
  pattern for convex-concave functions.
* Cors 37.3.2 and 37.6.2 are Rockafellar's finite-dimensional minimax theorems. Their
  infinite-dimensional analogues (Kneser–Fan, Sion) require **compactness** as a hypothesis, not
  boundedness — flag the substitution in the docstring. The backbone proves Cor 37.6.2 from
  Rockafellar's own unbounded machinery rather than from Mathlib's `Topology/Sion.lean`, because the
  unbounded theorems it specialises are wanted anyway.

## Stated with no printed proof

Cors 33.1.2, 34.2.1, 34.2.3, 37.1.3, and **Theorem 36.6** (the section ends immediately after the
statement). Thm 34.2's proof begins 34 lines after its statement.
