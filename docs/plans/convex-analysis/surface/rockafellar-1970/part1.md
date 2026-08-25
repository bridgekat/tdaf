# Part I — Basic Concepts (§1–§5)

`Tdaf/Surface/Rockafellar/Part1.lean` → `Part1/Section01.lean` … `Section05.lean`.

**49 numbered results: 42 G, 7 C.** Mostly the thinnest material in the book, with one thick file.

| § | module | results | G/C | thickness | backbone it specialises |
|---|---|---|---|---|---|
| 1 | `Section01.lean` | 8 | 3/5 | **thick** | mostly Mathlib (`AffineSubspace`, `affineSpan`, `AffineMap`, `AffineIndependent`, `Submodule.orthogonal`) |
| 2 | `Section02.lean` | 13 | 13/0 | thin | Mathlib `Convex`, `convexHull`, `PointedCone`; `Duality/Polar.lean` |
| 3 | `Section03.lean` | 9 | 9/0 | thin | **Mathlib** — not `Operations/*`; see the correction below |
| 4 | `Section04.lean` | 11 | 9/2 | medium | `Epigraph.lean`, `Indicator.lean`, `Homogeneous.lean` |
| 5 | `Section05.lean` | 8 | 8/0 | thin | `Operations/{InfConv,Image,Hull}.lean`, `Homogenize.lean` |

## New work, not specialisation

* **§1 Tucker representations** (book 553–581) — described only procedurally: choose `n` independent
  variables and solve for the other `m`. Used in §22 and Cor 31.4.2. Pure coordinate bookkeeping,
  so it belongs here rather than in the backbone. Also **barycentric coordinates** as a named
  construction.
* **§4 Thms 4.4 and 4.5** — the second-derivative and Hessian criteria. Mathlib has the
  one-dimensional case in `Analysis/Convex/Deriv.lean`; the `ℝⁿ` case follows by restricting to
  lines. That reduction is now in the backbone at `Tdaf/Analysis/Convex/Line.lean`
  (`convexOn_iff_lines`, `concaveOn_iff_lines`), so remediation §4.9 is closed.
* **§4–§5 examples.** The conjugate pairs and concrete convex functions (`eˣ`, `|x|ᵖ/p`, `−log`,
  `−(a²−x²)^{1/2}`, the geometric mean, log-sum-exp, the Tchebycheff norm). Genuine value: they are
  the tests that the definitions compute. Mathlib supplies the analysis (`norm_inner_le_norm`,
  `Analysis/MeanInequalities.lean`). **All unnumbered — harvest by line range**, book 1211–1290.

## Hazards

* `cone S` is *defined* to contain the origin (745) but Cors 2.6.2/2.6.3's cone need not. This
  off-by-one propagates through §§8, 9, 14, 19.
* `dim f := dim (dom f)` (1055), not `dim (epi f)`; later text uses `dim (epi f) = dim f + 1`.
* Properness is **not** preserved by `□` (1535, explicit); later results silently re-impose it.
* `f0` is defined by cases (1558–1561), and that discontinuity recurs in §§8, 9, 13, 15, 19.
* ~~Thm 5.8 rests on the informally described eight partial additions of §3.~~ **It does not.**
  The book's literal m-ary form `inf {f₁x₁ + ⋯ + fₘxₘ | ∑ xᵢ = x}` *is* the image
  `mapLin sumLin (∑ᵢ fᵢ ∘ projᵢ)`, so Theorem 5.7 closes Theorem 5.4 and all four clauses of
  Theorem 5.8 directly. §5 has **no dependency on §3**.
* Mixed-case labels here: `Theorem 3.4`, `3.6`, **`5.4`** (the `□` definition site), `Corollary 2.5.1`.

## Corrections found while building Part I

* **`Operations/*` is entirely function-level, so §3 does not specialise it.** §3 is set algebra and
  all nine of its results specialise Mathlib. The set-level inverse sum `#` has no backbone
  counterpart at all — `Operations/InfConv.lean`'s set-level shadow is ordinary `+` — so `invSum`
  is a genuine surface definition (remediation §8.7).
* **Partial addition was formalized after all**, as `partialAdd` over a general `Y × Z`, with the
  book's two extreme cases exact (`[Subsingleton Y] → (+)`, `[Subsingleton Z] → (∩)`). It is in
  §3 because §3 is where the book puts it, not because §5 needs it.
* **Theorem 3.8's `K₁ # K₂ = K₁ ∩ K₂` does not need convexity**; and the book's coefficient
  `(α₁⁻¹ + α₂⁻¹)⁻¹` for the inverse sum of vectors is wrong under Lean's `0⁻¹ = 0`. Both are
  recorded in [remediation §8](../../backbone/08-remediation.md#8-gaps-reported-by-the-part-i-surface-round).
