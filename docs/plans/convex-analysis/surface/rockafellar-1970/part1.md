# Part I — Basic Concepts (§1–§5)

`Tdaf/Surface/Rockafellar/Part1.lean` → `Part1/Section01.lean` … `Section05.lean`.

**49 numbered results: 42 G, 7 C.** Mostly the thinnest material in the book, with one thick file.

| § | module | results | G/C | thickness | backbone it specialises |
|---|---|---|---|---|---|
| 1 | `Section01.lean` | 8 | 3/5 | **thick** | mostly Mathlib (`AffineSubspace`, `affineSpan`, `AffineMap`, `AffineIndependent`, `Submodule.orthogonal`) |
| 2 | `Section02.lean` | 13 | 13/0 | thin | Mathlib `Convex`, `convexHull`, `PointedCone`; `Duality/Polar.lean` |
| 3 | `Section03.lean` | 9 | 9/0 | thin | `Operations/*` |
| 4 | `Section04.lean` | 11 | 9/2 | medium | `Epigraph.lean`, `Indicator.lean`, `Homogeneous.lean` |
| 5 | `Section05.lean` | 8 | 8/0 | thin | `Operations/{InfConv,Image,Hull}.lean`, `Homogenize.lean` |

## New work, not specialisation

* **§1 Tucker representations** (book 553–581) — described only procedurally: choose `n` independent
  variables and solve for the other `m`. Used in §22 and Cor 31.4.2. Pure coordinate bookkeeping,
  so it belongs here rather than in the backbone. Also **barycentric coordinates** as a named
  construction.
* **§4 Thms 4.4 and 4.5** — the second-derivative and Hessian criteria. Mathlib has the
  one-dimensional case in `Analysis/Convex/Deriv.lean`; the `ℝⁿ` case follows by restricting to
  lines, which needs `convexOn_iff_convexOn_lines` (remediation §4.9 — the *concave* half already
  exists, buried at `Saddle/Differential.lean:162`).
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
* Thm 5.8 rests on the informally described eight partial additions of §3; formalizing it means
  first formalizing that construction. Consider stating 5.8 only for the four operations the book
  actually singles out, with a docstring saying so.
* Mixed-case labels here: `Theorem 3.4`, `3.6`, **`5.4`** (the `□` definition site), `Corollary 2.5.1`.
