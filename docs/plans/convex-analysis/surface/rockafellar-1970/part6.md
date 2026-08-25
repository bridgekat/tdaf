# Part VI — Constrained Extremum Problems (§27–§32)

`Tdaf/Surface/Rockafellar/Part6.lean` → `Part6/Section27.lean` … `Section32.lean`.

**63 numbered results: 31 G, 31 C, 1 X**, plus **30 clause rows** — the highest clause density in
the book (Thm 27.1 has 9, Thm 30.4 has 10).

| § | module | results | G/C | thickness | backbone it specialises |
|---|---|---|---|---|---|
| 27 | `Section27.lean` | 9 (+9 clauses) | 1/8 | medium | `Optimization/Minimum.lean` |
| 28 | `Section28.lean` | 9 (+3 clauses) | 0/9 | **thickest file in the surface** | `Optimization/{Program,Lagrangian,Perturbation}.lean` |
| 29 | `Section29.lean` | 12 | 5/6/1X | medium | `Optimization/Perturbation.lean`, `Adjoint.lean` |
| 30 | `Section30.lean` | 10 (+16 clauses) | 9/1 | thin | `Optimization/{Adjoint,Normal}.lean` |
| 31 | `Section31.lean` | 12 (+6 clauses) | 10/2 | thin | `Optimization/{Fenchel,Moreau,Prox,ConeDuality}.lean` |
| 32 | `Section32.lean` | 11 | 6/5 | thin | `Optimization/Maximum.lean` |

## Gated on remediation

* **§27 needs Thm 27.1(e)** (remediation §4.6). The backbone excluded it as "unstatable without a
  reflexive pairing" because `∂f*(0)` lives in `E**` — but `ℝⁿ` *is* reflexive, so the surface
  demands it and cannot get it. Restate under `[IsCompatiblePairing B] [IsCompatiblePairing B.flip]`.
* **§29–§30 need the `negFst (prodPairing Bu Bx)` instances** (§4.2) — §30's adjoint bifunctions
  conjugate against `negFst`, and only the *pointwise* identity exists today. This is the likely
  `Setup.lean` blocker.
* **§29–§30 also need `Rn m × Rn n ≃ₗᵢ Rn (m+n)`** with transport for `conj`, `subgradient`, `ri`
  (§4.8): the book moves freely between the two.
* **§31** needs the bundled adjoint (§4.1) for Thm 31.2 and Cor 31.2.1.

## Receives from the backbone

Per remediation §6: `programLagrangian`, `IsKuhnTuckerVector`, `feasibleSet`, `optimalValue` move
here from `Optimization/Program.lean` (§28). They duplicate `lagrangian` and `KuhnTucker` and their
own docstrings say so — which is exactly the README's recipe for a surface definition. Keep the
*theorem* `exists_isKuhnTuckerVector_of_slater` in the backbone, restated against `lagrangian`.

## §28 is the most important surface file

It is where the abstract perturbation theory becomes recognisable Lagrange multipliers. Two things
must be got right:

1. **The program is the tuple, not the objective.** Rockafellar is emphatic (10761, 10797): two
   programs with the same objective can have different Lagrangians and different Kuhn–Tucker
   vectors. Carry `(C, f₀, …, f_m, r)` as the primitive, and the program ↔ Lagrangian correspondence
   (11047–11057) as a theorem.
2. **Build `ineqBifun`** and derive Thms 28.1–28.4 from §29–§30, with a lemma tying its `lagrangian`
   to the surface `programLagrangian`.

Two unnumbered counterexamples justify the constraint qualification and must be kept: 10989
(`f₁ = ξ₂`, `f₂ = ξ₁² − ξ₂` — a unique optimal solution with no Kuhn–Tucker vector) and 11007
(linear constraints only, but no feasible point in `ri C`).

## The book is defective here

* **Corollary 29.4.1 (12151) has no proof at all, and drops the properness hypothesis** its own
  Theorem 29.4 carries. Its clause that the perturbation functions of `(P)` and `(cl P)` agree on a
  neighbourhood of `0` is **false** without it: take `F u x = −∞` for `u` on a line `L ⊆ ℝ²` through
  the origin and `+∞` off it. State it with `F` proper. Found independently from the text and from
  the Lean side.
* **Theorem 29.4's printed proof is wrong at 12139**: it claims `((cl F)u)(y) = −∞` for *all* `y` in
  the improper case, but `cl f` is `+∞` outside `cl (dom f)`. The theorem survives; the printed
  justification does not.
* **Corollary 31.2.1's polyhedral strengthening (13379) is asserted with the proof explicitly
  omitted.**
* **Stated with no printed proof**: Cors 27.2.1, 28.2.2, 28.3.1, 28.4.1, 31.5.1.

## Other notes

* **Thm 27.1 is a nine-clause omnibus** whose proof (10449) is a one-line pointer list to §§8, 13,
  14, 23, 25. The clauses sit at three different backbone layers — split them.
* **Thm 30.4 is a ten-clause disjunction** of sufficient conditions whose printed proof covers only
  (a), (c), (e) and dualises.
* Two load-bearing unnumbered counterexamples in §30: 12671 (an *abnormal* closed proper program
  with a genuine duality gap — `(Fu)(x) = exp(−√(ux))` on the first quadrant, `inf F0 = 1` but
  `sup F*0 = 0`) and 12715 (a normal program with an optimal solution whose dual has none).
* Line 12667 names Thm 30.4(e)/(f) applied to linear programs the **Gale–Kuhn–Tucker Duality
  Theorem** with no separate numbered statement.
* The contraction property of `prox` (13851–13885) is unnumbered running text and is what makes
  Cor 31.5.2 work — it should be a named lemma. The backbone has it in `Optimization/Prox.lean`.
* §32's two examples at 14017–14043 show `C ⊆ ri(dom f)` in Cor 32.3.2 cannot be weakened to
  `C ⊆ dom f` even for closed `f`. Keep both. Cor 32.3.4 is the theoretical basis of the simplex
  method (a remark at 14013).
* **Cor 32.3.3 diverges from the book deliberately**: the backbone quotients the lineality space by
  an *arbitrary* complement rather than `L⊥`, so it needs no inner product. Strictly stronger; note
  it in the docstring so a reader checking alignment is not misled.
* Mixed-case labels: `Corollary 27.2.2`, `28.3.1`, `29.1.5`, `31.5.1`.
* Unnumbered example deposits: 11309–11596 (the decomposition principle), 12731–13136 (duals of
  ordinary convex programs), 13381–13465 (linear programming), 13691–13733 (Problems I and II).
