# Part VI — Constrained Extremum Problems (§27–§32)

`Tdaf/Surface/Rockafellar/Part6.lean` → `Part6/Section27.lean` … `Section32.lean`.

**63 numbered results: 31 G, 31 C, 1 X**, plus **30 clause rows** — the highest clause density in
the book (Thm 27.1 has 9, Thm 30.4 has 10).

| § | module | results | G/C | thickness | backbone it specialises |
|---|---|---|---|---|---|
| 27 | `Section27.lean` | 9 (+9 clauses) | 1/8 | medium | `Optimization/Minimum.lean` |
| 28 | `Section28.lean` | 9 (+3 clauses) | **5/4** | **thickest file in the surface** — 2432 lines, twice the next | `Optimization/{Program,Lagrangian}.lean`, **`Saddle/Minimax.lean`** |
| 29 | `Section29.lean` | 12 | 5/6/1X | **thin** | `Optimization/{Perturbation,Adjoint}.lean`, `Saddle/Minimax.lean`, `Subgradient/Uniqueness.lean`, `Bifunction/{Process,LinearProcess}.lean` |
| 30 | `Section30.lean` | 10 (+16 clauses) | **7/3** | thin | `Optimization/{Adjoint,Normal}.lean`, `Saddle/{Minimax,Correspondence}.lean` |
| 31 | `Section31.lean` | 12 (+6 clauses) | **7/2/3 mixed** | **thickest of the Part after §28** | `Optimization/{Fenchel,Moreau,Prox,ConeDuality,Normal}.lean` |
| 32 | `Section32.lean` | 11 | **4/7** | thin | `Optimization/Maximum.lean` |

## Gated on remediation

* ~~**§27 needs Thm 27.1(e)** (remediation §4.6).~~ **Never a gate, and the diagnosis was wrong.**
  `∂f*(0)` does not live in `E**`: for `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, `subgradient B.flip (conj B f) 0` is
  a subset of `E`, and clause (b) — `argmin f = ∂f*(0)` — had been stated in `Minimum.lean` since
  the file was written. The prescribed restatement was a no-op, since both classes were already on
  the section. The clause needed `Function.Injective B`, which is free in a normed space. On the
  surface it is two lines through `theorem_25_1`. **Part VI has no open gate.**
* ~~**§29–§30 need the `negFst (prodPairing Bu Bx)` instances** (§4.2)~~ — **neither section needs
  them, and the premise was wrong.** The claim was that "§30's adjoint bifunctions conjugate against
  `negFst`". They do not: the backbone reads Rockafellar's sign flip on the **argument**, not on the
  pairing. `⟨u, -v⟩ + ⟨x, y⟩` is the plain `prodPairing` of `(u, x)` with `(-v, y)`, the reflection
  is the linear map `adjointSwap`, and `conj` keeps all its own lemmas verbatim.
  `Optimization/Adjoint.lean`'s own docstring says exactly this, and the word `negFst` occurs in
  that file only in that sentence. Neither `Section29.lean` nor `Section30.lean` contains a
  `negFst`, a `pairingAdjoint`, or any sign-flipped pairing. §4.2 was built and is fine; it was
  never this Part's blocker.
* ~~**§29–§30 also need `Rn m × Rn n ≃ₗᵢ Rn (m+n)`** (§4.8)~~ — **closed, and likewise §30 only.**
  `Section29.lean` contains no `euclideanProdEquiv` and no `Rn (m + n)`. The transport is
  `Analysis/Convex/EuclideanProd.lean`; note the usable object is `euclideanProdEquiv` on the
  *plain* product, since the isometry the item originally asked for cannot exist (Mathlib's product
  norm is the sup norm).
* ~~**§31** needs the bundled adjoint (§4.1) for Thm 31.2 and Cor 31.2.1.~~ **Not a gate.** §4.1
  closed by measurement: the surface writes `A*` as `LinearMap.adjoint A` and carries no adjoint
  hypothesis, because `isAdjointPair_adjoint` already exists for `innerₗ E`. D3 stands unmodified.

**Every gate listed for this Part is closed, and three of the four were never gates at all.**
§4.2 and §4.8 were built but unused; §4.1 was closed by measurement; §4.6 was closed by trying the
clause. Only the *last* of those cost any Lean work, and it cost five new declarations.

## Receives from the backbone

**Naming hazard, recorded by §28 before anyone does this.** The backbone's `programLagrangian` is
**not** the Lagrangian: it is Rockafellar's `h = f₀ + Σ λᵢfᵢ`, which the surface calls `lagrangeFn`.
The surface's `programLagrangian` is the actual `L` on `ℝᵐ × ℝⁿ`. Deleting by name alone will
mismatch the two.

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
2. **Build `ineqBifun`** and tie its `lagrangian` to the surface `programLagrangian` — done, as
   `lagrangian_ineqBifun`, the book's line 11041 formula proved in full including the `-∞` case
   where `u* ∉ E_r`. **But "derive Thms 28.1–28.4 from §29–§30" is achievable only for 28.2.** The
   backbone's route to 28.3 is `isSaddlePoint_lagrangian_iff_mem_kuhnTucker`, which needs
   `ConvexBifun F` **and `ClosedBifun F`** — and an ordinary convex program's bifunction is *not*
   closed under Rockafellar's blanket assumptions, since he never assumes the `fᵢ` closed. That is
   exactly why Corollary 28.1.1 has to *add* closedness as a hypothesis. Deriving 28.3 from §29
   would have meant silently strengthening the book's theorem, so 28.1, 28.3 and 28.4 follow the
   book directly and the bridge is used only for what it genuinely buys: concavity of `L(·,x)`,
   concavity of `g`, and `g(u*) = -p*(-u*)` (line 11303).

Two unnumbered counterexamples justify the constraint qualification and must be kept: 10989
(`f₁ = ξ₂`, `f₂ = ξ₁² − ξ₂` — a unique optimal solution with no Kuhn–Tucker vector) and 11007
(linear constraints only, but no feasible point in `ri C`).

## The book is defective here

* **Corollary 29.4.1 (12151) has no proof at all, and drops the properness hypothesis** its own
  Theorem 29.4 carries. Its clause that the perturbation functions of `(P)` and `(cl P)` agree on a
  neighbourhood of `0` is **false** without it. It is *stated and refuted* in `Section29.lean`.
  The counterexample this file used to record — `F u x = −∞` on a line `L ⊆ ℝ²` through the origin,
  `+∞` off it — works but is more than is needed: what is wanted is a proper affine `dom F`
  containing the origin in its relative interior, and on `ℝ¹` the cheapest such set is `{0}`. The
  refutation is eight lines. **Only the perturbation clause fails**: the corollary's first clause,
  that `(cl P)` is strongly consistent, is true without properness, and so is the Kuhn–Tucker
  clause, because the adjoint never sees the closure.
* ~~**Theorem 29.4's printed proof is wrong at 12139.**~~ **Withdrawn — the book is right and this
  record was wrong.** The claim was that the printed step `((cl F)u)(y) = −∞` for *all* `y` fails
  because "`cl f` is `+∞` outside `cl (dom f)`". That describes the lower semicontinuous hull `f̄`,
  not `cl f`. Rockafellar defines the closure by cases at line **2177** — for an improper convex `f`
  taking `−∞` somewhere, `cl f` is *the constant function `−∞`* — and line **2231** draws exactly the
  contrast this record had backwards: "`f̄(x)` is `−∞` on `cl (dom f)` and `+∞` outside
  `cl (dom f)`, whereas `(cl f)(x)` is `−∞` **everywhere**, for such a function `f`." The step at
  12137–12141 is correct on both sides, and the backbone's `clBifun_apply_eq_clFn` takes the same
  route through `clFn_of_exists_eq_bot`. `api.md`'s `Adjoint.lean` record had the convention right
  all along. (The cited line 12139 is also a display-math delimiter; the sentence is at 12137.)
* **Corollary 31.2.1's polyhedral strengthening (13379) is asserted with the proof explicitly
  omitted** — "However, the proof will not be given here". Both halves are proved in
  `Section31.lean`. What the omitted proof costs, and very likely why it was skipped: in the
  *composed* setting condition (a) does two jobs, an exact sum on `ℝⁿ` and an exact image along `A`,
  and the polyhedral form must replace both. The sum is `IsExactSum.of_polyhedral`; **the image had
  no backbone constructor at all** until this round's §12.4.
* **Corollary 31.5.1 (13889) has no printed proof either**, and the inventory's "stated without
  proof" list did not have it. It is a genuine `Homeomorph` in `Section31.lean`: bijectivity is
  Theorem 31.5, and continuity of the inverse is the **unnumbered contraction property of the
  proximation** at 13851–13885 — now named `prox_contraction`, with `prox_lipschitzWith_one`
  beside it. Theorem 24.4's closedness of the graph is *not* needed.
* **Corollary 32.3.2's finiteness clause (13999) is false as stated** — it omits properness. For the
  improper `f ≡ −∞`, `ri (dom f) = ℝⁿ`, so every non-empty compact convex `C` satisfies the
  hypotheses and the supremum is `⊥`. Rockafellar's proof cites Theorem 10.1 for continuity and then
  compactness, and neither step excludes the value. The *attainment* clause survives without
  properness; it is finiteness that fails. `Section32.lean` carries `Proper f`.
* **Two hypotheses the book states and does not use.** Theorem 32.1 (13927) says "let `C` be a
  convex set contained in `dom f`" and never uses the convexity — the proof needs only that a
  relative interior point can be prolonged past itself inside `C`. Corollary 32.4.1 (14057) is
  proved by passing to `conv S` and citing Theorem 32.2, and the detour is unnecessary, because
  Theorem 32.4 asks nothing of `C` and applies to `S` directly. Neither is an error; both are
  recorded on the surface so a reader matching statement to statement is not surprised.
* **Stated with no printed proof**: Cors 27.2.1, 28.2.2, 28.3.1, 28.4.1, 31.5.1.

## Other notes

* **Thm 27.1 is a nine-clause omnibus** whose proof (10449) is a one-line pointer list to §§8, 13,
  14, 23, 25. The clauses sit at three different backbone layers — split them.
* **Thm 30.4 is a ten-clause disjunction** of sufficient conditions, and the printed proof argues
  **(a), (c), (e)**; says "Dually, (b), (d) and (f) imply that normality holds" with **no argument**;
  gives **(g)** one compressed sentence via Thm 27.1(d); disposes of **(h)** as "similarly … a
  special case of (a)"; and of **(i), (j)** as "Of course, (i) and (j) are contained in (g) and
  (h)". All ten are proved in `Section30.lean`, each docstring recording what the book supplied.
* **Thm 30.4's clauses (i) and (j) are false as stated** (12665): the containment in (g) and (h)
  needs the objective to be proper. Over a zero-dimensional `X` with `F0 ≡ +∞`, every point is an
  optimal solution, so `argmin (F0)` is non-empty and bounded, while no sublevel set of `F0` is
  non-empty at any finite `α`. With properness, `argmin (F0)` *is* a level set at its own finite
  minimum and the book's one-word containment is right. This is the only place in §30 where a
  hypothesis had to be added; four others could be dropped, because the adjoint cannot distinguish
  `F` from `cl F`.
* **Within Thm 30.4 only clauses (c) and (d) are G**, and `inventory.md`'s marks for (a) and (b)
  are exactly backwards: (a) sits in a `[FiniteDimensional ℝ U]` section and (b) in a
  `[FiniteDimensional ℝ Y]` one. Cors 30.2.1 and 30.5.2 are C as well — the latter runs on
  Cor 29.1.4. Hence `7/3` in the table above, measured from the backbone's `variable` blocks rather
  than from the shape of the statements. Same failure mode as §25's `0/11`, which was really `3/8`.
* **The `X` in §29's G/C column is `inventory.md`'s "stated without proof" mark**, not a scope
  deferral — the legend lives in `inventory.md` and there are exactly two `X`s in the book. §29's is
  Corollary 29.4.1, and it is dealt with in full rather than deferred.
* **§29's G/C entries for Cors 29.1.4 and 29.1.6 are exchanged.** Measured by `#check`ing whether
  `FiniteDimensional` survives into the cited backbone signatures: **29.1.4 is C** (both lemmas it
  specialises carry `[FiniteDimensional ℝ U]`, and it genuinely fails against a discontinuous
  functional — gotchas LIB8), **29.1.6 is G** (`infBifun_eq_bot_of_mem_relint` carries
  `omit [FiniteDimensional ℝ U]`; it is Theorem 7.2 applied to `inf F`). The count `5/6/1X` survives
  by coincidence. Cor 29.1.3 is C only as an *equivalence* — its "in which case" half is purely
  algebraic — and **Thm 29.1 is not merely G but layer-A**: §29's core needs no topology at all.
* **"Thm 29.3 comes out of §36" names the module, not the route.** `isSaddlePoint_lagrangian_iff`
  lives in `Saddle/Minimax.lean` because that is where `IsSaddlePoint` and `saddleLagrangian` are
  defined; the proof is Rockafellar's own, and its one non-trivial ingredient is
  `clFn_zero_eq_iSup_iInf`, which is §12. §29 is not gated on §36 in any sense.
* **The book's "optimal solution" is not `argmin`.** Rockafellar is explicit at 11715 that one does
  not speak of optimal solutions to an inconsistent program, so the two notions differ at both
  improper values. `Section29.lean` carries `IsOptimalSolution` with a bridge; that is what makes
  Theorem 29.3's `−∞` branch statable.
* Two load-bearing unnumbered counterexamples in §30: 12671 (an *abnormal* closed proper program
  with a genuine duality gap — `(Fu)(x) = exp(−√(ux))` on the first quadrant, `inf F0 = 1` but
  `sup F*0 = 0`) and 12715 (a normal program with an optimal solution whose dual has none).
* Line 12667 names Thm 30.4(e)/(f) applied to linear programs the **Gale–Kuhn–Tucker Duality
  Theorem** with no separate numbered statement.
* The contraction property of `prox` (13851–13885) is unnumbered running text and is what makes
  Cor 31.5.2 work — it is now named, as `prox_contraction` in `Section31.lean`, and it is also what
  gives Cor 31.5.1 its continuous inverse.
* **§31's `Optimization/Prox.lean` results are the *source* of §37's Cors 37.5.1/37.5.2, not the
  other way round.** `Saddle/Monotone.lean` imports `Optimization/Prox.lean` and instantiates §31's
  `subgradientRelHomeomorph` and `isMaximalMonotoneRel_subgradientRel` at
  `prodPairing (innerₗ U) (innerₗ X)`. Nothing in `Section31.lean` imports a `Saddle/` module and
  nothing should.
* **§31's `10/2` was wrong, and the shape of the error is new.** Measured: **7 G** (31.1, 31.3,
  31.3.1, 31.4, 31.4.2 — all over bare `AddCommGroup`/`Module`), **2 C** (31.4.1, 31.4.3, both
  marked correctly), and **3 mixed**, which the two-column scheme cannot express: Thm 31.2 is G in
  its adjoint formula, properness, convexity, closedness, `inf F 0` and `dom F`, and C in
  `ri (dom F)` and both strong-consistency characterisations, which go through
  `Convex.relint_image`; Cor 31.2.1's condition (a) is G and its condition (b) is C. Separately,
  **31.5, 31.5.1 and 31.5.2 are marked G and are C *in the formalisation only*** — Moreau's theorem
  is a Hilbert-space theorem and the G mark is mathematically right; finite-dimensionality enters
  only through Theorem 27.2's attainment argument. That is a backbone limitation rather than an
  inventory error, and it is the first time the two have had to be distinguished.
* §32's two examples at 14017–14043 show `C ⊆ ri(dom f)` in Cor 32.3.2 cannot be weakened to
  `C ⊆ dom f` even for closed `f`. Keep both. Cor 32.3.4 is the theoretical basis of the simplex
  method (a remark at 14013).
* **Thm 32.3 diverges from the book deliberately** — *not* Cor 32.3.3, which is what this note used
  to say. The backbone does not state the book's `sup_C f = sup_E f` with `E` the extreme points of
  `C ∩ L⊥`, because fixing `L⊥` would force an inner product on a development that otherwise needs
  none; it proves the two ends instead (the `ContainsNoLine` case, and Cor 32.3.3 for a complement
  chosen *inside the proof*). The **surface restores the book's form**, at the cost of re-running
  the decomposition — see §32's `## Backbone gaps`. **Cor 32.3.3 itself is the book's statement
  verbatim**: the arbitrary complement never reaches its conclusion, which is bare attainment, so
  there is nothing to flag on it and "strictly stronger" has no content there.
* **§32's G/C marks are wrong for Cors 32.1.1 and 32.2.1**, which are C, not G: they specialise
  `exists_isFace_forall_eq_of_isMaxOn` and `ConvexFn.iSup_sdiff_relint`, both of which carry
  `[FiniteDimensional ℝ]`, and the finite-dimensionality is irreducible — they run on Theorems 18.2
  and 18.4, which need a non-empty relative interior. The real split is **4 G / 7 C**. The two
  general results left are also the section's most general: Thm 32.2 and Thm 32.4 both live over a
  bare `Module ℝ E`, with no topology at all.
* Mixed-case labels: `Corollary 27.2.2`, `28.3.1`, `29.1.5`, `31.5.1`.
* **`r` counts the *inequality* constraints.** In Rockafellar `f₁, …, f_r` are the inequalities
  (`fᵢ ≤ 0`) and `f_{r+1}, …, f_m` the equalities. Stating it the other way round is an easy slip —
  this round's brief made it — and `Section28.lean`'s docstring says so explicitly.
* **§28's `0/9` was wrong; the real split is 5 G / 4 C.** G: 28.1, 28.3, 28.3.1, 28.4, 28.4.1 —
  none of their proofs uses finite dimension, 28.3's saddle-point half being `iSup`/`iInf` of the
  Lagrangian plus `isSaddlePoint_iff_iSup_eq_iInf`, and 28.4 with its corollary pure minimax
  bookkeeping. C: 28.1.1 (Heine–Borel through recession cones) and 28.2 with both its corollaries
  (`ri`). Caveat: Theorem 28.3's *clause (c)* row and `corollary_28_3_1_kuhnTucker` are C, routing
  through Theorem 23.8. This is the **third consecutive round** in which a Part plan's G/C column
  has been found wrong.
* **Corollary 28.3.1's book hypothesis is stronger than its proof.** Rockafellar states it for "a
  program satisfying the hypothesis of Theorem 28.2"; the proof uses only the *conclusion*. Carried
  with `∃ u, IsKuhnTuckerVector u`, which is how the book itself states the parallel Cor 28.4.1.
* **The preface note at line 277 is half right.** Corollary 28.2.1 does have an easier proof than
  Theorem 28.2, but it cannot replace it in a formalization: Corollary 28.2.2 — purely linear
  constraints with a feasible point in `ri C` — is *not* an instance of 28.2.1. Both are carried.
* Unnumbered example deposits: 11309–11596 (the decomposition principle), 12731–13136 (duals of
  ordinary convex programs), 13381–13465 (linear programming), 13691–13733 (Problems I and II).
