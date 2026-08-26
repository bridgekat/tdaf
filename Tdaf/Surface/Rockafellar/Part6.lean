/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Surface.Rockafellar.Part6.Section27
import Tdaf.Surface.Rockafellar.Part6.Section28
import Tdaf.Surface.Rockafellar.Part6.Section29
import Tdaf.Surface.Rockafellar.Part6.Section30
import Tdaf.Surface.Rockafellar.Part6.Section31
import Tdaf.Surface.Rockafellar.Part6.Section32

/-!
# Rockafellar, Part VI: Constrained Extremum Problems

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §§27–32. This module imports the six
section modules and adds nothing of its own.

| § | module | subject | declarations |
|---|---|---|---|
| 27 | `Part6.Section27` | The Minimum of a Convex Function | 58 |
| 28 | `Part6.Section28` | Ordinary Convex Programs and Lagrange Multipliers | 159 |
| 29 | `Part6.Section29` | Bifunctions and Generalized Convex Programs | 82 |
| 30 | `Part6.Section30` | Adjoint Bifunctions and Dual Programs | 101 |
| 31 | `Part6.Section31` | Fenchel's Duality Theorem | 122 |
| 32 | `Part6.Section32` | The Maximum of a Convex Function | 90 |

**All 63 of Part VI's numbered results have declarations**, in 612 of them, together with all 30 of
the Part's clause rows — the highest clause density in the book. Nothing here is deferred by scope
and nothing was blocked. `Part6.Section28` is the thickest module of the surface at 2432 lines,
twice the next.

## The four gates, and why three of them were not gates

Part VI was planned as the most heavily gated Part in the book, waiting on four backbone items.
All four are closed and **three of them closed without any Lean work**, because the claim that
created them was wrong.

* **§4.1, "bundle the adjoint"** — closed by *measurement*. The library-wide count of statements
  threading an adjoint plus an `IsAdjointPair` hypothesis is 32, not the ~100 the item claimed, and
  four of the six sections it named contribute none, because the book's `A*` there is a defined
  operation rather than a transpose. §31, the section the item said would need it most, contains no
  `IsAdjointPair` outside prose: `A*` is `LinearMap.adjoint A`, and `isAdjointPair_adjoint`
  discharges the obligation. Design decision **D3** stands unmodified.
* **§4.2, the `negFst` pairing instances** — built, and used by nothing. The premise was that "§30's
  adjoint bifunctions conjugate against `negFst`". They do not: the backbone puts Rockafellar's sign
  flip on the *argument*, not on the pairing, so `⟨u, -v⟩ + ⟨x, y⟩` is the plain product pairing of
  `(u, x)` with `(-v, y)` and `conj` keeps every one of its own lemmas. Neither `Section29` nor
  `Section30` contains a `negFst`.
* **§4.8, the product transport** — likewise built and unused here. Theorem 31.2 lives on
  `Rn m × Rn n` directly, through `prodPairing`, `Convex.relint_image` and
  `intrinsicInterior_prod_eq`; no transport to `Rn (m+n)` appears anywhere in the Part.
* **§4.6, Theorem 27.1(e)** — the only one that needed work, and it needed five declarations. The
  exclusion note said `∂f*(0)` "lives in `E**` and so needs a reflexive pairing". It does not: for
  `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ` the conjugate lives on `F`, so `subgradient B.flip (conj B f) 0` is a
  subset of `E` — clause (b) had been stating exactly that set since `Optimization/Minimum.lean` was
  written. What the clause needs is `Function.Injective B`, which is free in a normed space.

## What this Part settles about the backbone

**A convex program is the tuple, not the objective**, and the correspondence is a theorem.
Rockafellar is emphatic (pp. 273, 275) that two programs with the same objective can have different
Lagrangians and different Kuhn–Tucker vectors, so `OrdinaryConvexProgram` carries
`(C, f₀, …, f_m, r)` — with `r` counting the **inequality** constraints — and
`eq_of_programLagrangian_eq` recovers all of it from the Lagrangian alone, the index `r` included.

**Theorems 28.1, 28.3 and 28.4 follow the book directly rather than specialising §§29–30**, and
the reason is a real obstruction rather than convenience. The backbone's route to Theorem 28.3 is
`isSaddlePoint_lagrangian_iff_mem_kuhnTucker`, which needs `ClosedBifun F`; an ordinary convex
program's bifunction is *not* closed under Rockafellar's blanket assumptions, since he never
assumes the `fᵢ` closed — which is why Corollary 28.1.1 has to add closedness as a hypothesis.
Deriving 28.3 from §29 would have meant silently strengthening the book's theorem. The bridge
`lagrangian_ineqBifun` is proved in full and used for what it genuinely buys.

**§31 is the source of §37's Corollaries 37.5.1 and 37.5.2, not their consumer.**
`Saddle/Monotone.lean` imports `Optimization/Prox.lean` and instantiates §31's
`subgradientRelHomeomorph` and `isMaximalMonotoneRel_subgradientRel` at a product pairing. Nothing
in `Section31` imports a `Saddle/` module and nothing should.

## Where the book is defective

* **Corollary 29.4.1 has no proof and drops the properness its own Theorem 29.4 carries.** Its
  clause that the perturbation functions of `(P)` and `(cl P)` agree near `0` is false without it,
  and
  `Section29` states it as the book does and *refutes it in Lean* — on `ℝ¹`, where the cheapest
  witness is `dom F = {0}`. Only that clause fails: strong consistency of `(cl P)` and the
  Kuhn–Tucker clause both survive, the latter because the adjoint never sees the closure.
* **Theorem 30.4's clauses (i) and (j) are false as stated.** "Of course, (i) and (j) are contained
  in (g) and (h)" needs the objective to be proper — with `F0 ≡ +∞` every point is an optimal
  solution, so the optimal set is non-empty and bounded while no sublevel set is. This is the only
  place in §30 where a hypothesis had to be *added*; four others could be dropped, because the
  adjoint cannot distinguish `F` from `cl F`.
* **Theorem 30.4's printed proof covers three of its ten clauses.** It argues (a), (c), (e); says
  "dually, (b), (d) and (f)" with no argument; gives (g) one sentence; and disposes of (h), (i), (j)
  in a half-line each. All ten are proved here, each docstring recording what the book supplied.
* **Corollary 31.2.1's polyhedral strengthening is asserted with "the proof will not be given
  here".** Both halves are proved. Why it was skipped is visible from the Lean side: in the composed
  setting the constraint qualification does two jobs, an exact sum and an exact image, and the
  polyhedral form must replace both — and the *image* constructor did not exist in the backbone
  until the round that wrote this Part.
* **Corollary 31.5.1 has no printed proof either**, which no record had noticed. It is a genuine
  `Homeomorph` here: bijectivity is Theorem 31.5, and continuity of the inverse is the unnumbered
  contraction property of the proximation, now named `prox_contraction`.
* **Corollary 32.3.2's finiteness clause is false as stated** — it omits properness, and for
  `f ≡ -∞` every non-empty compact convex `C` satisfies the hypotheses with supremum `⊥`. The
  attainment clause survives.
* **Corollary 28.3.1's hypothesis is stronger than its proof**, which uses only the conclusion of
  Theorem 28.2 rather than its hypothesis — as the book itself does for the parallel Corollary
  28.4.1.
* **Two hypotheses are stated and never used**: Theorem 32.1's convexity of `C`, and Corollary
  32.4.1's detour through `conv S`, since Theorem 32.4 asks nothing of `C` at all.

## The counterexamples

Part VI carries seven, all transcribed as Lean definitions rather than paraphrased.

* **§28** — the two that justify the constraint qualification: a program with a unique optimal
  solution and no Kuhn–Tucker vector, and one with linear constraints but no feasible point in
  `ri C`.
* **§29** — `originBifun`, the refutation of Corollary 29.4.1 as printed.
* **§30** — an *abnormal* closed proper program with a genuine duality gap, whose two extrema are
  computed (`inf F0 = 1` against `sup F*0 = 0`); and a normal program with an optimal solution whose
  dual has none.
* **§32** — the two examples showing `C ⊆ ri (dom f)` in Corollary 32.3.2 cannot be weakened to
  `C ⊆ dom f`, even for closed `f`.
-/
