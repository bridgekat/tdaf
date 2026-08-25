/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Surface.Rockafellar.Part4.Section17
import Tdaf.Surface.Rockafellar.Part4.Section18
import Tdaf.Surface.Rockafellar.Part4.Section19
import Tdaf.Surface.Rockafellar.Part4.Section20
import Tdaf.Surface.Rockafellar.Part4.Section21
import Tdaf.Surface.Rockafellar.Part4.Section22

/-!
# Rockafellar, Part IV: Representation and Inequalities

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §§17–22. This module imports the six
section modules and adds nothing of its own.

| § | module | subject |
|---|---|---|
| 17 | `Part4.Section17` | Carathéodory's Theorem |
| 18 | `Part4.Section18` | Extreme Points and Faces of Convex Sets |
| 19 | `Part4.Section19` | Polyhedral Convex Sets and Functions |
| 20 | `Part4.Section20` | Some Applications of Polyhedral Convexity |
| 21 | `Part4.Section21` | Helly's Theorem and Systems of Inequalities |
| 22 | `Part4.Section22` | Linear Inequalities |

65 of Part IV's 70 numbered results have declarations. The five that do not are §22's
**elementary-vector development** — Lemmas 22.4 and 22.5, Corollary 22.4.1, and Theorems 22.6 and
22.7 (Tucker's complementarity theorem) — deferred by scope: they are a substantial body of
combinatorial matroid theory rather than convex analysis. Theorems 22.1–22.3 and Farkas' Lemma
(Corollary 22.3.1) are here.

## Two results the book gets wrong

**Corollaries 17.1.4 and 17.1.6 are false as stated**, and `Part4.Section17` does not omit them: it
states each as a proposition and *refutes it in Lean* (`corollary_17_1_4_false`,
`corollary_17_1_6_false`). Both counterexamples live on `ℝ¹`. The root cause is that an *affine*
dependency has coefficients summing to zero, so both signs occur, while a *conical* dependency can
have every coefficient of one sign — and then the book's "minimal `α′` on the vertical line" does
not exist.

## What this Part settles about the backbone

Theorem 20.5 — every polyhedral convex set is locally simplicial — is proved in the backbone
(`Polyhedral/Simplicial.lean`) and not by the book's two-line sketch, which merely asserts the
triangulation of a polyhedron near a point. §10's Theorem 10.2 does **not** depend on it either:
`Analysis/Convex/Simplicial.lean` proves upper semicontinuity relative to a simplex at every point
of it, not only at a vertex, so the "intuitively obvious" barycentric fact the book never proves is
never invoked.

Rockafellar's `λ ≥ 0⁺` convention, first modelled in `Part2.Section09` as the index type
`ExtCoeff`, is *inherited* rather than re-invented by §19's Theorems 19.5.1, 19.6 and 19.7.
-/
