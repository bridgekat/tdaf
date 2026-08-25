/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Surface.Rockafellar.Part2.Section06
import Tdaf.Surface.Rockafellar.Part2.Section07
import Tdaf.Surface.Rockafellar.Part2.Section08
import Tdaf.Surface.Rockafellar.Part2.Section09
import Tdaf.Surface.Rockafellar.Part2.Section10

/-!
# Rockafellar, Part II: Topological Properties

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §§6–10. This module imports the five
section modules and adds nothing of its own.

| § | module | subject |
|---|---|---|
| 6 | `Part2.Section06` | Relative Interiors of Convex Sets |
| 7 | `Part2.Section07` | Closures of Convex Functions |
| 8 | `Part2.Section08` | Recession Cones and Unboundedness |
| 9 | `Part2.Section09` | Some Closedness Criteria |
| 10 | `Part2.Section10` | Continuity of Convex Functions |

82 of Part II's 84 numbered results have declarations. The two that do not are Corollary 9.2.1
and Corollary 9.8.3, both recorded under `## What is not here` in `Part2.Section09` with the
backbone lemma each is waiting on. Several more are stated for two sets where the book states them
for `m` — Theorem 6.9, the `m`-ary corollaries of Theorem 9.1, Theorem 9.3, Theorem 9.8 — because
the backbone's recession-cone and convex-hull lemmas are binary; each says so in its own docstring.

Part II is where the surface becomes irreducibly finite-dimensional: 63 of the 84 results are
classified `C`, and Theorem 6.2 — a non-empty convex set has a non-empty relative interior — is the
single fact underwriting most of §§7, 9 and 10.
-/
