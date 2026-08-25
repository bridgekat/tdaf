/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Caratheodory
import Tdaf.Analysis.Convex.Face
import Tdaf.Analysis.Convex.Homogenize
import Tdaf.Analysis.Convex.Optimization.Prox
import Tdaf.Analysis.Convex.Polyhedral.Cone
import Tdaf.Analysis.Convex.Subgradient.Gradient

/-!
# Eponyms

Named results of convex analysis, under the names people search for.

Every declaration here is an `alias`. The mathematics is elsewhere; this file exists because the
descriptive names the library uses — `biconj_eq_clFn`, `convexHull_extremePoints` — are the right
names for a library organised by subject, and are not the names a newcomer types first. A naming
audit found that first-guess searches succeeded 53% of the time and that **every miss was an
eponym**, so the gap is exactly this list and no wider.

An alias is deliberately cheaper than a rename: the descriptive name stays primary, `alias` records
the equality of the two, and nothing downstream has to change. Where the library already uses the
eponym as the primary name — `fenchel_duality` (Theorem 31.1), `farkas` (Corollary 22.3.1),
`helly_finite` (Theorem 21.6) — there is nothing to add and no alias appears below.

## Main results

* `fenchel_moreau` — `f** = cl f` for convex `f`.
* `fenchel_inequality` — `⟨x, y⟩ ≤ f x + f* y`.
* `jensen` — the finite-convex-combination inequality.
* `caratheodory` — a point of `conv S` is a convex combination of `n + 1` points of `S`.
* `krein_milman` — a compact convex set is the convex hull of its extreme points.
* `minkowski_weyl` — a cone is polyhedral iff it is finitely generated.
* `moreau_decomposition` — `(f □ q) z + (f* □ q) z = q z`.
* `subgradient_maximalMonotone` — `∂f` is maximal monotone.
* `perspective` — the perspective of a convex function.

## Design notes

**`subgradient_maximalMonotone` is an alias, not a relocation.** Its natural home by subject is
`Subgradient/Monotone.lean`, beside `IsMaximalMonotoneRel`, and it is stated in
`Optimization/Prox.lean` instead. That is forced, not accidental: the proof is Moreau's theorem, and
`Optimization/Prox.lean` imports `Subgradient/Monotone.lean`, so moving the statement down would be
an import cycle. The alias is what makes it findable from the predicate's side.

**`perspective` aliases a `def`, not a theorem.** `smulRight f a` is Rockafellar's `fa`, which is
the perspective function under its other name; the two are the same construction and neither name
is wrong.
-/

namespace Tdaf.ConvexAnalysis

/-- **Fenchel–Moreau**: a convex function's biconjugate is its closure. Rockafellar's
Theorem 12.2. -/
alias fenchel_moreau := biconj_eq_clFn

/-- **Fenchel's inequality**: `⟨x, y⟩ ≤ f x + f* y`, for proper `f`. Rockafellar's Theorem 12.2,
the inequality half. -/
alias fenchel_inequality := Proper.le_add_conj

/-- **Jensen's inequality** for a finite convex combination. Rockafellar's Theorem 4.3. -/
alias jensen := ConvexFn.sum_le

/-- **Carathéodory's theorem**: a point of `conv S` is a convex combination of at most
`dim E + 1` points of `S`. Rockafellar's Theorem 17.1. -/
alias caratheodory := mem_convexHull_iff_exists_fin_finrank_succ

/-- **Krein–Milman**, finite-dimensional form: a compact convex set is the convex hull of its
extreme points. Rockafellar's Theorem 18.5 for bounded sets. -/
alias krein_milman := convexHull_extremePoints

/-- **Minkowski–Weyl**: a convex cone is polyhedral exactly when it is finitely generated.
Rockafellar's Theorem 19.1 for cones. -/
alias minkowski_weyl := polyhedralCone_iff_finitelyGeneratedCone

/-- **Moreau's decomposition**: `(f □ q) z + (f* □ q) z = q z`, where `q z = ½ B z z`.
Rockafellar's Theorem 31.5. -/
alias moreau_decomposition := moreau_add

/-- **The subdifferential of a closed proper convex function is maximal monotone.**
Rockafellar's Corollary 31.5.2. -/
alias subgradient_maximalMonotone := isMaximalMonotoneRel_subgradientRel

/-- **The perspective** of a convex function, `(f a) x = a · f (x / a)` for `a > 0`, defined
through the epigraph so that the `a = 0` and improper cases come out right. Rockafellar writes it
`fa` (§5). -/
alias perspective := smulRight

end Tdaf.ConvexAnalysis
