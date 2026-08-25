# Part II — Topological Properties (§6–§10)

`Tdaf/Surface/Rockafellar/Part2.lean` → `Part2/Section06.lean` … `Section10.lean`.

**84 numbered results: 21 G, 63 C.** Every section leans on finite dimension; all of it specialises
backbone layer D, so the surface stays thin despite the C-count.

| § | module | results | G/C | backbone it specialises |
|---|---|---|---|---|
| 6 | `Section06.lean` | 18 | 2/16 | `RelativeInterior.lean` |
| 7 | `Section07.lean` | 17 | 3/14 | `Closure.lean`, `RelativeInterior.lean` |
| 8 | `Section08.lean` | 18 | 13/5 | `Recession/{Cone,Function,ConeHull}.lean` |
| 9 | `Section09.lean` | 18 | 3/15 | `Recession/Closedness.lean` |
| 10 | `Section10.lean` | 13 | 0/13 | `Continuity.lean`, `Convergence.lean` |

## Hazards

* **Thm 6.2 (`ri C ≠ ∅` for non-empty convex `C`) silently underwrites most of §§7, 9, 10, 11, 16,
  18, 20.** It is the single fact that makes this Part finite-dimensional, and it is false in
  infinite dimensions.
* **`cl f` is case-split** (2177) and `epi (cl f) = cl (epi f)` is asserted "by definition" (2185)
  but holds only for proper `f`. The backbone already proves agreement with the book's definition
  (`ConvexFn.clFn_eq_lscHull`, `RelativeInterior.lean:1131`) — **do not re-prove it here**, contrary
  to an earlier plan draft that listed this as a surface obligation.
* **The `λ ≥ 0⁺` convention** (3301, restated 3236): `λᵢCᵢ` *means* `0⁺Cᵢ` when `λᵢ = 0`, not `{0}`.
  Needed by Thms 9.6, 9.7, 9.8 (and again in §19). Introduce an explicit extended-scalar type, or
  split each statement into two cases — but do it once, here, and reuse it in §19.
* **`direction` is a quotient object** (2495, equivalence classes of half-lines) that the book never
  formally types, yet `conv S` for mixed sets in §§17–19 depends on it. Model via the
  homogenisation cone; `HullDirections.lean` already takes this route.
* `f0⁺` is deliberately overloaded with §5's `fλ` (2703), and the "recession cone of `f`" (2849) is
  neither `0⁺(dom f)` nor `0⁺(epi f)` — the book warns of this itself.
* **"Locally simplicial"** (3409) is defined but the barycentric-coordinate fact Thm 10.2 needs is
  called "intuitively obvious" (3417) and never proved. Thm 20.5 supplies it, also by assertion —
  so §10 and §20 share one gap, to be filled once, in §20.
* Thm 8.5's second formula involves `f(x+λy) − f(x)` with possibly infinite values; check the
  `∞ − ∞` convention there.
* Mixed-case labels: `Theorem 6.1`, `Corollary 6.6.2`, `9.1.3`, `9.2.2`.
* Unnumbered example deposits: 2523–2557 and 2773–2819 (recession cones and recession functions).
