# Part V — Differential Theory (§23–§26)

`Tdaf/Surface/Rockafellar/Part5.lean` → `Part5/Section23.lean` … `Section26.lean`.

**49 numbered results: 18 G, 31 C** (plus 7 clause rows in Thm 23.5). §25 is the most irreducibly
finite-dimensional section in the book.

| § | module | results | G/C | backbone it specialises |
|---|---|---|---|---|
| 23 | `Section23.lean` | 16 | 13/3 | `Subgradient/{Defs,Calculus,Existence,Approx}.lean` |
| 24 | `Section24.lean` | 11 | 3/8 | `Subgradient/{Monotone,OneDim,Convergence,Bounded}.lean` |
| 25 | `Section25.lean` | 11 | 0/11 | `Subgradient/{Gradient,Rademacher,GradientLimit}.lean` |
| 26 | `Section26.lean` | 11 | 2/9 | `Subgradient/{LegendreType,StrictlyConvex}.lean` |

## Gated on remediation

**§23** wants `m`-ary `IsExactSum` (remediation §4.4): Thm 23.8 is the sum rule for
`f₁ + ⋯ + f_m` under a shared-`ri` qualification, and without an indexed form the surface must
induct and re-derive properness at each step.

## Notes

* **Thm 23.5 is a seven-clause equivalence** — (a)(b)(c)(d) and the three starred variants — and all
  seven are G. One declaration per clause.
* **Thm 23.8 has two proofs in the book.** The "ALTERNATIVE PROOF" (8773) uses only separation and
  omits the polyhedral clause; it is the better route for a port, since it avoids §16's conjugacy
  machinery.
* Line 8477 leaves `rec(∂f(x)) =` the normal cone to `dom f` as an unproved exercise; it is verified
  only later, inside the proof of Thm 25.6.
* The example at 8479–8485 shows `dom ∂f` need not be convex — keep it as a test case.
* **Line 9631 warns explicitly** that maximal *monotonicity* of `∂f` (Cor 31.5.2) does **not** follow
  from Thm 24.9 plus "cyclically monotone ⇒ monotone". Keep the two facts separate; the backbone
  already does.
* §24's "complete non-decreasing curve" (9181) and its characterisation as a maximal totally-ordered
  subset of `ℝ²` (9195) are pure order theory — the natural `ℝ`-level surface for §24.
* Line 9193 leaves as "an elementary exercise" that `(x,x*) ↦ x + x*` is a homeomorphism `Γ → ℝ`.
  This is the one-dimensional shadow of Cor 31.5.1 — **do not duplicate it**; derive from §31.
* **§26: do not state a naive involution lemma.** Line 10275 warns that "the Legendre conjugate of
  the Legendre conjugate" is undefined in general; involutivity holds only within the Legendre-type
  class (Thm 26.5). The counterexamples at 10085, 10093 and 10263 — the last being `ξ₁²/4ξ₂` on the
  open upper half-plane, whose `D` is a **parabola**, not convex — pin down why the hypotheses
  cannot be weakened. Keep all three.
* **§26 "essentially smooth"** (10027) is a three-part condition (a)(b)(c); Lemma 26.2 gives the
  equivalent directional form (c′) assuming (a)(b). Carry both and the equivalence, since different
  downstream theorems use different forms.
* The one G-fragment of §25 worth isolating: the *forward* half of Thm 25.1 (differentiable ⇒
  `∇f(x) ∈ ∂f(x)`). The converse is finite-dimensional.

## Deferred by scope

**Theorem 24.2's integral formula and Corollary 24.2.1** — one-dimensional Lebesgue integration
theory, not convex analysis. Thm 24.2's *uniqueness* clause is reachable without integration and is
in scope.

## Stated without proof

Corollaries 23.5.1, 25.5.1. Mixed-case label: `Corollary 23.8.1`.
