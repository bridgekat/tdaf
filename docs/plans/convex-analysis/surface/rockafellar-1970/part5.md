# Part V — Differential Theory (§23–§26)

`Tdaf/Surface/Rockafellar/Part5.lean` → `Part5/Section23.lean` … `Section26.lean`.

**49 numbered results: 18 G, 31 C** (plus 7 clause rows in Thm 23.5). §25 is the most irreducibly
finite-dimensional section in the book.

**DONE — all 49 numbered results have declarations**, in 249 of them. Nothing is deferred by scope
and nothing was blocked. The `G/C` column below is the *general / concrete* split, not a
theorem/corollary split; three agents in a row misread it, so it is worth saying twice.

| § | module | results | G/C | declarations | backbone it specialises |
|---|---|---|---|---|---|
| 23 | `Section23.lean` | 16 | 13/3 | 72 | `Subgradient/{Defs,Calculus,Existence,Approx}.lean` |
| 24 | `Section24.lean` | 11 | 3/8 | 48 | `Subgradient/{Monotone,OneDim,Convergence,Bounded,Primitive,Integral}.lean` |
| 25 | `Section25.lean` | 11 | 3/8 | 40 | `Subgradient/{Gradient,Rademacher,GradientLimit,Uniqueness,Reconstruction,Legendre}.lean` |
| 26 | `Section26.lean` | 11 | 2/9 | 89 | `Subgradient/{EssentiallySmooth,BoundaryDirDeriv,StrictlyConvex,Preservation,Legendre,LegendreType,Cofinite}.lean` |

Label counts by kind, for the record, because the `G/C` column keeps being read as one:
§23 is 10 theorems + 6 corollaries, §24 is 9 theorems + 2 corollaries, §25 is 7 theorems +
4 corollaries, §26 is 5 theorems + 2 lemmas + 4 corollaries.

## Gated on remediation — closed, but only half of it was where the gate said

**§23** wanted `m`-ary `IsExactSum` (remediation §4.4), and the product round built
`IsExactFinsetSum` with `of_relint` and `of_polyhedral`. That was the *interface*; what §23 needs is
the **consequence**, `IsExactFinsetSum.subgradient_finsetSum`, and `Subgradient/Calculus.lean` still
has only the binary `IsExactSum.subgradient_add`. §23 proves the `m`-ary form as a `private` lemma
and records it for hoisting. Reading a gate as closed because its constructors exist is the same
mistake as LIB17, one level down.

## Notes

* **Thm 23.5 is a seven-clause equivalence** — (a)(b)(c)(d) and the three starred variants — and all
  seven are G. One declaration per clause.
* **Thm 23.8 has two proofs in the book, and the advice here was backwards.** The "ALTERNATIVE
  PROOF" (8773) uses only separation, but it reduces `m` to `2` *by induction on Theorem 6.5* and
  omits the polyhedral clause. The printed proof goes through Theorem 16.4, which the backbone
  already carries in `m`-ary form as `IsExactFinsetSum.of_relint`, so it discharges the constraint
  qualification once and needs no induction. The printed proof is the better route; the alternative
  is the one that puts the induction back.
* Line 8477 leaves `rec(∂f(x)) =` the normal cone to `dom f` as an unproved exercise, saying it is
  verified later inside the proof of Thm 25.6. **It is not** — the backbone's proof of Thm 25.6 uses
  only the inclusion `⊆`, so nothing discharges the exercise on the way. §25 discharges it directly
  instead (`recessionCone_subgradient_eq_normalCone`, four lines, independent of Thm 25.6), and §23
  assumes it nowhere.
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

## Deferred by scope — less than this said

Only **Theorem 24.2's integral formula** `f(x) = ∫ₐˣ φ` is deferred, and nothing in the book uses it
(Thm 24.9's proof cites Cor 24.2.1, not the formula).

* **Corollary 24.2.1 is not deferred.** `Subgradient/Integral.lean` proves it in full
  (`sub_eq_intervalIntegral_rightDeriv`, `sub_eq_intervalIntegral_leftDeriv`), and that module's own
  docstring says why the stated reason does not apply: the fundamental theorem of calculus applies
  directly, with no improper integral and no Lebesgue theory of monotone functions.
* **Theorem 24.2's *existence* clause is reachable too**, not only uniqueness.
  `Subgradient/Primitive.lean` builds `f` from the graph `Γ(φ)`, which is a maximal monotone
  relation, with no integral anywhere.

## Stated without proof

Corollaries 23.5.1, 25.5.1. Mixed-case label: `Corollary 23.8.1`.
