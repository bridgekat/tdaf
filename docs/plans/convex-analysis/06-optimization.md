# Sub-plan 6 — Constrained extremum problems

Covers Rockafellar §27–§32.

This is where the library pays off for applications. The organising decision is
[D8](00-overview.md#d8): a convex program *is* a perturbation bifunction, and everything (objective,
Lagrangian, dual program, Kuhn–Tucker vectors) is obtained from it by **partial conjugation**.

---

## 6.1 `Optimization/Minimum.lean` — §27

**Status: Theorem 27.1 (a), (b), (c), (d), (f), (g), (h) and (i), Theorems 27.2 and 27.4, the
27.3 in full — general case *and* polyhedral refinement — and Corollaries 27.3.2 and 27.3.3 are
done. Everything except (e) and Corollary 27.3.1.**

Theorem 27.1 is a summary: nine facts about `inf f` and `argmin f`, each a restatement of an earlier
result in terms of `f*` at the origin. It is the ideal first theorem of this sub-plan because it
forces all the earlier APIs to line up — and it did: (a) and (b) went straight through, and the
other seven turned out to be exactly the parts of the book that were still deferred elsewhere.
Eight of the nine are now in. The only one left is (e), which cannot be *stated* without a
reflexive pairing: `∂f*(0)` a singleton is a statement about `E**`.

| Lean name | book | status |
|---|---|---|
| `argmin`, `mem_argmin_iff_zero_mem_subgradient`, `convex_argmin` | §27's opening remarks | done |
| `conj_zero_eq_neg_iInf`, `iInf_eq_neg_conj_zero`, `zero_mem_dom_conj_iff` | **Thm 27.1(a)** | done |
| `argmin_eq_subgradient_conj_zero` | **Thm 27.1(b)** | done |
| `iInf_ne_bot_and_argmin_eq_empty_iff`, `iInf_ne_top` | **Thm 27.1(c)** | done — (a) and (b) composed with Thm 23.3's second half, now in `Subgradient/Existence.lean`. Only one of the book's two finiteness bounds appears on each side: `f*(0) ≠ ⊥` and `⨅ f ≠ ⊤` hold for *every* proper `f` |
| `argmin_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj`, `zero_mem_interior_dom_conj_iff_recessionConeFn_eq_zero`, `exists_setOf_le_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj`, `argmin_nonempty_and_isBounded_iff_exists_setOf_le` | **Thm 27.1(d)**, both sentences, and the sublevel-set reading that Thm 30.4(g) states | done — and it needs **no** Cor 13.3.4, contrary to the book's proof: Cor 14.2.2 already says every level set is bounded exactly when the origin is interior to `dom f*`, and Thm 27.2 turns that into existence of a minimiser |
| — | Thm 27.1(e) | **not done** — `∂f*(0)` a singleton lives in `E**`, so a reflexive pairing is needed to state it |
| `recessionCone_setOf_le_eq_polarCone_dom_conj`, `recessionCone_argmin_eq_polarCone_dom_conj` | **Thm 27.1(f)** | done — Thm 8.7 composed with Thm 14.2, which is now in `Recession/Conjugate.lean` |
| `supportFn_setOf_le`, `supportFn_argmin`, `conj_flip_conj_add_coe` | **Thm 27.1(g)**, both sentences | done. The first needs **no shifted-function API**: Cor 13.2.1 computes the closure of a generated function as a support function directly, and `conj_flip_conj_add_coe` identifies the level set it produces as `{x ∣ f**(x) - α ≤ 0}`. The second is Thm 27.1(b) plus Thm 23.2 |
| `iInf_supportFn_setOf_le`, `epsSubgradient_conj_zero` | **Thm 27.1(h)** | done — Thm 23.6 for `f*` at the origin, once the level sets of `f` above `inf f` are identified with the ε-subdifferentials of `f*` |
| `zero_mem_closure_dom_conj_iff`, `zero_notMem_closure_dom_conj_iff`, `recessionFn_le_neg_coe_iff` (in `Duality/Level.lean`) | **Thm 27.1(i)**, both sentences | done — the first is Cor 13.3.4(a) at the origin, available for a general `y₀` as `mem_closure_dom_conj_iff`; the second is that with the quantifier negated. It needed **no Thm 8.5 work**: `recessionFn_le_coe_iff_forall` is already Thm 8.5 through Thm 8.1's `a = 1` test. Rockafellar's `y ≠ 0` and his restriction of `x` to `dom f` are both automatic |
| `argmin_nonempty_of_recessionConeFn_eq_zero`, `isCompact_argmin_of_recessionConeFn_eq_zero`, `exists_pos_forall_exists_mem_argmin_dist_lt` | **Thm 27.2**, all three assertions | done |
| `tendsto_infDist_argmin`, `isBounded_range_of_tendsto_iInf`, `mem_argmin_of_mapClusterPt` | Cor 27.2.1 | done |
| `tendsto_of_argmin_eq_singleton` | Cor 27.2.2 | done |
| `recessionConeFn_add_indicatorFn`, `exists_forall_le_of_recessionConeFn_inter_eq_zero` | **Thm 27.3**, non-polyhedral case | done |
| `exists_forall_le_of_inter_subset_constancySpace_inter_linealitySpace` | **Thm 27.3**, general case with the constancy/linearity recession hypothesis | done — strictly weaker hypothesis than the `= {0}` row above |
| `exists_linearProj`, `eq_of_sub_mem_constancySpace`, `exists_forall_le_of_polyhedral_of_inter_subset_constancySpace` | **Thm 27.3**, polyhedral refinement | done — and it does **not** need Helly, see below |
| `argmin_nonempty_of_recessionConeFn_subset_constancySpace` | the refinement with `C = Rⁿ` | done |
| `argmin_nonempty_of_polyhedralFn`, `exists_forall_le_of_polyhedralFn_of_polyhedral` | **Cor 27.3.2** | done — and it does **not** rest on the polyhedral refinement, see below |
| — | Cor 27.3.1 | **not stated** — its wording could not be checked against the book; the refinement it rests on is done |
| `exists_forall_le_of_forall_le_zero` | Cor 27.3.3, non-polyhedral case | done |
| `le_of_mem_subgradient_of_neg_mem_normalCone`, `exists_mem_subgradient_neg_mem_normalCone` | **Thm 27.4** | done |

### What actually happened

**Theorem 27.1(a) needs no hypotheses at all.** `f*(0) = ⨆ x (0 - f x) = -(⨅ x, f x)`; Rockafellar's
standing "closed proper convex" is there for the *rest* of Theorem 27.1. The Lean statement is
therefore `conj_zero_eq_neg_iInf (B) (f)`, with no `hf` and no `hc`.

**Theorem 27.1(b) is Theorem 23.5 (d) read at the origin.** `x ∈ ∂f*(0)` is
`f*(0) + f**(x) ≤ ⟨x, 0⟩`; Fenchel–Moreau turns `f**` into `f`, the pairing term is `0`, and what is
left is `f x ≤ -f*(0) = inf f`. The `EReal` step is `EReal.le_sub_iff_add_le` with `c = 0`, which
needs no finiteness because `0` is neither `⊥` nor `⊤` — so the theorem has no properness hypothesis
either.

**Theorem 27.4 splits into a hypothesis-free half and an `IsExactSum` half**, as planned.
`le_of_mem_subgradient_of_neg_mem_normalCone` is three lines: the subgradient inequality and the
normality inequality add. `exists_mem_subgradient_neg_mem_normalCone` is Theorem 23.8 applied to
`h + δ(· | C)` plus `∂δ(· | C) = N_C`, and Rockafellar's two hypotheses (`ri (dom h)` meets `ri C`;
`C` polyhedral and `ri (dom h)` meets `C`) are two ways of supplying the `IsExactSum` instance.

**`argmin` is a definition, not `IsMinOn f Set.univ`.** It is quantified over constantly, and
`{x | ∀ z, f x ≤ f z}` unfolds to exactly the subgradient inequality at `y = 0`, which makes
`mem_argmin_iff_zero_mem_subgradient` a `simp`. `mem_argmin_iff_isMinOn` is the bridge to Mathlib.

**Theorem 27.2 is Theorem 8.7 plus Theorem 8.4 plus Mathlib's lower-semicontinuous extreme value
theorem.** Any nonempty level set is closed and convex, has the same recession cone as `f`
(`recessionCone_setOf_le`), hence is compact (`isCompact_iff_recessionCone_eq_zero`);
`LowerSemicontinuousOn.exists_isMinOn` attains a minimum on it, and off it `f` is larger.

**The ε–δ clause did not need Rockafellar's nested compactness.** He intersects a nest of closed
bounded sets `S_δ = lev_{inf f + δ} f \ (M + ε·int B)` and derives a contradiction from a common
point. One application of the extreme value theorem replaces the whole argument: if
`K = lev_{inf f + 1} f \ (M + ε·int B)` is empty then `δ = 1` works; otherwise `f` attains a
minimum on the compact `K` at some `b`, `b ∉ M` forces `inf f < f b`, and any `δ` with
`inf f + δ < f b` does the job. That is `exists_pos_forall_exists_mem_argmin_dist_lt`.

**Corollaries 27.2.1 and 27.2.2 are one lemma about `Metric.infDist`.** `tendsto_infDist_argmin`
says that along any minimising net `infDist (u i) (argmin f) → 0`; it is stated for an arbitrary
filter, since nothing about sequences is used. Boundedness of the sequence
(`isBounded_range_of_tendsto_iInf`) then splits the range into a finite head and a tail inside a
closed ball; the cluster-point half (`mem_argmin_of_mapClusterPt`) is `clusterPt_iff_nonempty` plus
the triangle inequality; and Corollary 27.2.2 is the singleton case, where
`Metric.infDist_singleton` turns the conclusion into `dist (u i) x → 0`. Corollary 27.2.2 needs no
recession hypothesis of its own: a one-point minimum set *is* a level set, so Theorem 8.7 forces
`0⁺f = {0}`.

**Theorem 27.3's non-polyhedral case is Theorem 9.3 plus Theorem 27.2.** The recession calculus is
`recessionConeFn_add_indicatorFn`: `recessionFn_add` gives `(h + δ(·|C))0⁺ = h0⁺ + δ(·|0⁺C)`, and
because the second summand only takes the values `0` and `⊤` the sublevel condition splits into
`h0⁺ y ≤ 0` and `y ∈ 0⁺C`. That is exactly what a *general* sum lemma cannot do — for
`h(x) = -x` and `g(x) = x` on `ℝ` the recession cone of `h + g` is all of `ℝ` while
`0⁺h ∩ 0⁺g = {0}` — so the lemma is stated for indicators, not for sums. The degenerate case
`dom h ∩ C = ∅` is handled separately: `h` is then `+∞` throughout `C` and every point of `C`
minimises, which is what Rockafellar means by "if `f` is identically `+∞` the infimum is trivially
attained throughout `C`".

**The polyhedral refinement of Theorem 27.3 does not need Helly.** Rockafellar proves it from
Theorem 21.5, applied to `C` together with the level sets `lev_α h`, `α > inf`; Theorem 21.5 is
still not formalised, and the refinement no longer waits for it. The directions of constancy of `h`
form a subspace, and `exists_linearProj` projects `E` along it: `h` is unchanged (it is constant
along the fibres), the image of `C` is polyhedral, and the common recession cone collapses to `{0}`,
which is the hypothesis of the general case. Polyhedrality of `C` enters exactly once, through
`Polyhedral.recessionCone_image` — a linear map commutes with `0⁺` on a polyhedral set and, in
general, on no other kind, since for a general closed convex set the image need not even be closed.

**The same projection strengthens the general case.** The recession hypothesis
`0⁺h ∩ 0⁺C = {0}` that `exists_forall_le_of_recessionConeFn_inter_eq_zero` carries is stronger than
it needs to be: it is enough that every common direction of recession be a direction of constancy of
`h` *and* a direction of linearity of `C`, which is what
`exists_forall_le_of_inter_subset_constancySpace_inter_linealitySpace` assumes. There the projection
is along `constancySubmodule h ⊓ linealitySubmodule C`, the image of `C` is literally `C ∩ N`, and
no polyhedrality is used.

**Corollary 27.3.1 is not stated.** Its exact wording could not be checked against the book, and the
project's rule is not to attach a book number to a guessed statement. What the refinement yields —
the unconstrained `argmin_nonempty_of_recessionConeFn_subset_constancySpace` — is stated without
one.

**Corollary 27.3.2 does not need any of that.** The book derives it from 27.3.1;
`argmin_nonempty_of_polyhedralFn` gets it directly from the finitely generated description of the
epigraph (Theorem 19.1). A lower bound forces every generating *direction* upward, so the vertical
coordinate is minimised over `epi f` at one of the finitely many generating *points* — no
closedness, no properness, no Helly. Restricting `f` to `C` is then Rockafellar's own vertical
prism. This is what lets Theorem 29.2's optimal-solution clause through as well. Corollary 27.3.1
still routes through the refinement.

Corollary 27.3.3's non-polyhedral half needs none of that either: the constraint set is
`⋂ i {x | f i x ≤ 0}`, its recession cone is `⋂ i 0⁺f i` by Corollary 8.3.3 and Theorem 8.7, and
Theorem 27.3 applies.

## 6.2 `Optimization/Perturbation.lean` — §29 (generalized convex programs)

**Status: Theorem 29.1 is done in full**, together with the closedness and convexity half of
Corollary 29.1.1 and the existence statement that Theorem 23.4 supplies.

```lean
abbrev Bifun (U X : Type*) := U → X → EReal
def graphFn (F : Bifun U X) : U × X → EReal := fun p => F p.1 p.2
def ConvexBifun (F : Bifun U X) : Prop := ConvexFn (graphFn F)
def domBifun (F : Bifun U X) : Set U := {u | ∃ x, F u x ≠ ⊤}

/-- The perturbation function `inf F`. -/
noncomputable def infBifun (F : Bifun U X) : U → EReal := fun u => ⨅ x, F u x

/-- Kuhn–Tucker vectors, Rockafellar's own definition. -/
def KuhnTucker (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : Set V :=
  {v | infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
    (⨅ u, (((B u v : ℝ) : EReal) + infBifun F u)) = infBifun F 0}
```

| Lean name | book | status |
|---|---|---|
| `convexFn_infBifun`, `dom_infBifun` | **Thm 29.1**, first assertion | done |
| `mem_kuhnTucker_iff_forall_le` | the inequality reformulation the book gives next | done |
| `mem_kuhnTucker_iff_neg_mem_subgradient` : `v ∈ KT ↔ -v ∈ ∂(inf F)(0)` | **Thm 29.1**, second assertion | done |
| `kuhnTucker_eq_neg_subgradient`, `convex_kuhnTucker`, `isClosed_kuhnTucker` | **Cor 29.1.1**, the closed-convex clause | done |
| `kuhnTucker_nonempty_of_stronglyConsistent` | **Cor 29.1.4**, nonemptiness half | done |
| `supportFn_neg_set`, `posHomogeneous_dirDeriv_infBifun`, `convexFn_dirDeriv_infBifun`, `supportFn_kuhnTucker` | **Cor 29.1.1**, the derivative clause | done |
| `kuhnTucker_eq_empty_iff` | **Cor 29.1.2** | done |
| `kuhnTucker_eq_singleton_of_dirDeriv_eq`, `kuhnTucker_eq_singleton_of_hasGradientAt` | **Cor 29.1.3** | done |
| `dirDeriv_infBifun_eq` | **Cor 29.1.4**, the derivative formula | done |
| `proper_infBifun_of_stronglyConsistent`, `continuousOn_infBifun_interior`, `bddAbove_kuhnTucker_of_strictlyConsistent`, `infBifun_ne_top_of_mem_domBifun` | **Cor 29.1.5** | done |
| `isBounded_kuhnTucker_of_strictlyConsistent`, `isCompact_kuhnTucker_of_strictlyConsistent` | **Cor 29.1.5**, the compactness clause | done — on `isBounded_iff_forall_bddAbove`, Cor 13.2.2 in the norm. The only §29 statement needing `FiniteDimensional ℝ V` |
| `infBifun_eq_top_of_notMem_domBifun`, `infBifun_eq_bot_of_mem_relint` | **Cor 29.1.6** | done |
| `polyhedralFn_mapLin`, `PolyhedralFn.clFn_eq_of_mem_dom` | **Cor 19.3.1**, the prerequisite | done |
| `PolyhedralBifun`, `polyhedralBifun_iff`, `PolyhedralBifun.polyhedralFn_infBifun`, `kuhnTucker_nonempty_of_polyhedralBifun`, `polyhedral_kuhnTucker_of_polyhedralBifun` | **Thm 29.2** (polyhedral case) | done |
| `argmin_nonempty_of_polyhedralBifun`, `polyhedral_argmin_of_polyhedralBifun` | **Thm 29.2**, the optimal-solution clause | done — on Cor 27.3.2, which turned out not to need Helly. It needs **less** than the book asks: `inf F 0 ≠ -∞` suffices for existence (an optimal value of `+∞` makes every point optimal); finiteness is needed only for polyhedrality of the minimum set |
| `isSaddlePoint_lagrangian_iff`, `iSup_lagrangian`, `iSup_lagrangian_eq`, `iInf_lagrangian_ne_top` | **Thm 29.3** | done — in `Saddle/Minimax.lean`, where §36 is |
| `domBifun_eq_image_dom_graphFn`, `mem_relint_slice`, `clBifun_apply_eq_clFn`, `infBifun_clBifun_eq`, `domBifun_subset_domBifun_clBifun`, `domBifun_clBifun_subset_closure` | **Thm 29.4** | done, in `Optimization/Adjoint.lean` where `clBifun` is defined. **The note that it needed saddle-point existence (Thm 37.6) was wrong** — Theorem 29.4 is a §6/§7 statement about closures: Theorem 6.6 puts a relative interior point of `dom (graph F)` over `u`, the prolongation principle (Thm 6.4) makes its second coordinate relatively interior to the slice, and Theorem 7.5 writes `(cl F) u` and `cl (F u)` as the same limit along a segment. Cor 29.4.1 is still not done |

`Consistent`, `StronglyConsistent`, `StrictlyConsistent` are `0 ∈ dom F`, `0 ∈ ri (dom F)`,
`0 ∈ int (dom F)` respectively. They are the constraint qualifications of Part VI and connect
directly to [`Exact.lean`](03-relint-recession.md#36-tdafanalysisconvexdualityexactlean--d5).

### What actually happened

**The definitional worry recorded here was real, and the book settled it.** The plan's draft defined
`KuhnTucker` by the inequality `inf F 0 ≤ ⟨u, v⟩ + inf F u`, which would have made Theorem 29.1 an
`Iff.rfl`. Rockafellar's §29 defines a Kuhn–Tucker vector as one for which `⨅ u {⟨u, v⟩ + inf F u}`
is **finite and equal to** `inf F 0`, and that is what the file uses. The inequality form is then a
short lemma (`mem_kuhnTucker_iff_forall_le`), because `iInf_add_infBifun_le` — evaluate at `u = 0`
— makes the infimum automatically `≤ inf F 0`, so equality is the same as the pointwise bound.

**Theorem 29.1's convexity clause is Theorem 5.7 at a projection.** `infBifun F` is
`fun u => ⨅ x, graphFn F (u, x)`, which is exactly the shape of `convexFn_iInf_right` from
`Operations/Image.lean`; `dom_infBifun` is `dom_iInf_right`. Neither needed a new argument.

**The subgradient half is a finite-real rearrangement, nothing more.** `-v ∈ ∂(inf F)(0)` unfolds to
`inf F 0 + ⟨u - 0, -v⟩ ≤ inf F u`, and moving the real term `⟨u, v⟩` to the other side of an
`EReal` inequality is `coe_add_neg_le_iff`, a three-line private lemma. Because the equivalence is
proved rather than definitional, `kuhnTucker_eq_neg_subgradient` gives `KT = -(∂(inf F)(0))` as
sets, and closedness, convexity and nonemptiness then transfer for free from
`Subgradient/{Defs,Existence}.lean` through `Set` negation, which is a preimage under a
homeomorphism.

**Corollary 29.1.4's nonemptiness needs nothing new.** `StronglyConsistent F` is `0 ∈ ri (dom F)`
and `dom (inf F) = dom F`, so `subgradient_nonempty_of_mem_relint_dom` (Theorem 23.4) applies
directly. Its compactness clause is a different statement — boundedness of `∂f x` for `x` in the
*interior* — which `Subgradient/Existence.lean` does not carry, so it is left out.

## 6.3 `Optimization/Lagrangian.lean` — §28–§29 via partial conjugation

**Status: the Lagrangian and its identification with the concave conjugate are done.** §28's
ordinary convex programs are done too, but in a **file of their own** — see §6.3a.

```lean
noncomputable def lagrangian (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : V → X → EReal :=
  fun v x => ⨅ u, ((B u v : ℝ) : EReal) + F u x

theorem lagrangian_eq_concaveConj :
    lagrangian B F v x = concaveConj B (fun u => -(F u x)) v
theorem mem_kuhnTucker_iff_iInf_lagrangian :
    v ∈ KuhnTucker B F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      (⨅ x, lagrangian B F v x) = infBifun F 0
```

| Lean name | book | status |
|---|---|---|
| `lagrangian_eq_concaveConj` | the identification the design rests on | done |
| `iInf_lagrangian` : `⨅ x L(v, x) = ⨅ u (⟨u, v⟩ + inf F u)` | the identity §29 states after the definition | done |
| `mem_kuhnTucker_iff_iInf_lagrangian`, `iInf_lagrangian_le` | **§29**, the Lagrangian description of Kuhn–Tucker vectors, and weak duality | done |
| `concaveFn_lagrangian`, `lagrangian_le` | `L(·, x)` concave; `L(v, x) ≤ F 0 x` | done |
| — | `ineqBifun` | **not needed** — see §6.3a |
| `exists_isKuhnTuckerVector_of_slater` (in `Optimization/Program.lean`) | **Thm 28.2** (Slater) | done |
| — | **Thms 28.1, 28.3, 28.4**, Cor 28.3.1 | surface, and 28.3 needs §36 |

`lagrangian` is a partial concave conjugate; every Lagrangian fact is a partial-conjugate fact. This
is what lets §28, §29, §36 and §37 share proofs instead of repeating them four times.

**§28 splits.** The `(m+3)`-tuple packaging and the book's numbering go to the surface, but
**Theorem 28.2 (existence of Kuhn–Tucker vectors under Slater's condition) stays in the backbone** —
review finding C3. Slater for finitely many convex inequalities is not about coordinates
(`Fin m → ℝ` with the product order generalises verbatim), it is the single most-used result in
convex optimisation practice, and sending it to the surface would force applications to import a
`Rockafellar`-namespaced, `EuclideanSpace`-specific file to get strong duality — a layering
inversion. So `Optimization/Lagrangian.lean` is to carry "Slater ⇒ `KuhnTucker` nonempty and
compact" (Corollary 29.1.4 plus §21's theorem of the alternative), through the bifunction attached
to a system of convex inequalities and affine equations:

```lean
noncomputable def ineqBifun (f₀ : E → EReal) (f : Fin m → E → EReal) (r : ℕ) :
    Bifun (Fin m → ℝ) E := fun u x =>
  f₀ x + ∑ i : Fin m,
    (if (i : ℕ) < r then indicatorFn {x | f i x ≤ (u i : EReal)} x
                    else indicatorFn {x | f i x = (u i : EReal)} x)
```

Then §28's Theorems 28.1, 28.3, 28.4 and the Kuhn–Tucker theorem (Corollary 28.3.1) become
surface-level specialisations of backbone results.

### What actually happened

**The Lagrangian is a concave conjugate on the nose, not `-(conj B … (-v))`.** The plan's draft
routed it through the convex conjugate at a reflected point. Since `Duality/ConcaveConj.lean`
already defines `concaveConj B g v = ⨅ u (⟨u, v⟩ - g u)`, the identification is
`lagrangian B F v x = concaveConj B (fun u => -(F u x)) v` with `a - (-b) = a + b` as the only step,
and no sign flip on the argument at all. Concavity of `L(·, x)` is then `concaveFn_concaveConj`
applied pointwise in `x`, with **no hypothesis on `F`** — not convexity, not properness.

**Swapping the two infima is the one place with content.**
`⨅ x L(v, x) = ⨅ u (⟨u, v⟩ + inf F u)` is `iInf_comm` plus the fact that a *real* constant moves
through an infimum on `EReal`. The latter is `Tdaf.EReal.iInf_add_coe`, which had to be added to
`Order/EReal.lean`: it is proved by adding `-r` back, since adding a real is a monotone bijection
of `EReal` but `iInf` does not commute with it definitionally. With that in hand,
`mem_kuhnTucker_iff_iInf_lagrangian` is a rewrite of §6.2's definition, and weak duality
`iInf_lagrangian_le` is `iInf_add_infBifun_le` read through it.

**Slater was never blocked, and `ineqBifun` was never needed.** An earlier revision of this
sub-plan recorded that §21's theorems of the alternative cover only systems of *inequalities* while
§28 allows mixed inequality/equality systems. That is wrong on both counts.
`alternative_of_convex_system_affine` in `Helly.lean` keeps the affine constraints in a **second
index type** `κ` — precisely the mixed form — and an equality constraint splits into two affine
inequalities, `Sum.elim a fun k => -(a k)`, exactly as Rockafellar does it. And `ineqBifun` is a
packaging of the constraints as a bifunction over `Fin m → ℝ`; Theorem 28.2 is a statement about
the constraint functions themselves, so the packaging buys nothing on the way in. See §6.3a.

## 6.3a `Optimization/Program.lean` — §28

**Status: done.** Theorem 28.2 (existence of a Kuhn–Tucker vector under Slater's condition),
Corollary 28.2.1, Corollary 28.2.2, and the equality-constrained variant.

```lean
def feasibleSet (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ) : Set E :=
  {x | (∀ i, f i x ≤ 0) ∧ ∀ j, b j x ≤ 0}
noncomputable def programLagrangian (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) : E → EReal :=
  fun x => f₀ x + (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * b j x : ℝ) : EReal)
noncomputable def optimalValue (f₀) (f) (b) : EReal := ⨅ x ∈ feasibleSet f b, f₀ x
structure IsKuhnTuckerVector (f₀) (f) (b) (l : ι → ℝ) (μ : κ → ℝ) : Prop
```

| Lean name | book | status |
|---|---|---|
| `feasibleSet`, `programLagrangian`, `optimalValue`, `IsKuhnTuckerVector` | §28's vocabulary | done |
| `programLagrangian_le_of_mem_feasibleSet`, `programLagrangian_eq_top`, `programLagrangian_eq_coe` | the elementary facts the proof runs on | done |
| `exists_isKuhnTuckerVector_of_slater` | **Thm 28.2** | done |
| `exists_isKuhnTuckerVector_of_mem_dom` | **Cor 28.2.1** | done |
| `exists_isKuhnTuckerVector_of_affine` | **Cor 28.2.2** | done, as `[IsEmpty ι]` |
| `exists_multipliers_of_slater_eq` | equality constraints, signed multipliers | done |
| — | Thms 28.1, 28.3, 28.4, Cor 28.3.1 | surface, and 28.3 needs §36 |

### What actually happened

**The whole proof is Theorem 21.2 applied to `Option ι`.** Add the objective as one more strict
inequality, `f₀ x - α < 0` with `α` the (finite) optimal value. Branch (a) of the alternative would
produce a feasible point strictly below the optimal value, so branch (b) holds and yields
multipliers `c : Option ι → ℝ` and `μ : κ → ℝ`. Everything after that is the single step
`0 < c none`: at the Slater point every `c (some i) * f i x` and every `μ j * a j x` is `≤ 0`, so
`c none = 0` would force all the other `c` to vanish, contradicting `c ≠ 0`. Normalising by
`c none` produces the Kuhn–Tucker vector.

**The Lagrangian here is not `lagrangian`.** `programLagrangian` is the concrete
`f₀ + ∑ lᵢ fᵢ + ∑ μⱼ bⱼ`; `Optimization/Lagrangian.lean`'s `lagrangian` is the partial concave
conjugate of a bifunction. They agree once `ineqBifun` is defined, and that identification — which
would make §28 an instance of §29/§30 rather than a parallel development — is the one piece of §28
still worth building.

**Rockafellar's hypothesis (b) subsumes the plan's `hdom`.** `dom f₀ ⊆ dom (f i)` implies
`ri (dom f₀) ⊆ dom (f i)`, so only the former is a hypothesis.

## 6.4 `Optimization/Adjoint.lean` — §30

**Status: Theorem 30.1 is done in full, and Theorem 30.2 with weak duality (Corollary 30.2.2) is
done.** Theorems 30.3–30.5 are done in `Optimization/Normal.lean`; see §6.4a.

```lean
/-- The adjoint bifunction: the conjugate of the graph function, with a sign flip on the first
factor. -/
noncomputable def adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun Y V :=
  fun y v => ⨅ p : U × X, (F p.1 p.2 + ((Bu p.1 v - Bx p.2 y : ℝ) : EReal))
```

| Lean name | book | status |
|---|---|---|
| `adjointBifun_eq_neg_conj_graphFn` : `(F* y)(v) = -f*(-v, y)` | **Thm 30.1**, the computation | done |
| `concaveFn_graphFn_adjointBifun` | **Thm 30.1**, concavity | done, with no hypothesis on `F` |
| `closedConcaveFn_graphFn_adjointBifun` | **Thm 30.1**, closedness of `F*` | done, with no hypothesis on `F` |
| `concaveAdjointBifun`, `clBifun`, `ClosedBifun` | the vocabulary **Thm 30.1** is stated in | done |
| `concaveAdjointBifun_adjointBifun_eq_clBifun` | **Thm 30.1**, `F** = cl F` | done |
| `concaveAdjointBifun_adjointBifun_eq_self` | **Thm 30.1**, `F** = F` for closed convex `F` | done |
| `adjointBifun_clBifun` | `(cl F)* = F*` — what §34's closure operations run on | done |
| `ImageClosedBifun`, `ClosedBifun.imageClosedBifun` | the slice-wise closedness §33's correspondence runs on | done |
| `adjointBifun_zero_eq_concaveConj` — the dual objective is the **concave** conjugate of `−inf F` | **Thm 30.2** | done |
| `adjointBifun_zero_le`, `iSup_adjointBifun_zero_le` : `sup F* 0 ≤ inf F 0` | **Cor 30.2.2**, weak duality | done |
| `mem_kuhnTucker_iff_adjointBifun_zero_eq` | **Thm 30.5**, the half holding without normality | done |
| — | Cor 30.2.1 | not done |
| `Normal`, **Thms 30.3, 30.4, 30.5** | §6.4a | done |

**Sign warning.** Theorem 30.2 is about the **concave** conjugate: the book (line 12487) says `F*0`
is the conjugate of the *concave* function `−inf F`, and `g* ≠ −(−g)*`. `inf F` is convex; its
convex conjugate is not `F*0`. Every §30 statement mixing the two must go through `concaveConj`,
which `Duality/ConcaveConj.lean` defines (D2).

### What actually happened

**The sign flip lives in the argument, not in a new pairing.** The plan expected
`negFst (prodPairing Bu Bx)` from `Duality/Pairing.lean` to carry it. Reading Rockafellar's formula
`⟨u, -v⟩ + ⟨x, y⟩` as a pairing of `(u, x)` with `(-v, y)` is cheaper: `F*` becomes `conj` for the
*plain* `prodPairing`, evaluated at a reflected point, and every `conj` lemma stays usable verbatim.
`negFst` remains available but is not used here. Concavity of the adjoint is then `convexFn_conj`
composed with the linear reflection `adjointSwap : (Y × V) →ₗ[ℝ] (V × Y)` through
`convexFn_compLin` — three lines, and again with no hypothesis on `F`.

**The two finite terms are grouped inside one coercion.** `F u x - ⟨x, y⟩ + ⟨u, v⟩` is written
`F u x + ((⟨u, v⟩ - ⟨x, y⟩ : ℝ) : EReal)`: the same number, but it can never produce `∞ - ∞`, which
the plan's draft — two separate `EReal` operations — could.

**Closedness of `F*` needed one missing lemma, in a new file.** It is `closedFn_conj` transported
along `adjointSwap`, but `Operations/Image.lean` is a layer-A module and has `convexFn_compLin`
with no `ClosedFn` counterpart; Mathlib, meanwhile, has only the *outer* composition
(`Continuous.comp_lowerSemicontinuous`) and not the inner one. The fix is
`Operations/Closed.lean` — a small layer-B companion holding `lowerSemicontinuous_comp` and
`closedFn_compLin` — after which the clause is two lines. The instance binder has to be
`[IsContinuousPairing (prodPairing Bu Bx).flip]`, not the un-flipped form: the un-flipped one
demands a topology on `U × X`, which nothing in §30 supplies. Note also that `Bu` and `Bx` must
stay *implicit* in any statement whose instance binders mention them — an explicit `(Bu …)` shadows
the section variable the binder refers to, and instance search then fails on a different `Bu`.

**`ClosedBifun` and `ImageClosedBifun` are different predicates, and §33 needs the weaker one.**
`ClosedBifun F` is closedness of the *graph* function on `U × X`; `ImageClosedBifun F` asks only
that each slice `F u` be closed. A slice of a closed function is closed
(`ClosedBifun.imageClosedBifun`, via `lowerSemicontinuous_comp` at `x ↦ (u, x)`), but not
conversely — image-closedness says nothing about the joint behaviour. Rockafellar's bracket sees
exactly the slice-wise closure, which is why Theorem 33.2 has *two* distinct equations and why
§33's one-to-one correspondence is a statement about image-closed bifunctions.

**Theorem 30.2 is `iInf_comm` again, and the concave conjugate is genuinely needed.**
`(F* 0)(v) = ⨅ u (⟨u, v⟩ + inf F u)` is the same infimum swap as `iInf_lagrangian`, and the result
is `concaveConj Bu (fun u => -(inf F u))` — so `adjointBifun_zero_eq_concaveConj` is a rewrite, and
Corollary 30.2.2 is `iInf_add_infBifun_le` from §6.2. `mem_kuhnTucker_iff_adjointBifun_zero_eq`
then says the Kuhn–Tucker vectors are exactly the dual-optimal `v` at which the duality gap closes,
which is the half of Theorem 30.5 that needs no normality hypothesis.

## 6.4a `Optimization/Normal.lean` — §30 from Corollary 30.2.2 on

**Status: done** except clauses (h) and (j) of Theorem 30.4.

```lean
theorem clFn_zero_eq_iSup_iInf (hf : ConvexFn f) :
    clFn f 0 = ⨆ y : F, ⨅ x : E, (((B x y : ℝ) : EReal) + f x)
def Normal (F : Bifun U X) : Prop := clFn (infBifun F) 0 = infBifun F 0
noncomputable def supBifun (G : Bifun Y V) : Y → EReal := fun y => ⨆ v, G y v
def ConcaveNormal (G : Bifun Y V) : Prop := clConcave (supBifun G) 0 = supBifun G 0
```

| Lean name | book | status |
|---|---|---|
| `clFn_zero_eq_iSup_iInf` | the computation the section rests on | done |
| `clFn_infBifun_zero_eq_iSup_adjointBifun` | **Cor 30.2.2**, first formula | done, without closedness |
| `clConcave_supBifun_zero_eq_infBifun_concaveAdjointBifun`, `clConcave_supBifun_adjointBifun_zero_eq` | **Cor 30.2.2**, second formula | done |
| `normal_iff_iSup_adjointBifun_eq` | **Thm 30.3**, (a) ⟺ (c) | done |
| `concaveNormal_adjointBifun_iff`, `normal_iff_concaveNormal_adjointBifun` | **Thm 30.3**, (b) | done |
| `StronglyConsistent.normal`, `StrictlyConsistent.normal` | **Thm 30.4(a)** | done |
| `ConcaveStronglyConsistent.concaveNormal`, `normal_of_concaveStronglyConsistent_adjointBifun` | **Thm 30.4(b)** | done |
| `normal_of_kuhnTucker_nonempty` | **Thm 30.4(c)** | done |
| `mem_kuhnTucker_iff_adjointBifun_zero_eq_iSup`, `kuhnTucker_eq_setOf_isMax`, `isGreatest_adjointBifun_zero_of_mem_kuhnTucker` | **Thm 30.5** | done |
| `supBifun`, `domConcaveBifun`, `ConcaveConsistent`, `ConcaveStronglyConsistent`, `ConcaveNormal` | the concave mirrors of §29's vocabulary | done |
| `forall_conj_eq_top_iff`, `not_concaveConsistent_adjointBifun_iff`, `concaveConsistent_adjointBifun_iff`, `not_consistent_iff_exists_supBifun_eq_top`, `consistent_iff_forall_supBifun_ne_top` | **Cor 30.2.1**, both halves | done |
| `le_limsup_nhds`, `clConcave_eq_limsup_or`, `liminf_infBifun_eq_iSup_adjointBifun`, `limsup_supBifun_adjointBifun_eq` | **Cor 30.2.3** (the `liminf` form) | done — on `clFn_eq_liminf_or`, now in `Closure.lean` |
| `ConcaveKuhnTucker`, `mem_concaveKuhnTucker_iff_neg_mem_kuhnTucker`, `concaveNormal_of_concaveKuhnTucker_nonempty`, `normal_of_concaveKuhnTucker_adjointBifun_nonempty` | **Thm 30.4(d)** | done |
| `PolyhedralBifun.normal`, `ConcavePolyhedralBifun`, `ConcavePolyhedralBifun.concaveNormal`, `normal_of_concavePolyhedral_adjointBifun` | **Thm 30.4(e), (f)** | done |
| `shiftBifun`, `infBifun_shiftBifun`, `convexBifun_shiftBifun`, `adjointBifun_shiftBifun_zero`, `supBifun_adjointBifun`, `mem_domConcaveBifun_adjointBifun`, `normal_of_exists_setOf_le` | **Thm 30.4(g)** | done — and the book's "i.e." is a theorem, not a step: `0 ∈ int (dom (F 0)*) ⇒ 0 ∈ int (domConcaveBifun F*)` needs *all slices of a closed convex bifunction have the same recession function* (`recessionFn_slice_eq`, Thm 8.3 on the epigraph). No properness assumed; the one §30 statement needing `FiniteDimensional ℝ U` |
| `normal_of_argmin_nonempty_and_isBounded` | **Thm 30.4(i)** | done — with `Proper (F 0)`, which the book's "(i) is contained in (g)" quietly needs |
| — | Thm 30.4 (h), (j) | not done — the concave mirrors, blocked structurally: they are (g), (i) applied to `F*`, whose slices live on `V`, and `V` is a plain module throughout §29–§30 while Thm 27.1(d) and Cor 13.3.4(c) need it finite-dimensional |
| `isSaddlePoint_lagrangian_iff_normal_and_optimal`, `isSaddlePoint_lagrangian_iff_le_adjointBifun`, `iInf_lagrangian_eq_adjointBifun_zero` | Cor 30.5.1 (saddle points of `L`) | done — in `Saddle/Minimax.lean` |

### What actually happened

**Everything after Theorem 30.2 is one lemma.** `clFn_zero_eq_iSup_iInf` is Fenchel–Moreau at the
origin: `f**(0) = ⨆ y (⟨0, y⟩ - f*(y)) = ⨆ y (-f*(y))`, and `-f*(y) = ⨅ x (f x - ⟨x, y⟩)` is the
dual objective at `-y`. The reindexing is `Function.Surjective.iSup_comp` on negation, and the rest
of the file is bookkeeping.

**The dual half is the primal half negated.** `-(sup G) = inf (-G)` pointwise, so
`clConcave (sup G) 0 = -(clFn (inf (-G)) 0)` and the primal formula applies with the pairings
`Bx.flip`, `Bu.flip`; the sign bookkeeping is
`-(adjointBifun Bx.flip Bu.flip (-G) 0 x) = concaveAdjointBifun Bu Bx G 0 (-x)`, and a second
negation reindexing closes it. Composing with `F** = cl F` gives the book's second formula.

**The concave mirrors of §29's vocabulary had to be built, and they are cheap.**
`domConcave (supBifun G) = domConcaveBifun G` mirrors `dom_infBifun`, and
`ConcaveFn.clConcave_eq_of_mem_relint_domConcave` mirrors Theorem 7.4. The latter belongs with
`clConcave` in `Duality/ConcaveConj.lean`, which is layer C and does not import
`RelativeInterior`; it lives in `Normal.lean` until a second consumer appears.

## 6.5 `Optimization/Fenchel.lean` and `Optimization/Moreau.lean` — §31

**Status: Theorems 31.1, 31.3, 31.4 and 31.5 are done** (31.3 with the linear transformation taken
to be the identity, which is the setting of 31.1; 31.5 without its existence-and-uniqueness half).

```lean
theorem fenchel_duality (hex : IsExactSum B f (-g)) :
    (⨅ x, f x - g x) = ⨆ y, concaveConj B g y - conj B f y
```

`concaveConj` (`g*(y) = ⨅ x, ⟨x,y⟩ - g x`) lives in `Duality/ConcaveConj.lean` rather than in
`Concave.lean`: it needs a pairing, and `Concave.lean` is a layer-A file that should not acquire
separation and Hahn-Banach as dependencies. `prox` for Theorem 31.5 still has to be built, and
needs an inner-product space and a real existence-and-uniqueness proof.

Rockafellar's hypotheses — (a) `ri (dom f) ∩ ri (dom g) ≠ ∅`, and (b) `f, g` closed with
`ri (dom g*) ∩ ri (dom f*) ≠ ∅` — are the primal-side and dual-side instances of `IsExactSum`, with
attainment of the sup under (a) and of the inf under (b). Stating the theorem against `IsExactSum`
gives all four variants, including both polyhedral ones, from one proof.

**Theorem 31.2 did not need the `EReal` splitting lemma this section used to demand.** The row
below said the blocker was "an `EReal` lemma splitting `⨅ (a, b) (u a + v b)` into `⨅ u + ⨅ v`".
That route is unnecessary. Going through the *concave* face of Theorem 16.3 — `concaveConj_compLin`
— turns the dual value at `y` into a supremum over the fibre `A'⁻¹{y}`, and the only arithmetic
left is `(⨆ i, u i) - c = ⨆ i, (u i - c)` for `c ≠ ⊥`, which `IsExactSum.conj_left_ne_bot` already
supplies.

| Lean name | book | status |
|---|---|---|
| `concaveConj_sub_conj_le_sub` | weak duality (the first display of the proof of Thm 31.1) | done |
| `fenchel_duality`, `exists_concaveConj_sub_conj_eq`, `isGreatest_concaveConj_sub_conj` | **Thm 31.1**, condition (a) | done |
| `iInf_sub_eq_neg_iInf_conj_sub`, `fenchel_duality_of_closed`, `exists_sub_eq_iInf` | **Thm 31.1**, condition (b) | done |
| `concaveConj_compLin`, `fenchel_duality_comp`, `exists_concaveConj_sub_conj_comp_eq` | **Thm 31.2** | done |
| — | **Cor 31.2.1** | not done — its exact statement was not verified against the source, and an unverified statement is not written |
| `neg_mem_subgradient_neg_iff_add_concaveConj_eq`, `sub_eq_concaveConj_sub_conj_iff`, `iInf_sub_eq_of_sub_eq`, `iSup_sub_eq_of_sub_eq`, `iInf_sub_eq_iff_exists_kuhnTucker` | **Thm 31.3**, Cor 31.3.1, with `A = id` | done |
| `sub_comp_eq_concaveConj_sub_conj_iff`, `iInf_sub_comp_eq_of_sub_eq`, `iSup_sub_comp_eq_of_sub_eq`, `iInf_sub_comp_eq_iff_exists_kuhnTucker`, `concaveConj_sub_conj_comp_le_sub` | **Thm 31.3**, Cor 31.3.1, with a general `A` | done. **Theorem 31.3 itself needs nothing from Theorem 31.2** — only the `IsAdjointPair` datum, to identify `⟨A x, z⟩'` with `⟨x, A' z⟩`; only Cor 31.3.1's attainment clause consumes `concaveConj_compLin`. It needs neither `f` nor `g` closed, for the reason recorded below for `A = id`. Cor 31.3.1 does need `Proper (-g)` on all of `G`, which `IsExactSum.proper_right` does **not** give — that comes from `IsExactImage.proper`, so the image hypothesis is load-bearing for more than attainment |
| `iInf_add_indicatorFn_eq_neg_iInf_conj_add_indicatorFn`, `iInf_mem_eq_neg_iInf_mem_neg_polarCone`, `neg_conj_le_of_mem_neg_polarCone` | **Thm 31.4**, the duality equation | done |
| `add_conj_eq_zero_iff_mem_subgradient_and_pairing_eq_zero`, `forall_le_of_mem_subgradient_of_pairing_eq_zero`, `conj_le_conj_of_mem_subgradient_of_pairing_eq_zero` | **Thm 31.4**, the optimality conditions | done |
| — | **Cor 31.4.1** (the orthant), Cors 31.4.2–3 | not done — instances of Thm 31.4 in a coordinate space |
| `quadFn`, `conj_quadFn`, `conj_quadFn_sub`, `moreau_add`, `infConv_quadFn_ne_top` and companions, `mem_subgradient_iff_infConv_eq` | **Thm 31.5 (Moreau)**, the identity and the Kuhn–Tucker characterisation | done |
| `moreauObj`, `prox`, `argmin_moreauObj_nonempty`, `mem_argmin_moreauObj_iff`, `eq_of_sub_mem_subgradient`, `existsUnique_sub_mem_subgradient`, `prox_eq_iff`, `argmin_moreauObj_eq_singleton`, `infConv_quadFn_eq_moreauObj_prox`, `prox_add_prox_conj` | **Thm 31.5**, attainment and uniqueness | done (`Optimization/Prox.lean`), in finite dimensions |
| `x = ∇(f* □ w) z`, `x* = ∇(f □ w) z` | **Thm 31.5**, the gradient formulas | not done — need Thm 26.3 on the Moreau envelopes |
| `dist_prox_prox_le`, `lipschitzWith_prox`, `subgradientRelHomeomorph` | **Cor 31.5.1** | done (`Optimization/Prox.lean`) |
| `isMaximalMonotoneRel_subgradientRel` | **Cor 31.5.2** | done (`Optimization/Prox.lean`) |

Moreau's theorem (31.5) needs an inner-product structure and is the source of the proximal operator.
Its *identity* is proved in an arbitrary real Hilbert space (`Optimization/Moreau.lean`); the
attainment and uniqueness clauses, and the two corollaries, are in `Optimization/Prox.lean` and are
finite-dimensional, because attainment is Theorem 27.2 and `Optimization/Minimum.lean` proves that
only in `ℝⁿ`. Corollary 31.5.2 gives maximal monotonicity of `∂f` without going through the much
harder §24, exactly as Rockafellar says.

### What actually happened

**There is no separation argument in the file.** Rockafellar separates `epi f` from
`{(x, μ) | μ ≤ g x + α}`. Here the separation has already been spent, once, inside Theorem 16.4, so
Theorem 31.1 is Theorem 27.1(a) (`inf h = -h*(0)`) applied to `h = f + (-g)`, with
`IsExactSum.conj_add_apply` splitting `h*(0)` into `⨅ y (f*(y) + (-g)*(-y))` and
`neg_concaveConj` rewriting `(-g)*(-y)` as `-g*(y)`. Four lines of `rw`, once the `∞ - ∞` side
conditions are discharged from properness of the two summands.

**Weak duality needs no hypothesis.** `concaveConj_sub_conj_le_sub` was written with `f x ≠ ⊥` and
`g x ≠ ⊤` and the linter reported both unused. The reason is that each collision lands on the side
that makes the *dual* value `-∞`: if `f x = ⊥` then `f* y = ⊤` and `g*(y) - f*(y) = ⊥`, and if
`g x = ⊤` then `g* y = ⊥` and the dual value is `⊥` again.

**Theorem 31.3 needs no superdifferential.** Rockafellar's second Kuhn–Tucker condition is
`Ax ∈ ∂g*(u*)`, phrased with the superdifferential of a concave function. Since that
superdifferential is `-∂(-g)`, the condition is spelled `-y ∈ ∂(-g) x` and
`neg_mem_subgradient_neg_iff_add_concaveConj_eq` identifies it with the concave Fenchel equality
`g x + g*(y) = ⟨x, y⟩`. The theorem itself is then pure `EReal` arithmetic: squeezed between
`⟨x,y⟩ ≤ f x + f*(y)` and `g x + g*(y) ≤ ⟨x,y⟩`, the equality `f x - g x = g*(y) - f*(y)` forces
both squeezes to be tight. The finiteness bookkeeping is three private lemmas proved by
`induction a <;> … <;> simp_all`, which discharges all 81 infinite cases at once.

**Condition (b) is condition (a) transposed.** `fenchel_duality` applied to `(f*, g*)` over
`B.flip`, with `biconj_eq_self` and `biconcaveConj_eq_self` collapsing the biconjugates, gives
`⨅ y (f* - g*) = -(⨅ x (f - g))`; negating turns the dual-side attainment of a supremum into
primal-side attainment of an infimum. The closed proper concave `g` is spelled
`ClosedProperConvexFn fun x => -(g x)` — the sign dictionary applied to the bundled interface,
which also spares §31 a "closed proper concave" structure of its own.


**Theorem 31.4 did not go through Theorem 31.1 either.** Rockafellar applies Fenchel's theorem with
`g = -δ(· | K)`; but `δ(· | K)` is an ordinary convex function, so the shorter route is the one
Theorem 31.1 itself takes — Theorem 27.1(a) applied to `f + δ(· | K)`, then
`IsExactSum.conj_add_apply` at the origin, then `conj_indicatorFn_eq_indicatorFn_polarCone`
(Theorem 14.1) for the second factor. The `0 - y` the splitting produces is exactly the sign flip
that turns the polar cone `K°` into Rockafellar's `K*`, which is why `K*` is spelled
`-(polarCone B K)` and `mem_neg_polarCone` is the only new definition the section needs. The
optimality conditions came out as a three-way package: `add_conj_eq_zero_iff_…` says that for
`x ∈ K` and `y ∈ K*` the values agree exactly when `y ∈ ∂f x` and `⟨x, y⟩ = 0`, and the other two
lemmas turn that into primal and dual optimality. Weak duality for the cone program
(`neg_conj_le_of_mem_neg_polarCone`) needs nothing but `sub_le_conj`.

**Corollary 31.4.1 is deliberately not stated.** It is Theorem 31.4 with `K` the non-negative
orthant of a coordinate space; the componentwise complementarity `ξⱼ ξⱼ* = 0` is a statement about
`EuclideanSpace ℝ (Fin n)`, not about the pairing, so it belongs to the surface layer.

**Moreau's Theorem 31.5 needed no finite-dimensionality.** `w(z - ·)` is finite and continuous
everywhere, so `IsExactSum.of_continuousAt` — not `of_relint` — supplies the constraint
qualification, and the theorem holds in an arbitrary real Hilbert space paired with itself by
`innerₗ E`. The proof is again Theorem 27.1(a) on `f + w(z - ·)` with the conjugate split at the
origin; `conj_quadFn_sub` computes `(w(z - ·))*(y) = ⟨z, y⟩ + w y`, and the reindexing `y ↦ -y`
turns that into `w(z - y) - w z`, which is what makes the dual infimum appear. Pulling the real
constant `-w z` out of the infimum needed a new `Tdaf.EReal.iInf_add_coe`, the dual of the existing
`iSup_add_coe`.

**The last step of Moreau's proof cancels, so finiteness had to be earned.** `(f* □ w) z` is
bounded above by evaluating at any point of `dom f*` (Theorem 12.2 makes that nonempty) and bounded
below because `conj B (f + w(z - ·)) 0` dominates `-(f x₀ + w(z - x₀))`. Once it is a real number,
`(f □ w) z = w z - (f* □ w) z` follows and the finiteness of the *other* envelope comes for free;
`infConv_quadFn_ne_top`, `infConv_quadFn_ne_bot` and their dual companions record all four.

**The Kuhn–Tucker characterisation is one line of algebra plus a squeeze.** For `z = x + y`,
`(f x + w y) + (f*(y) + w x) = (f x + f*(y)) + (w x + w y)` and `⟨x, y⟩ + w x + w y = w z`, so
Fenchel's inequality puts the left-hand side at or above `w z`, which `moreau_add` identifies with
the sum of the two infima. Each summand is at least its own infimum, so equality in the sum forces
equality in both — and conversely. What is *not* proved is that a splitting exists: that is
Theorem 27.2 in a Hilbert space, and `Optimization/Minimum.lean` has it only in finite dimensions.

## 6.6 `Optimization/Maximum.lean` — §32

**Status: Theorems 32.1, 32.2, 32.3 and 32.4 are done**, with Corollaries 32.1.1, 32.2.1, 32.3.2
(both clauses) and 32.4.1. Maximising a convex function is short and self-contained; it depends on
§18, on §10 for the one attainment statement, and on nothing later.

```lean
theorem ConvexFn.eq_of_isMaxOn_mem_relint (hf : ConvexFn f) (hCdom : C ⊆ dom f) {z : E}
    (hz : z ∈ ri C) (hmax : ∀ w ∈ C, f w ≤ f z) {x : E} (hx : x ∈ C) : f x = f z
```

Maximisation is spelled `∀ z ∈ C, f z ≤ f x` rather than `IsMaxOn f C x`. Every proof in the
section consumes the hypothesis by applying it at one specific point, and the unfolded form is what
`ConvexFn.epi_combo` and the subgradient inequality want; `isMaxOn_iff` is the bridge for a caller
who arrives with `IsMaxOn`.

| Lean name | book | status |
|---|---|---|
| `ConvexFn.eq_of_isMaxOn_mem_relint` | **Thm 32.1** | done |
| `exists_isFace_forall_eq_of_isMaxOn` | **Cor 32.1.1** | done |
| `ConvexFn.iSup_convexHull`, `exists_eq_of_isMaxOn_convexHull` | **Thm 32.2**, both clauses | done |
| `convexHull_sdiff_relint` (Thm 18.4, hull form), `ConvexFn.iSup_sdiff_relint`, `exists_notMem_relint_eq_of_isMaxOn`, `ConvexFn.iSup_sdiff_relint_of_containsNoLine` | **Cor 32.2.1** | done |
| `ConvexFn.iSup_extremePoints`, `exists_mem_extremePoints_eq_of_isMaxOn` | **Cor 32.3.2**, compact case, without the "attained" clause | done |
| `ConvexFn.add_le_of_forall_add_smul_le`, `ConvexFn.add_le_of_mem_recessionCone`, `ConvexFn.exists_mem_convexHull_extremePoints_le`, `ConvexFn.iSup_extremePoints_of_containsNoLine`, `exists_mem_extremePoints_eq_of_isMaxOn_of_containsNoLine` | **Thm 32.3**, both clauses | done |
| `ConvexFn.iSup_extremePoints_add_coneHull` | Thm 32.3 in representation form (no boundedness hypothesis) | done |
| `ConvexFn.eq_of_forall_le`, `exists_mem_extremePoints_isMaxOn_of_finitelyGenerated` | the two likely readings of Cors 32.3.1/32.3.3/32.3.4 | done, but **not** claimed to be those corollaries |
| — | **Cors 32.3.1, 32.3.3, 32.3.4** | not done — the book's statements could not be verified (no access to the text) |
| `exists_mem_extremePoints_isMaxOn_of_isCompact` | **Cor 32.3.2**, the "supremum is attained" clause, for `C ⊆ ri (dom f)` | done |
| `mem_normalCone_of_mem_subgradient_of_isMaxOn`, `ne_zero_of_mem_subgradient_of_isMaxOn` | **Thm 32.4** | done |
| `le_of_mem_normalCone` | **Cor 32.4.1** | done |

### What actually happened

**Theorem 32.1 is the prolongation lemma plus one convex combination.** `ri C` gives a factor
`t > 1` with `(1 - t) • x + t • z ∈ C` (`exists_one_lt_smul_mem_of_mem_relint`, the easy half of
Theorem 6.4), and `combo_prolong` says that travelling from `x` to that point at parameter `t⁻¹`
lands back on `z`. If `f x < f z`, pick a real `ξ` strictly between them; `ConvexFn.epi_combo`
then bounds `f z` by `(1 - t⁻¹) ξ + t⁻¹ ζ < ζ = f z`. The only place the hypothesis `C ⊆ dom f` is
used is in extracting the real number `ζ`.

**Corollary 32.1.1 is Theorem 18.2 with Theorem 32.1 applied to the face.**
`exists_isFace_mem_relint` produces the face having the maximiser in its *relative interior*, and
the maximum principle then makes `f` constant on it. The statement returned is the pointwise one —
every maximiser lies in a face on which `f` equals the maximum — which is what "the maximiser set
is a union of faces" means once the union is taken over maximisers.

**Theorem 32.2 needs no Carathéodory decomposition and no topology.** `{z | f z ≤ α}` is convex
(`ConvexFn.convex_le`) and contains `S` when `α` is the supremum over `S`, so `convexHull_min`
hands over `conv S`. The attainment clause is the same argument on the *strict* sublevel set
`{z | f z < f x}` (`ConvexFn.convex_lt`): a convex function that stays below its maximum throughout
`S` stays below it throughout `conv S`. Both halves are therefore stated over `Module ℝ E`, which
is why they can be reused verbatim for the extreme-point corollary in finite dimensions.

**Corollary 32.3.2 in the compact case is Minkowski fed to Theorem 32.2.**
`convexHull_extremePoints` (Corollary 18.5.1, in `Face.lean`) rewrites `C` as `conv (extreme pts)`
and the two halves of Theorem 32.2 do the rest. Rockafellar's full Corollary 32.3.2 also asserts
that the supremum is *attained*, which needs Theorem 10.1 (continuity of a convex function on
`ri (dom f)`); that clause is not here.

**Theorem 32.4 did not need Theorem 23.7.** The plan was to route it through `∂f x ⊆ N_lev(x)`.
Read directly it is three lines: the subgradient inequality gives
`f x + ⟨z - x, y⟩ ≤ f z` and maximality gives `f z ≤ f x`, so `⟨z - x, y⟩ ≤ 0` once `f x` is known
to be a real number and can be cancelled. The non-vanishing clause is the same inequality at a
point where `f` differs from the maximum. Corollary 32.4.1 is then the definitional unfolding of
`normalCone`, so it is stated as `le_of_mem_normalCone` and holds with no convexity hypothesis at
all.

**Theorem 32.3 is Theorem 18.5 plus one inequality, and the inequality is the whole content.**
Writing `x ∈ C` as `u + v` with `u ∈ conv (ext C)` and `v` in the cone of the extreme directions
(`convexHullPD_extremePoints_extremeDirections`) puts the half-line `u + t • v`, `t ≥ 0`, inside
`C`; a convex function bounded above on a half-line is non-increasing along it
(`ConvexFn.add_le_of_forall_add_smul_le`, proved by taking `t → ∞` in
`f (u + v) ≤ (1 - t⁻¹) ξ + t⁻¹ β`), so `f (u + v) ≤ f u` and Theorem 32.2 removes the hull.
Boundedness above cannot be dropped: `f x = x` on `C = [0, ∞)` has supremum `⊤` over `C` and `0` over its only
extreme point. The *representation* form `ConvexFn.iSup_extremePoints_add_coneHull`, which keeps the
directions in the index set, needs no hypothesis at all.

**Corollary 32.2.1 is stated with `¬ IsAffineHalf C`, not with `ContainsNoLine C`.** The half-line
is a counterexample to the "no lines" reading, and it is exactly the case Theorem 18.4 excludes:
`convexHull_sdiff_relint` is Theorem 18.4 in hull form, and
`ConvexFn.iSup_sdiff_relint_of_containsNoLine` recovers the reading Rockafellar has in mind by
adding `2 ≤ dim C` (`not_containsNoLine_of_isAffineHalf`).

**The attainment clause of Corollary 32.3.2 is false as the plan recorded it.** For a merely
compact convex `C ⊆ dom f` the supremum need not be attained: on the closed unit disc, `f = 0` on
the open disc and `f (cos θ, sin θ) = 1 - θ` for `θ ∈ (0, 2π]` is convex (chords between distinct
boundary points meet the circle only at their endpoints) with an unattained supremum `1`.
`exists_mem_extremePoints_isMaxOn_of_isCompact` therefore asks for `C ⊆ ri (dom f)`, which is where
Theorem 10.1 (`ConvexFn.continuousOn_relint_dom`) applies — the prerequisite the plan named, but
the hypothesis has to be in the statement, not only in the proof.

**Corollaries 32.3.1, 32.3.3 and 32.3.4 are still open, for a different reason than recorded.**
§18 is no longer the obstacle; what is missing is the *statements*. They could not be checked
against the book, and rather than invent them the file carries two unnumbered specialisations of
Theorem 32.3 that any of them plausibly is: `ConvexFn.eq_of_forall_le` (a convex function bounded
above on the whole space is constant — the ray lemma applied in both directions) and
`exists_mem_extremePoints_isMaxOn_of_finitelyGenerated` (over a finitely generated set the extreme
points are finite in number by Corollary 18.3.1, so the supremum is a maximum).

**Correction to the earlier status.** This section used to record Theorem 32.3 and Corollaries
32.2.1, 32.3.1, 32.3.3 and 32.3.4 as blocked on Theorems 18.4–18.5 for *unbounded* closed convex
sets, "which `Face.lean` currently has only for compact sets". Both halves of that are now out of
date: the unbounded representation is `convexHullPD_extremePoints_extremeDirections` in
`Representation.lean`, not `Face.lean`, and it is complete.
