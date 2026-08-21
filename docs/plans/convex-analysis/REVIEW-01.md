# Review 01 — adversarial review of the convex-analysis plan

Three independent sub-agents reviewed `00-overview.md` and `01`–`08` at commit `1b0cc08`, with
disjoint lenses (architecture/generality, factual fidelity, Lean feasibility) and no shared context.
This file records what they found, what was decided, and what is still open. It is the record file
that later agents should read before starting work, so that these obstacles are not rediscovered.

Findings are kept even where the plan was right, because "we checked this and it holds" is as useful
to a later agent as "this is broken".

---

## A. What survived

* **D1 (`E → EReal`, convexity = convex epigraph in `E × ℝ`) is confirmed, twice over.**
  Every one of Rockafellar's §4 arithmetic conventions was checked in Lean against Mathlib's
  `EReal`, *including* the ones the plan never wrote down (`α·∞ = −∞` and `α·(−∞) = ∞` for `α < 0`,
  `0·(−∞) = 0`, `⊥·⊥ = ⊤`, `inf ∅ = +∞`, `sup ∅ = −∞`). **No case was found where Mathlib's `EReal`
  disagrees with a convention Rockafellar defines.** Separately, `SMul ℝ EReal` genuinely does not
  exist, so `ConvexOn ℝ s (f : E → EReal)` is not even statable — the epigraph definition is forced,
  not merely preferred.
* **The `WithTop ℝ` alternative is not viable as a carrier.** `OrderBot (WithTop ℝ)` does not exist
  and cannot: `ℝ` has no least element, so `sSup ∅` is undefined and `WithTop ℝ` is not a complete
  lattice. Every core definition (`conj`, `ofEpi`, `infConv`, `sSupFn`, `recessionFn`) is a `⨆`/`⨅`
  over an arbitrary family. `EReal = WithBot (WithTop ℝ)` is complete precisely because of the `⊥`.
  `WithTop ℝ` also is not closed under the operations (infimal convolution of proper functions can
  be `−∞`; `clFn` of an improper function is `≡ −∞` by definition), and improper functions are
  load-bearing in §7, §12 and §34. **`E → WithTop ℝ` belongs in the surface only**, as an
  equivalence `{f : E → EReal // ∀ x, f x ≠ ⊥} ≃ (E → WithTop ℝ)` giving exact alignment for the
  book's "a function from `C` to `(−∞,+∞]`" (Theorems 4.1, 4.3, 4.7, 5.1).
* **`dom` must stay unconditional.** `dom f = Prod.fst '' epi f` is now proved in
  `Epigraph.lean` for arbitrary `f`, improper included — so the definition already *is* Rockafellar's
  "projection of the epigraph". Restricting `dom` to functions avoiding `⊥` would make Theorem 7.2
  ("an improper convex function is `−∞` on `ri (dom f)`"), Corollary 7.2.3 and Corollary 29.1.6
  unstatable.
* **D3's Mathlib footing exists.** `LinearMap.dualEmbedding_surjective` (Weak Representation
  Theorem) holds with no separating hypothesis; `LocallyConvexSpace ℝ (WeakBilin B × ℝ)` and
  `IsTopologicalAddGroup (WeakBilin B × ℝ)` are found by `inferInstance`; and
  `geometric_hahn_banach_closed_point` applies there, as Fenchel–Moreau's proof needs.
  `B.flip.flip = B` is `rfl`, so carrying `B` explicitly creates no unification problem.
* **`conj`'s behaviour on improper functions is as claimed** — both proved in Lean with the plan's
  exact definition: `f x₀ = ⊥ → conj B f ≡ ⊤`, and `conj B ⊤ ≡ ⊥`. Record them as lemmas.
* **D6/D7, `infConv := ofEpi (epi f + epi g)` rather than the `⨅` formula, and `Lattice.lean`'s meet
  being `convFn` rather than pointwise `inf`** are all correct calls.
* ~35 sampled book attributions across all eight sub-plans matched the text, and the existing Lean
  code states Theorems 4.1, 4.2, 4.6 and `Proper` faithfully.

## B. Critical — the plan was wrong

### B1. D4's justification is false. `clFn` must branch on `lscHull f`, not on `f`.

The plan claimed a proper convex function has a continuous affine minorant in any locally convex
space, hence `Proper f → Proper (clFn f)` (Rockafellar Theorem 7.4) at layer C. **This is false**, and
both the architecture and the feasibility reviewer produced the same counterexample independently.

Let `g : E →ₗ[ℝ] ℝ` be a *discontinuous* linear functional on an infinite-dimensional space. Its
kernel is dense (`LinearMap.isClosed_or_dense_ker`). Pick `v` with `g v = 1`; for any target
`(x₀, t)`, the points `u + t • v` with `u ∈ ker g` satisfy `g (u + t•v) = t`, so they lie in `epi g`
at height `t`, and `x₀ − t•v` is a limit of such `u`. Hence `closure (epi g) = univ`, so
`lscHull g ≡ ⊥`. But `g` is convex, finite everywhere and proper. Theorem 7.4 is genuinely
finite-dimensional. The plan's proof sketch begged the question: it *assumed*
`(x₀, f x₀ − 1) ∉ closure (epi f)`, which is exactly what fails.

The damage is not confined to §7. With `f := g + δ(·|closedBall 0 1)`, the planned `clFn f` is `⊥`
on the ball, while `conj B f ≡ ⊤` and hence `biconj B f ≡ ⊥`. **Fenchel–Moreau — the keystone —
would be false as planned at layer C.**

**Resolution.**

1. `clFn f := if ∃ x, lscHull f x = ⊥ then (fun _ => ⊥) else lscHull f` — branch on the *hull*.
   This is the standard Γ-regularization and makes `biconj = clFn` unconditionally true. For convex
   `f` in `ℝⁿ` it provably coincides with Rockafellar's definition (by Theorems 7.2/7.4), so surface
   fidelity is unaffected — and proving that coincidence is now a *surface* obligation, recorded in
   `08-surface.md`.
2. The affine-minorant lemma is restated for **closed** proper convex `f`. In that form the plan's
   argument is correct, including the "the separating functional cannot be vertical" step (a
   functional `(y,0)` takes the same value at `(x₀,c)` and `(x₀, f x₀)`, and `x₀ ∈ dom f`).
3. Add the **dichotomy lemma**, which is what replaces Theorem 7.2 outside finite dimensions and was
   absent from the plan: *an lsc convex function taking `⊥` anywhere is `≡ ⊥`.* True in any TVS —
   convexity gives `≡ ⊥` on `[x₀, x₁)` and lsc at `x₁` finishes.
4. `Proper f → Proper (clFn f)` in its unconditional form moves to **layer D**.

D4's *ordering* conclusion (conjugacy before relative interiors) survives — only its justification
and the unconditional Theorem 7.4 do not.

### B2. There is no adjoint for a linear map between paired spaces.

`03-relint-recession.md` §3.6/§3.7 and `05-differential.md` §5.2 write `A.adjoint` / `Aᵀ`. Mathlib's
`LinearMap.adjoint` requires `RCLike`, inner-product spaces and `FiniteDimensional` on both sides. For
`A : E →ₗ[ℝ] G` with `E`, `G` carrying arbitrary pairings there is no adjoint, and one need not
exist — the transpose exists only if `A` is weakly continuous, and then it is extra *data*.

**Resolution.** Carry the pair, in Mathlib's `LinearMap.IsAdjointPair` shape: add
`(A' : H →ₗ[ℝ] F) (hA : ∀ x z, B' (A x) z = B x (A' z))` to `IsExactImage` and to every statement
using `Aᵀ`, with constructors supplying `A'` in the inner-product and finite-dimensional
instantiations. Name it once in `Duality/Pairing.lean`. Also bind `B'` (the pairing on `A`'s
codomain), which the plan uses but never introduces.

### B3. §33–§34: two definitions make their own theorems false.

* **`kernel`** was defined as a *set*, `ri (dom₁ K) ×ˢ ri (dom₂ K)`. The book (line 14887) says the
  kernel is "the **restriction of `K`** to `ri (dom K)`" — a *function*. With the plan's definition
  `K` and `K + 1` share a kernel but are not equivalent, so `saddleEquiv_iff_kernel_eq`
  (Theorem 34.4) is refutable. Fix: `kernel K := (ri (dom₁ K) ×ˢ ri (dom₂ K)).restrict K`, or a
  `Set.EqOn` formulation.
* **`SaddleEquiv`** used *doubled* partial closures. Book line 14641: "`K` and `L` are equivalent if
  **`cl₁K = cl₁L` and `cl₂K = cl₂L`**" — the single ones. Theorem 34.4's proof concludes exactly
  that, so this is not cosmetic.
* **`dom₁` / `dom₂` are never defined anywhere in the plan**, yet `kernel`, `SaddleEquiv`,
  Theorems 34.2–34.5 and §37 are all stated with them. §34 is therefore not actually planned.
* **Theorem 33.3 is misstated**: the book gives a one-to-one correspondence between **lower closed**
  concave-convex functions and closed convex bifunctions (and upper closed ↔ concave). The
  equivalence-class version is Theorem 34.2, which the plan already lists separately.

### B4. D8 needs a product pairing and a written sign table.

D8 promises §29–§30 and §33–§37 are "one operator plus Fenchel–Moreau", but the full conjugate on
`U × X` (`adjointBifun`, Theorem 30.1, Theorem 33.3) needs a pairing on `U × X` built from `Bu` and
`Bx` **with a sign flip on the first factor** — an object the plan never names — and the composition
law `conj (prodPairing Bu Bx) = partialConj₁ ∘ partialConj₂` is never stated, though it is the entire
technical content of D8. Meanwhile `lagrangian` is a partial *concave* conjugate with another sign,
and §33's bracket a third. Four conventions, none written down.

**Resolution.** Before any `Optimization/` code: add `prodPairing`, `negFst`/`negSnd` to
`Duality/Pairing.lean`, prove the composition law, and put a five-row table in D8 fixing, for each of
{bracket, Lagrangian, adjoint, `cl₁`, `cl₂`}, which variable, convex or concave, and the sign.

Related: **`EReal` negation does not distribute over addition** — `-(⊥ + ⊤) = ⊤` but
`(-⊥) + (-⊤) = ⊥`. Mathlib's `EReal.neg_add` carries two hypotheses. So
`lagrangian_eq_neg_partialConj` is not an identity as stated, and neither is any D2 sign-transfer
lemma. Every concave↔convex transfer needs `≠ ⊥` / `≠ ⊤` side conditions — precisely at the improper
functions that §34 and Part VII are about.

## C. Significant

1. **`IsExactSum` has the wrong shape.** `conj B (f+g) ≤ infConv (conj B f) (conj B g)` is *always*
   true, so `conj_add` and `attained` are one fact stated as two. Worse, for proper `f`, `g` with
   disjoint domains `f + g ≡ ⊤`, so `conj B (f+g) ≡ ⊥` while `conj B f y₁ + conj B g y₂ > ⊥` always:
   `attained` is then *unsatisfiable*. And `f + g` is the `Pi` `EReal` sum, which silently evaluates
   `⊤ + ⊥ = ⊥` — a hidden `∞ − ∞` inside the interface. Fix: a single field
   `exact_le : ∀ y, ∃ y₁ y₂, y₁ + y₂ = y ∧ conj B f y₁ + conj B g y₂ ≤ conj B (f + g) y`,
   with `conj_add` derived, and a standing properness hypothesis. Also add the properness the book's
   Theorems 16.3/16.4 carry and the plan dropped from `of_relint`.
2. **`Duality/Exact.lean` creates a real import cycle.** §20's theorems *are* `IsExactSum`
   statements, so `Polyhedral/Duality.lean` must import `Exact.lean` — but the plan gives
   `Exact.lean` an `of_polyhedral` field. Fix: `Exact.lean` holds the interface and its
   interface-only consequences; each `IsExactSum.of_*` lives in the module owning its hypothesis.
3. **§28's Slater theorem belongs in the backbone.** The plan sends Theorem 28.2 to the surface while
   conceding it "is the one with real content". Slater for finitely many convex inequalities is not
   about coordinates. Applications would have to import a `Rockafellar`-namespaced,
   `EuclideanSpace`-specific file to get strong duality — a layering inversion. Move
   "Slater ⇒ `KuhnTucker` nonempty and compact" into `Optimization/Lagrangian.lean`; leave the
   surface the `(m+3)`-tuple packaging and the numbering.
4. **`KuhnTucker` may be defined by Theorem 29.1's conclusion**, which would make
   `kuhnTucker_iff_neg_mem_subgradient` an `Iff.rfl` — the definitional cheat `08-surface.md` §8.4
   forbids. Must be checked against §29's own definition before writing `Perturbation.lean`.
5. **`epi_recessionFn` is not definitional.** `epi (ofEpi S) = S` needs every vertical section of `S`
   closed below; `0⁺(epi f)` is closed only when `epi f` is. Add `ClosedFn f` to that row and to
   every §8 function statement, and make `ofEpi`'s section-closedness a named lemma in
   `Operations/Epi.lean` — `lscHull`, `infConv`, `mapLin`, `convFn`, `smulRight` all consume it.
6. **Theorem 30.2's conjugate is the *concave* one.** Book line 12487: `F*0` is the conjugate of the
   **concave** function `−inf F`. The plan writes the convex conjugate of `inf F`. This is exactly
   what D2 warns about.
7. **Stage ordering.** `Duality/Support.lean` (stage 5) needs `Recession/Function.lean` (stage 6).
   Move the recession *definitions* and their layer-A/B facts to stage 3–4; leave only §9
   (`Closedness.lean`) in stage 6.
8. **Theorem 9.1's prerequisites are unnamed**: `recessionCone (S ∩ T) = recessionCone S ∩ recessionCone T`
   for nonempty closed convex `S`, `T` (Cor 8.3.3); `recessionCone (A ⁻¹' closedBall) = ker A`; the
   `L ⊆ linealitySpace (cl C)` translation lemma; and Mathlib's nested-compacts lemma
   (`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`) is indexed by a *type*, so
   the proof must be reorganised around `t n = C_{1/(n+1)}`.
9. **Minkowski–Weyl's route conflates two proofs.** Double polarity gives `K = K°°` only for *closed*
   cones, so "finitely generated ⇒ polyhedral" needs the prior theorem **"a finitely generated cone
   is closed"** — the actual hard content, which the plan never mentions. Fourier–Motzkin is a
   separate, projection-based proof of the other direction. Homogenisation also needs `C ≠ ∅`.

## D. Survey corrections (things claimed about Mathlib that are wrong)

| plan claim | truth |
|---|---|
| `EReal.sub_le_iff_le_add` missing | exists, `Data/EReal/Operations.lean:458`, with weaker disjunctive hypotheses. Also `le_sub_iff_add_le`, `sub_le_of_le_add`. Defining our own would shadow Mathlib's inside `namespace Tdaf` |
| `EReal.coe_smul` missing | is `EReal.coe_mul`, `Data/EReal/Basic.lean:147` |
| `egauge` absent | **`Mathlib/Analysis/Convex/EGauge.lean` already defines `egauge`** as an `ℝ≥0∞`-valued Minkowski gauge. Rename ours to `Tdaf.gaugeFn`, or reuse Mathlib's — Rockafellar's gauge is nonnegative, so `ℝ≥0∞` loses nothing |
| "Mathlib has *no* minimax theorem" (`07`) | **false** — `Mathlib/Topology/Sion.lean` has Sion–von Neumann including a saddle-point form. Reuse it for Corollary 37.6.2; it removes the "genuinely new" justification for prioritising §36/§37 |
| `IsCompact.convexHull` (`04` §4.1) | does not exist. Mathlib has `Set.Finite.isCompact_convexHull` (finite sets). The compact case of Theorem 17.2 is *not* already available |
| `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`, `inner_mul_le_norm_mul_norm`, `Real.inner_le_nnorm_mul_nnorm` (`08` §8.3) | none exist. Cauchy–Schwarz is `norm_inner_le_norm`. The `MeanInequalities`/Young reference is real |
| `lowerSemicontinuous_iff_isClosed_epi` "wraps Mathlib" | Mathlib's version puts the epigraph in `E × EReal`; ours is in `E × ℝ`. It is a ~10-line proof, not a wrap |
| `add_iSup` / `iSup_add` / `iSup_sub` / `mul_le_mul_left` for `EReal` | genuinely absent from all of Mathlib. These are the workhorses of every conjugacy proof (`conj` is a `⨆` of `· − f x`). **`Order/EReal.lean` is a file, not five lemmas** |
| `Compatible τ B` / Mackey–Arens | nothing in Mathlib. `Convex.closure_eq_of_compatible` must be built from `iInter_halfSpaces_eq` plus a definition of `Compatible`. **An unbudgeted file on D3's critical path** |
| `cone : Set E → Set E` | does not exist. `ConvexCone.hull ℝ s` is the *wrong* object (not pointed — need not contain `0`). Use `PointedCone.span ℝ s`, or define `Tdaf.cone` |
| "448 numbered results" | ≈461: 235 theorems, **217** corollaries, 9 lemmas. The corollary count was 7% low and propagates into the sizing table |

## E. Lean statements in the plan that do not elaborate

| where | error | fix |
|---|---|---|
| `clFn` (`02` §2.1) | `failed to synthesize Decidable (∃ x, f x = ⊥)` | `open Classical in`. The `⨅ _ : p, f` trick does **not** apply — the default value is a function |
| `Polyhedral` (`04` §4.3) | `→ₗ[ℝ]` binds looser than `×`, so `p.2` is `map_smul'` | `Finset ((E →ₗ[ℝ] ℝ) × ℝ)` |
| `FinitelyGenerated` (`04` §4.3) | `Unknown identifier cone` | `PointedCone.span ℝ ↑D` |
| `pairing` (`08` §8.2) | `innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ` — `innerₗ` takes the *space* | `innerₗ (Rn n)`. Every surface file is stated against this |
| `IsExactSum.of_polyhedral` (`03` §3.6) | applies the set-level `Polyhedral` to a function | `PolyhedralFn f` (named in `04`'s table, never defined) |
| `LegendreType` (`05` §5.5) | `extends` parents must be applied | `extends EssentiallySmooth f, EssentiallyStrictlyConvex f` |
| `ofEpi`, `mapLin` in `01`'s operations *table* | anonymous-subtype binders are not `⨅` syntax | the `⨅ μ ∈ {μ : ℝ | …}` form in the code block is the one that elaborates |

Everything else transcribed — `ofEpi`, `infConv`, `smulRight`, `hom`, `PosHomogeneous`, `hypo`,
`ConcaveFn`, `lscHull`, `conj`, `biconj`, `supportFn`, `polarCone`, `polarSet`, `dirDeriv`,
`subgradient`, `normalCone`, `recessionCone`, `recessionFn`, `Bifun`, `infBifun`, `KuhnTucker`,
`lagrangian`, `adjointBifun`, `ineqBifun`, `partialConj₂`, `ConcaveConvexFn`, `SaddleFn`,
`IsSaddlePoint`, `HasSaddleValue`, `ConvexProcess`, `IsExactSum`, `Convex.closure_image_eq`,
`notation "ri"`, `closure[τ]` — **elaborates as written**.

## F. Ergonomics warnings for whoever writes these files

1. **`open Pointwise` is mandatory and unmentioned in the plan.** `infConv`, `smulRight`,
   `linealitySpace`, `gaugeFn`, `posHomogeneous_iff_isCone_epi` and `ConvexProcess` all use pointwise
   set algebra and fail instance synthesis without it.
2. **`WeakBilin B` is a type synonym; `simp`/`rw` do not fire through it.** Pair literals, `ext` and
   `Prod.mk_add_mk` in `WeakBilin B × ℝ` need manual ascription
   (`failed to synthesize HAdd (E × ℝ) (WeakBilin B × ℝ) ?m`). Since D3 makes "prove it in
   `WeakBilin B`, transport out" the central strategy, budget a small `WeakBilin`-transport simp set
   before §2.4.
3. **Mathlib does not give you the dual of `WeakBilin B × ℝ`.** Decomposing
   `g (x,μ) = B x y + c·μ` must be hand-written: restrict along `ContinuousLinearMap.inl`, apply
   `LinearMap.dualEmbedding_surjective`, take `c = g (0,1)`.
4. **`dirDeriv` is only meaningful on `dom f`.** `EReal` has `Div` (`Mathlib.Data.EReal.Inv`, so
   `Order/EReal.lean` must import it), but `⊤ − ⊤ = ⊥`, so off `dom f` the definition returns `⊥`
   for every direction and the advertised `f'(x;0) = 0` fails. Theorem 23.1's hypothesis is "`x` a
   point where `f` is finite" — keep it.
5. **`lscHull f := ofEpi (closure (epi f))` is used as if `epi (lscHull f) = closure (epi f)`.** That
   needs "for closed `S ⊆ E × ℝ`, the vertical infimum is attained when finite" — see C5.

## G. Still open

* Whether Rockafellar ever *uses* an `∞ − ∞` convention locally in §16/§30 (some treatments adopt
  `∞ − ∞ = ∞` there). `EReal` picks `⊥`. Decides whether B4's side conditions are cosmetic or
  load-bearing.
* Whether `IsExactSum.of_continuousAt` is as cheap in a bare TVS as claimed — a 30-line spike would
  settle it and stress-test the corrected `IsExactSum`.
* Whether `Mathlib/Analysis/Convex/Approximation.lean` and `Mathlib/Topology/Sion.lean` overlap §10
  and §35–§36 beyond the minimax theorem itself.
* Whether Theorem 8.3 needs local compactness or only closedness (plan says layer D; may be
  over-conservative).
* Whether `convexFn_ofEpi` (Theorem 5.3) is provable as stated — true, but the ε-argument it needs
  (the vertical infimum need not be attained) is unsketched.
