# Sub-plan 8 — The Rockafellar surface library

The surface library states all 448 numbered results of *Convex Analysis* in `ℝⁿ`, in the book's own
numbering and notation, and proves each by specialising the backbone.

Per the repository README, the surface is the integration test: it is what tells us whether the
backbone's generality was chosen correctly. If a surface proof is longer than a few lines, that is a
signal to change the backbone, not to write a longer surface proof.

---

## 8.1 Layout

```
Tdaf/Surface/Rockafellar/
  Notation.lean          -- δ(·|C), δ*(·|C), γ(·|C), f0⁺, fλ, □, #, K°, C°, ⟨f,g⟩
  Setup.lean             -- the ambient ℝⁿ: EuclideanSpace ℝ (Fin n), the inner-product pairing
  Part1/Section01.lean … Section05.lean
  Part2/Section06.lean … Section10.lean
  Part3/Section11.lean … Section16.lean
  Part4/Section17.lean … Section22.lean
  Part5/Section23.lean … Section26.lean
  Part6/Section27.lean … Section32.lean
  Part7/Section33.lean … Section37.lean
  Part8/Section38.lean … Section39.lean
```

Namespace `Rockafellar`; names `theorem_4_2`, `corollary_16_4_1`, `lemma_22_4`. Every declaration
carries a docstring quoting the book's statement verbatim, so that semantic alignment can be checked
by reading the file alone.

## 8.2 The ambient setting

```lean
namespace Rockafellar
open Tdaf.ConvexAnalysis
variable {n : ℕ}
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Rockafellar's pairing: the standard inner product on `ℝⁿ`, as a bilinear map.
Note `innerₗ` takes the *space*, not the field: `innerₗ ℝ` elaborates to `ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ`. -/
noncomputable def pairing (n : ℕ) : Rn n →ₗ[ℝ] Rn n →ₗ[ℝ] ℝ := innerₗ (Rn n)
```

Everything is then `conj (pairing n)`, `subgradient (pairing n)`, etc. Because `Rn n` is a
finite-dimensional real inner-product space, all four layers of
[D9](00-overview.md#d9-generality-boundaries) are available simultaneously, which is exactly why the
book can state everything without qualification.

The surface also owns two *bridging obligations* that the backbone's generality creates:

1. **`clFn` agrees with the book.** The backbone defines `clFn` by branching on whether `lscHull f`
   takes `⊥` (necessary in infinite dimensions — see [D4](00-overview.md#d4)); Rockafellar branches
   on whether `f` does. Prove they coincide for convex `f` on `ℝⁿ`, via Theorems 7.2 and 7.4.
2. **`(-∞, +∞]`-valued functions.** Rockafellar repeatedly writes "a function from `C` to
   `(-∞,+∞]`" (Theorems 4.1, 4.3, 4.7, 5.1). Supply
   `{f : E → EReal // ∀ x, f x ≠ ⊥} ≃ (E → WithTop ℝ)` so those statements can be given in the
   book's own terms. This is the *only* place `WithTop ℝ` should appear: it is not a complete
   lattice (no `OrderBot`, since `ℝ` has no least element), so it cannot carry the `⨆`/`⨅` that
   `conj`, `ofEpi` and `infConv` are defined by, and it is not closed under the operations.

A design point worth stating: Rockafellar identifies `ℝⁿ` with its dual throughout, writing `x*` for
a vector in the same space. The surface honours this by taking `F = E` and `B = ⟨·,·⟩`. The `*`
decoration becomes a naming convention, not a type distinction — which is faithful, and which is
also why the backbone must keep the two spaces distinct so that the general theory does not silently
depend on self-duality.

## 8.3 Sections needing genuine surface work

Most sections should be near-mechanical. These are not:

- **§1 (Affine sets).** Almost entirely Mathlib (`AffineSubspace`, `affineSpan`,
  `AffineMap`, `AffineIndependent`, `Submodule.orthogonal`). New: barycentric coordinate systems as a
  named construction, and **Tucker representations** (Theorem 1.4's solved form and the
  correspondence between Tucker representations of `L` and of `L^⊥`). Tucker representations are
  used only in §22 and Corollary 31.4.2; they are coordinate bookkeeping and belong here, not in the
  backbone.
- **§4–§5 examples.** The concrete conjugate pairs and convex functions (`eˣ`, `|x|ᵖ/p`,
  `−log`, `−(a²−x²)^{1/2}`, the geometric mean, log-sum-exp, the Tchebycheff norm). Genuine work,
  genuine value: they are the tests that the definitions compute. Mathlib supplies the analytic
  facts (`norm_inner_le_norm` for Cauchy–Schwarz, and `Analysis/MeanInequalities.lean` for Young's
  inequality; note that `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`,
  `inner_mul_le_norm_mul_norm` and `Real.inner_le_nnorm_mul_nnorm` do **not** exist).
- **§4 Theorems 4.4, 4.5** (second-derivative and Hessian criteria). Mathlib has the one-dimensional
  version in `Analysis/Convex/Deriv.lean`; the `ℝⁿ` version follows by restricting to lines, which
  needs a small lemma `convexOn_iff_convexOn_lines`.
- **§22.** The elementary-vector development is self-contained linear algebra with no backbone
  counterpart; it lives here in full, including Tucker's complementarity theorem (Theorem 22.7).
- **§28.** Ordinary convex programs as `(C, f₀, …, f_m, r)`. The surface defines the structure,
  builds the associated bifunction (`ineqBifun`), and derives Theorems 28.1–28.4 and the
  Kuhn–Tucker theorem from §29–§30. This is the thickest surface file and the most important one:
  it is where the abstract perturbation theory becomes recognisable Lagrange multipliers.
- **§30–§31 examples.** Linear programming duality, quadratic programming, the geometric-programming
  example at the end of §30, and the Fenchel duality examples of §31. High value as tests.

## 8.4 Semantic-alignment checklist

For each section, confirm before marking it done:

1. Every numbered result of the section has a declaration, or is explicitly listed as omitted with a
   reason (Rockafellar states a handful of results as exercises; those are recorded as `-- exercise`
   comments, not silently dropped).
2. The statement quantifies over the same objects as the book. In particular, Rockafellar's "convex
   function" always means *extended-real-valued, defined on all of `ℝⁿ`* — a surface statement about
   `f : ℝⁿ → ℝ` is a mistranslation unless the book says "finite".
3. Improperness is not silently excluded. Rockafellar admits improper convex functions and several
   theorems (7.2, 12.2, 34.2.3) are specifically about them.
4. No `axiom`, no `sorry`, no definitional cheat: in particular the surface must not *define* a
   notion so as to make a theorem true by unfolding. Where a surface definition is introduced for
   alignment, it comes with an equivalence proof to the backbone notion.
5. `#print axioms` on each section's main results shows only the standard three.

## 8.5 Suggested surface order

Follow the backbone stages, not the book order:

1. §4, §5 (after backbone stage 2) — the first alignment check, and the one most likely to expose a
   wrong definition.
2. §11, §12, §13 (after stage 5) — conjugacy is where the pairing decision is tested.
3. §2, §3, §1 — mostly Mathlib re-exports; cheap, and they make the earlier files readable.
4. §6, §7, §8, §9, §10 (after stage 6).
5. §16, §23 (after stage 7/8) — the dual-operations table and subdifferential calculus.
6. §17–§22 (after stage 9).
7. §27–§32 (after stage 10), with §28 last within this group.
8. §33–§39 (after stage 11).
