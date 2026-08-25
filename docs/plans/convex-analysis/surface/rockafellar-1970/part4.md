# Part IV — Representation and Inequalities (§17–§22)

`Tdaf/Surface/Rockafellar/Part4.lean` → `Part4/Section17.lean` … `Section22.lean`.

**70 numbered results: 7 G, 63 C.** The most coordinate-bound Part, and the one with the most
genuinely new surface work.

| § | module | results | G/C | thickness | backbone |
|---|---|---|---|---|---|
| 17 | `Section17.lean` | 10 | 0/10 | **thick** | `Caratheodory.lean`, `HullDirections.lean` |
| 18 | `Section18.lean` | 16 | 5/11 | medium | `Face.lean`, `Representation.lean`, `Exposed.lean`, `Tangent.lean` |
| 19 | `Section19.lean` | 17 | 0/17 | **thick** | `Polyhedral/*` |
| 20 | `Section20.lean` | 8 | 0/8 | **thick** | `Polyhedral/{Ops,Separation,Closedness}.lean` |
| 21 | `Section21.lean` | 10 | 2/8 | medium | `Helly.lean`, `HellyRefined.lean` |
| 22 | `Section22.lean` | 9 | 0/9 | **mostly deferred** | `LinearInequalities.lean` (Farkas only) |

## Stated and refuted

**Corollaries 17.1.4 and 17.1.6 are false as Rockafellar states them.** The surface states them and
transcribes the counterexample — on `ℝ¹` take `f₁ y = −y`, `f₂ y = y`; then `conv {f₁, f₂} ≡ −∞`, so
the positively homogeneous function generated is `−∞` everywhere, while at `x = 1` every admissible
representation uses a single index and gives `−1` or `1`. (Root cause: an *affine* dependency has
coefficients summing to zero, so both signs occur; a *conical* dependency can have every coefficient
of one sign, and then the book's "minimal `α′` on the vertical line" does not exist.) Recorded in
`api.md`'s `Caratheodory.lean` record. This is the third category of the alignment checklist —
neither proved nor silently omitted.

## Deferred by scope

**§22's elementary-vector development** — Lemmas 22.4, 22.5, Cor 22.4.1, Thms 22.6, 22.7 (Tucker's
complementarity theorem). A substantial body of combinatorial matroid theory, not convex analysis.
Farkas' Lemma (`Corollary 22.3.1`) and Thms 22.1–22.3 are **in scope** and specialise
`LinearInequalities.lean`.

Earlier plan drafts disagreed about §22 — the root plan excluded it, the surface plan said it "lives
here in full". Both were right about different questions: it *belongs* here, and it is *deferred*.
Placement is not scheduling.

## Hazards

* **Mixed point/direction sets** — `conv S`, `aff S`, `dim S`, "generalized simplex", "vertices at
  infinity" — run through §§17–19. `S` is a *pair* (points, directions), not a subset of `ℝⁿ`. Model
  as a subset of the homogenisation cone `{(λ,x) | λ ∈ {0,1}}`.
* **Thm 18.5** is stated only for sets containing no lines; the "obvious extension to closed convex
  sets of arbitrary lineality" (6603) is never stated or proved, and a surface will want it.
* **Thm 19.6 and Cor 18.7.1 have no `Proof.` paragraph.** Thm 19.1's proof is four implications each
  sketched in a paragraph, one of which says only "It suffices to treat the case where…".
* **Thm 20.5** — every polyhedral convex set is locally simplicial — is the missing link that makes
  Thm 10.2 applicable, and its proof (7243–7249) is a two-line sketch *asserting* the triangulation
  of a polyhedron near a point. This is real work, and §10 depends on it.
* **Thm 20.1**'s asymmetry — the polyhedral members need only `dom` to meet, the others need
  `ri dom` — is the subtlest constraint qualification in Parts I–IV, and is the whole point of §20.
* **The `λ = 0⁺` convention returns** in Thms 19.5.1, 19.6, 19.7. Reuse the §9 treatment.
* **The book cites a nonexistent "Corollary 21.3.3"** in its own Comments (17309); the text has
  21.3.2. Thm 21.1's hypothesis is `dom fᵢ ⊇ ri C` (not `⊇ C`) and is deliberate; the `0·∞ = 0`
  convention is load-bearing in its alternative (b).
* `Σ ζ*ⱼ Iⱼ > 0` in Thm 22.6 is a **set containment** (`⊆ (0,∞)`), stated once in a parenthesis at
  8067, 120 lines before the theorem. "Real interval" is left loose at 8033, and the
  elementary-vector definition at 8119 is OCR-truncated — verify against a clean copy.
* The graph-theoretic material at 8121–8153 (circulations, tensions, cocircuits) is motivation only
  and is used in no proof; omit it.
* Mixed-case labels: `Corollary 17.1.3`, `22.3.1`.
