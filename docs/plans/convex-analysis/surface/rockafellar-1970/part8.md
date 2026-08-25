# Part VIII — Convex Algebra (§38–§39)

`Tdaf/Surface/Rockafellar/Part8.lean` → `Part8/Section38.lean`, `Part8/Section39.lean`.

**21 numbered results, and every one of them is G.** No clause rows. This is the only Part with a
clean sweep, which makes it the natural first target for any future non-`ℝⁿ` surface (§10 of the
[overview](../../00-overview.md)) and the thinnest Part to port here.

| § | module | results | G/C | backbone it specialises |
|---|---|---|---|---|
| 38 | `Section38.lean` | 12 | 12/0 | `Bifunction/{Algebra,Cofinite}.lean` |
| 39 | `Section39.lean` | 9 | 9/0 | `Bifunction/{Process,ProcessDuality}.lean` |

Both files are thin: statement, `ℝⁿ` instantiation, one-line proof by application. Budget the effort
in the *gates* below, not in the sections.

## Gated on [remediation](../../backbone/08-remediation.md)

* **§2.2 — de-leak `reflect`'s mirror statements.** Part VIII specialises `Bifunction/Process.lean`,
  where eight statements mention the involution in their own hypotheses. A surface theorem
  numbered `theorem_39_2` must read like the book's Theorem 39.2 and not like a transport lemma, so
  the leak has to be plugged before `Section39.lean`, not after.
* **§4.1 bundled adjoint.** §38's `F*` and §39's `A*` are the densest adjoint users in the book —
  every one of the 21 results touches one. Carrying `A*` as a loose argument plus an
  `IsAdjointPair` hypothesis would double the length of both files.
* **§4.4 `m`-ary `infConv`.** `F₁ □ ⋯ □ F_m` appears in the associativity discussion (16239) and in
  the co-finite remark; the binary form forces an induction the book does not do.

## §38 — the algebra

Defines `F₁ □ F₂`, `Fλ`, `Ff`, `GF`, `⟨f, g⟩`, and *co-finite*.

* **`⟨f, g⟩` is a partial operation** (16527). It is defined only when the `∞ − ∞` collision does
  not occur, and the book simply says so in prose. Do not model it as a total function returning a
  junk value on the bad inputs: state the results with the definedness side condition explicit, so
  a reader can see where the book's fluency is hiding a hypothesis. The same applies to the
  commutativity and associativity claims for `□` and for bifunction multiplication, which hold only
  "to the extent that they are defined" (16239, 16507) — improper bifunctions break both.
* **Theorem 38.1 carries an orientation-dependent `∞ − ∞` convention**: `−∞` for convex
  bifunctions, `+∞` for concave. This is the fourth overloading of `⟨·,·⟩` in the book (the first
  three are in §33) and the fourth distinct `∞ − ∞` rule. Name the two conventions separately in the
  surface; do not let a single notation carry both.
* **Co-finiteness is the class where every `ri` hypothesis evaporates.** A closed convex `F` is
  co-finite iff `dom F = ℝᵐ` *and* `dom F* = ℝⁿ` (16701). The three facts in the closing discussion
  (16693–16729) are stated without proof labels but are used; the backbone has them in
  `Bifunction/Cofinite.lean` and the surface should number them as the book's running text does not.
* Mixed-case labels: `Theorem 38.1`, `Corollary 38.7.2`.

## §39 — convex processes

Defines convex process (graph = a convex cone containing `0`), `dom A`, `range A`, `A⁻¹`,
polyhedral convex process, `cl A`, `λA`, `A + B`, `AC`, `Af`, `BA`, the sup/inf **orientation**, the
indicator bifunction of an oriented process, the adjoint `A*`, and `⟨C, D⟩`, `⟨C, h⟩`, `⟨h, D⟩`.

* **Orientation is data, not a convention.** Theorems 39.5 and 39.8 require the two processes to
  carry the *same* orientation, and Theorem 39.2 **flips** it. Both orientations must therefore be
  simultaneously expressible: a global convention — of the kind §36 imposes for saddle-functions —
  cannot even state Theorem 39.5. Rockafellar makes the orientation a formal *pair* (16945–16965);
  the surface must do the same. This is the one place in the book where the orientation apparatus
  is unavoidable rather than merely convenient, and it is why the backbone carries it as a field.
* **Theorem 39.1 is restated with `A0 = {0}`.** The book's hypothesis is that `A0` is *bounded*, but
  boundedness is used only to force `A0 = {0}` (a convex cone that is bounded is trivial). Stating
  it the intended way is strictly more general and drops a finite-dimensional dependency. Record the
  divergence in the docstring, as with Cor 32.3.3 in [Part VI](part6.md).
* `A⁻¹A ≠ id` (16929): convex processes form a non-commutative semigroup under composition, and a
  complete lattice under inclusion (16943). Both are one-line surface facts worth stating, since the
  lattice structure is what [D12](../../00-overview.md#d12-order-theoretic-duality-is-mathlibs-and-it-is-load-bearing) says to get from Mathlib rather than
  rebuild.
* Theorem 39.3 is the four-part correspondence between a process, its indicator bifunction, and the
  two brackets; Theorem 39.4 turns it into a characterisation. These are the two results whose
  surface statements will be longest, because the book states them as a chain of equalities across
  a page.

## Do not mine the closing material

Lines 17199–17268 sketch a research programme — an algebra of oriented processes, a proposed duality
for multivalued maps — entirely without proof. It is the end of the book, not a section of results.
Nothing there is a numbered result and nothing there should become a surface declaration.
