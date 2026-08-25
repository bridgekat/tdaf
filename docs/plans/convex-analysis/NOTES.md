# Working notes

Central record for anyone — human or agent — writing modules for the convex-analysis project. It
exists so that the same obstacle is not rediscovered twice.

**Read this file. Grep the other two.**

| file | what it is | size |
|---|---|---|
| `NOTES.md` (this) | house style, the verification bar, how to find things | short, read it |
| [`gotchas.md`](gotchas.md) | Lean and Mathlib traps, grouped by cause | read §EL before writing proofs; grep the rest |
| [`api.md`](api.md) | one record per backbone module: what is in it, and what is deliberately not | reference only — never read end to end |

The plans themselves are elsewhere: [`00-overview.md`](00-overview.md) for the design decisions
(D0–D12) and the corrections to Rockafellar, [`backbone/`](backbone/) for the sub-plans and the
remediation list, [`surface/`](surface/) for the textbook-aligned layer.

---

## House style

From the repository `README.md` ("Reviewing a formalization"):

* **Minimize duplication.** Before writing a lemma, check whether Mathlib or this project already
  has it. This is the single most-violated rule here — see `gotchas.md` LIB1, which records seven
  times it has been violated and what each one cost.
* **Bundle *concepts*, not individual assumptions.** `Proper`, `ConvexFn`, `ClosedProperConvexFn`,
  `IsExactSum` are named mathematical concepts and are structures. A single side condition such as
  `∀ x, f x ≠ ⊥` is not a concept — repeat it inline rather than inventing a name for it. A
  *conjunction* of concepts qualifies when the book names it: "closed proper convex function" is
  Rockafellar's most repeated phrase and is `ClosedProperConvexFn`. Two of the three is not — leave
  `(hf : ConvexFn f) (hc : IsClosed (epi f))` inline.
* **A name must not resolve to the wrong statement.** The worst outcome is a name a reader will
  guess that exists and means something else. `epi_anti` is antitone, so it may not be `epi_mono`;
  `PosHomogeneous.map_zero_trichotomy` is `f 0 ∈ {0, ⊤, ⊥}` rather than Mathlib's universal
  `f 0 = 0`, so it may not be `map_zero` (the conditional equality is `map_zero_eq_zero`). Leaving
  the guessable name *unbound* is better than binding it to a near-miss.
* **Instantiate the Mathlib interfaces that emerge implicitly.** If a definition turns out to be a
  Galois connection, a closure operator, a cone, a module, a lattice — say so, eagerly, and get the
  machinery and the lemma names for free instead of hand-rolling them. `gc_ofEpi_epi` /
  `gi_ofEpi_epi` / `epiClosure` (`Operations/Epi.lean`) turn `subset_epi_iff_le_ofEpi` into a
  `GaloisInsertion` and identify `IsEpiLike` with closure-operator closedness;
  `PosHomogeneous.epiCone` (`Homogeneous.lean`) bundles the epigraph of a positively homogeneous
  convex function as a `ConvexCone ℝ (E × ℝ)`, which §13 and §14 want. But *recording* an interface
  is not *using* it — see `gotchas.md` LIB5.
* Code should be idiomatic and pleasant to read, not merely correct. Prefer several short lemmas to
  one long proof: if a proof runs past a few lines, that is usually a signal to change what it is
  built on, not to write a longer proof.
* **Nothing in the backbone may depend on Rockafellar** (design decision D10 in `00-overview.md`).
  Names are mathematical, never bibliographic; statements are the natural general ones rather than
  the book's packaging; a module docstring leads with what the module is *about* and puts
  "Rockafellar §35" in its `## References` section. Per-declaration doc comments should still cite
  "**Rockafellar, Theorem 23.4**" — that is a citation, not a dependency — but the statement has to
  read as mathematics without it. A theorem worth having in the book's own packaging is a
  *surface* theorem, proved by specializing backbone lemmas.

### Writing a module docstring

Lead with the subject, then the main results, then the design decisions a reader would otherwise
have to reverse-engineer, then **what is not here and why**.

That last section is the one that rots. Two sweeps have found "not here" notes outliving the
obstruction they described — three of the four in the second sweep named a *reason* that was wrong
rather than merely a stale location, and each was pointing work away from a result that already
existed. An explanation is the part a later agent believes and does not re-derive. Re-check them
after every merge.

---

## Build and verification

From the repository (or worktree) root:

```
lake build Tdaf.Analysis.Convex.<Module>     # builds one module and its dependencies
lake build                                   # builds everything reachable from Tdaf.lean
```

A module does **not** need to be listed in `Tdaf.lean` to be built by name — but it must be listed
before it counts as done, in the single flat list ordered by full module path
(`grep "^import " Tdaf.lean | LC_ALL=C sort -c`).

**The bar, before declaring a module done:**

- `lake build` completes with **no errors and no warnings** — deprecation warnings included;
- `grep -rn "sorry" <file>` finds nothing, and there is no `axiom`;
- `#print axioms` on every main declaration reports exactly
  `[propext, Classical.choice, Quot.sound]`.

Two things make this bar harder than it looks, both in `gotchas.md` §BLD: `lake` keys on content
hashes, so `touch` does **not** make the linters re-run (BLD1), and a build tree can be silently
stale while `lake` reports success (BLD2). To be sure the linters ran, delete the module's `.olean`
and rebuild. And `#print axioms` output wraps, so a naive `grep` of it under-counts (BLD8).
