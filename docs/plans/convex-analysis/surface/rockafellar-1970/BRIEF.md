# Brief — formalizing a section of the Rockafellar surface

You are writing one **section module** of the surface library for R. T. Rockafellar,
*Convex Analysis* (Princeton, 1970), in Lean 4 / Mathlib `v4.34.0-rc1`.

Read this whole file before writing any Lean.

## What a surface module is

The backbone (`Tdaf/Analysis/Convex/`, 112 modules, ~3 200 theorems) already contains the
mathematics, stated in its natural generality with descriptive names. Your job is **not** to prove
things. Your job is to state each numbered result of your section *in the book's own terms* and
close it by applying the backbone.

> **If a surface proof runs past a few lines, that is a signal to change the backbone, not to write
> a longer surface proof.** Stop, record it, and move on — see "When the backbone does not fit".

The surface is the integration test. It is what tells us whether the backbone's generality was
chosen correctly.

## Where things go

```
Tdaf/Surface/Common/Euclidean.lean      -- the ambient setting; import this
Tdaf/Surface/Rockafellar/PartN/SectionMM.lean
```

Your module begins:

```lean
import Tdaf.Surface.Common.Euclidean
-- plus any earlier section modules whose definitions you need

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface
```

`Tdaf.Surface.Common.Euclidean` gives you `Rn n := EuclideanSpace ℝ (Fin n)` and
`pairing n : Rn n →ₗ[ℝ] Rn n →ₗ[ℝ] ℝ`, the inner product read as a bilinear map. Every backbone
duality notion is then `conj (pairing n)`, `subgradient (pairing n)`, `polarCone (pairing n)`, and
so on. **All 31 typeclass instances a surface needs are already discharged there** — if instance
search fails on something that file asserts, that is a bug worth reporting, not something to work
around locally.

Register your module in `Tdaf.lean`, alphabetically.

## Naming

Namespace `Rockafellar`, **flat**. Names are the book's numbering, verbatim:

```
theorem_2_1     corollary_2_6_3     lemma_22_4     theorem_30_4_g
```

Multi-clause theorems get **one declaration per clause**, with a letter suffix matching the book's
`(a)`, `(b)`, … — their clauses genuinely differ in hypotheses and in which backbone layer they come
from. Do not bundle them into a conjunction.

This is the one place in the repository where bibliographic names are correct. The backbone forbids
them precisely so they are unambiguous here.

## Docstrings

Every declaration carries a docstring that **quotes or closely paraphrases the book's statement**,
so alignment can be checked by reading the surface file alone. Follow this shape:

```lean
/-- **Rockafellar, Theorem 2.6.** A subset of `ℝⁿ` is a convex cone if and only if it is closed
under addition and positive scalar multiplication.

Specialises `convex_iff_add_mem_of_isCone`. -/
```

Say which backbone declaration you specialised. If the book's proof is defective or absent, say so
here — fourteen results in the book are printed with no proof at all and three printed arguments are
wrong; your section plan lists the ones in your range.

## Surface definitions

You may introduce a definition for alignment when the book's notion has no backbone counterpart in
the book's exact shape — Rockafellar's *cone* (closed under **positive** scaling; the origin may or
may not belong) is the standard example, since Mathlib's `PointedCone` contains `0` by definition.

When you do, **you must immediately prove its equivalence to the backbone notion**, and state every
subsequent result through the equivalence rather than re-deriving anything. A surface definition
with no bridge lemma is a definitional cheat and will be rejected in review.

Never define a notion so as to make a theorem true by unfolding.

## Alignment checklist — verify before you report done

1. Every numbered result in your range has a declaration, **or** is placed in exactly one of three
   explicit categories, recorded in the module docstring under `## What is not here`:
   **omitted with a reason**, **deferred by scope**, or **stated and refuted**. The third is real:
   Corollaries 17.1.4 and 17.1.6 are *false as Rockafellar states them*, and the surface transcribes
   the counterexample rather than dropping them silently.
2. The statement quantifies over the same objects as the book. Rockafellar's "convex function"
   always means extended-real-valued (`Rn n → EReal`) and defined on **all** of `ℝⁿ`. A statement
   about `f : Rn n → ℝ` is a mistranslation unless the book says *finite*.
3. Improperness is not silently excluded. Several theorems (7.2, 12.2, 34.2.3) are specifically
   about improper functions. Do not add `Proper` to a hypothesis list that the book does not have.
4. No `axiom`, no `sorry`.
5. `#print axioms` on your section's main results shows exactly
   `[propext, Classical.choice, Quot.sound]`.
6. The section's own numbering is contiguous: if the book has 2.1, 2.1.1, 2.2, …, so do you.

## When the backbone does not fit

This will happen, and it is the most valuable thing you will find. Three cases:

* **The backbone result exists but is awkward to apply** (unbundled hypotheses that a bundled type
  would carry, a binary operation where the book states an `m`-ary one, an explicit adjoint argument
  where the book writes `A*`). Write the surface statement anyway, close it however you can, and
  record the friction.
* **The backbone result does not exist.** Do *not* prove it in the surface. State it with the
  proof you would need, record it as a backbone gap, and move on.
* **The book's result is false, or its proof is.** Record it, state the corrected version, and say
  so in the docstring.

Report all three in your final report under a heading `## Backbone gaps and friction`, one line
each, with the surface declaration that hit it. These become remediation items.

## Process

* Work in **your own worktree**, never in the primary checkout. You will be told its path.
* `lake build <your module>` must be clean: **no errors and no warnings**, including the line-length
  and style linters.
* Use the Lean LSP over MCP where it helps (`lean_goal`, `lean_hover_info`, `lean_local_search`,
  `lean_multi_attempt`). `lean_local_search` before guessing a lemma name; `lean_leansearch` and
  `lean_loogle` for Mathlib.
* Grep the backbone before writing anything. Nearly every result you need is there under a
  descriptive name; `docs/plans/convex-analysis/NOTES.md` has a per-module record of what is in each
  file, and `Tdaf/Analysis/Convex/Eponyms.lean` maps the famous names.
* **Read `NOTES.md` §2 (gotchas) before starting.** 355 entries of things that have already cost
  someone an hour.

## Your inputs

* The book text: `D:\Users\bridgecat\Documents\Projects\tdaf-convex-analysis\convex-analysis.md`,
  with the line range for your section given in your task.
* Your section's entry in `docs/plans/convex-analysis/surface/rockafellar-1970/inventory.md` — every
  label, its line, a one-line statement, and a G/C classification.
* Your Part's plan, `part<N>.md`, in the same directory — hazards, modelling decisions, and the
  results the book gets wrong.

## Your report

Keep it short and factual:

1. Declarations written, by book label.
2. Anything in the three "not here" categories, with the reason.
3. `## Backbone gaps and friction` — the list described above.
4. The `lake build` result and the `#print axioms` result.
5. Anything that cost you more than twenty minutes, phrased as a gotcha for `NOTES.md`.
