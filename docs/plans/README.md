# Plans

Formalization plans, as described in the repository README. Each project gets a directory containing
a root plan (`00-overview.md`), a **backbone** tree of sub-plans, and a **surface** tree with one
directory per textbook.

The backbone is general, textbook-independent mathematics: it is named for its subject, stated at
the weakest hypotheses that carry the proof, and must be usable by a reader who has never opened the
book the project started from. A surface is strictly aligned to one text: its modules follow that
text's chapter and section numbering, its declarations are named for the results they state, and it
proves nothing — every surface declaration is an instantiation of a backbone theorem, or a record of
a divergence.

| project | root plan | backbone | surfaces |
|---|---|---|---|
| Convex analysis | [`convex-analysis/00-overview.md`](convex-analysis/00-overview.md) | [`convex-analysis/backbone/`](convex-analysis/backbone/) — 8 sub-plans | [`rockafellar-1970/`](convex-analysis/surface/rockafellar-1970/00-overview.md) — R. T. Rockafellar, *Convex Analysis*, Princeton, 1970 |

## Shape of a project directory

```
convex-analysis/
  00-overview.md            root plan: design decisions, module hierarchy, split test, status
  NOTES.md                  house style, the verification bar, and where everything else is
  api.md                    one record per backbone module: what is in it, what is not, and why
  gotchas.md                Lean and Mathlib traps, grouped by cause
  backbone/
    01-foundations.md … 07-saddle-algebra.md    the general library, by layer
    08-remediation.md                           work the surface will otherwise pay for per-statement
  surface/
    rockafellar-1970/
      00-overview.md        module layout, naming, instantiation and alignment checklists
      inventory.md          every numbered result in the book, with a general/coordinate verdict
      part1.md … part8.md   one plan per Part of the book
```

A plan is a living document: it is written before formalization begins, reviewed whenever the
formalization pushes back on it, and updated when the library changes shape. The `Status` section of
a root plan records what has actually been formalized; `NOTES.md` and its two reference files record
what was learned doing it,
including the places where the book is wrong.
