# What is in this repository

Two libraries: `Tdaf` is the backbone, and `TdafSurface` holds one directory per textbook. The
surfaces depend on the backbone and never the other way round, which is why they are separate — the
backbone builds and is read on its own.

So far there is one project: **convex analysis**. `Tdaf/Analysis/Convex` is the general theory over
real vector spaces, developed at four levels of generality — a bare real vector space, a topological
vector space, a locally convex space, and finite-dimensional Euclidean space — with each result
stated at the weakest of the four that carries it. `TdafSurface/Rockafellar` is its surface for
R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), covering all thirty-nine sections of the
book. Every numbered result is formalized except the five making up §22's elementary-vector
development, which is combinatorial matroid theory that the book itself presents as independent of
convexity.

Surface declarations are named for the results they state, so the name is the index: `theorem_33_1`
is Theorem 33.1 and `corollary_37_5_2` is Corollary 37.5.2.

Both libraries build with no `sorry`, no warnings, and nothing beyond the three standard axioms.

`TdafSurface/Rockafellar.lean` is the project's index: the section-by-section outline, the
ambient setup, and the places where formalizing the book corrected it.

`tracker/` is the plan, in the TOML that [tracker](https://github.com/bridgekat/tracker) reads: a
copy of `Tdaf/` and `TdafSurface/` with `.lean` replaced by `.toml`, since a group is the plan for
the module its path names, and a node for each result the libraries stand behind — what the
backbone modules advertise as their main definitions and results, and the book's numbered results
on the surface side, each citing the result it states. After `lake build`, `tracker status` reports
the counts, `tracker show` a group's brief or one node with its signature and real dependencies,
and `tracker graph` the dependency graph. A later project adds its own groups there, one per module
it means to write, and names these nodes as dependencies. `tracker/README.md` states the
conventions the plan is written by.
