# What is in this repository

`Tdaf/Analysis` is the backbone; `Tdaf/Surface` holds one directory per textbook.

So far there is one project: **convex analysis**. `Tdaf/Analysis/Convex` is the general theory over
real vector spaces, developed at four levels of generality — a bare real vector space, a topological
vector space, a locally convex space, and finite-dimensional Euclidean space — with each result
stated at the weakest of the four that carries it. `Tdaf/Surface/Rockafellar` is its surface for
R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), covering all thirty-nine sections of the
book. Every numbered result is formalized except the five making up §22's elementary-vector
development, which is combinatorial matroid theory that the book itself presents as independent of
convexity.

Surface declarations are named for the results they state, so the name is the index: `theorem_33_1`
is Theorem 33.1 and `corollary_37_5_2` is Corollary 37.5.2.

The library builds with no `sorry`, no warnings, and nothing beyond the three standard axioms.

`Tdaf/Surface/Rockafellar.lean` is the project's index: the section-by-section outline, the
ambient setup, and the places where formalizing the book corrected it.

`tracker/` is the plan, in the TOML that [tracker](https://github.com/bridgekat/tracker) reads: one
group per module, and a node for each result the library stands behind — what the backbone modules
advertise as their main definitions and results, and the book's numbered results on the surface
side, each citing the result it states. `lake build && lake exe tracker check` resolves every node
against the compiled library; `tracker status` reports the counts, `tracker show` a group's brief or
one node with its signature and real dependencies, and `tracker graph` the dependency graph. The
backbone and the surfaces are separate root groups, and a later project adds its own there and names
these nodes as dependencies. `tracker/README.md` states the conventions the plan is written by.
