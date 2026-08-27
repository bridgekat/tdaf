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
