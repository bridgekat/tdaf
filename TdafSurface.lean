import TdafSurface.Common.Euclidean
import TdafSurface.Rockafellar
import TdafSurface.Rockafellar.Part1
import TdafSurface.Rockafellar.Part1.Section01
import TdafSurface.Rockafellar.Part1.Section02
import TdafSurface.Rockafellar.Part1.Section03
import TdafSurface.Rockafellar.Part1.Section04
import TdafSurface.Rockafellar.Part1.Section05
import TdafSurface.Rockafellar.Part2
import TdafSurface.Rockafellar.Part2.Section06
import TdafSurface.Rockafellar.Part2.Section07
import TdafSurface.Rockafellar.Part2.Section08
import TdafSurface.Rockafellar.Part2.Section09
import TdafSurface.Rockafellar.Part2.Section10
import TdafSurface.Rockafellar.Part3
import TdafSurface.Rockafellar.Part3.Section11
import TdafSurface.Rockafellar.Part3.Section12
import TdafSurface.Rockafellar.Part3.Section13
import TdafSurface.Rockafellar.Part3.Section14
import TdafSurface.Rockafellar.Part3.Section15
import TdafSurface.Rockafellar.Part3.Section16
import TdafSurface.Rockafellar.Part4
import TdafSurface.Rockafellar.Part4.Section17
import TdafSurface.Rockafellar.Part4.Section18
import TdafSurface.Rockafellar.Part4.Section19
import TdafSurface.Rockafellar.Part4.Section20
import TdafSurface.Rockafellar.Part4.Section21
import TdafSurface.Rockafellar.Part4.Section22
import TdafSurface.Rockafellar.Part5
import TdafSurface.Rockafellar.Part5.Section23
import TdafSurface.Rockafellar.Part5.Section24
import TdafSurface.Rockafellar.Part5.Section25
import TdafSurface.Rockafellar.Part5.Section26
import TdafSurface.Rockafellar.Part6
import TdafSurface.Rockafellar.Part6.Section27
import TdafSurface.Rockafellar.Part6.Section28
import TdafSurface.Rockafellar.Part6.Section29
import TdafSurface.Rockafellar.Part6.Section30
import TdafSurface.Rockafellar.Part6.Section31
import TdafSurface.Rockafellar.Part6.Section32
import TdafSurface.Rockafellar.Part7
import TdafSurface.Rockafellar.Part7.Section33
import TdafSurface.Rockafellar.Part7.Section34
import TdafSurface.Rockafellar.Part7.Section35
import TdafSurface.Rockafellar.Part7.Section36
import TdafSurface.Rockafellar.Part7.Section37
import TdafSurface.Rockafellar.Part8
import TdafSurface.Rockafellar.Part8.Section38
import TdafSurface.Rockafellar.Part8.Section39

/-!
# TDAF surfaces

The **surfaces** of TDAF, one directory per textbook and each aligned to its text section by
section. A surface states a book's results in the book's own terms and proves them from `Tdaf`, the
backbone: it is the integration test the backbone has to pass, not a place to prove new
mathematics. A surface whose proof does not go through the backbone is a sign the backbone is
missing something.

The dependency runs one way and never the other, which is why this is a library of its own: `Tdaf`
builds and is read without any of it.

`TdafSurface.Common` holds what a surface shares with the next one rather than with a book.
`TdafSurface.Common.Euclidean` instantiates the backbone's duality theory at `ℝⁿ`, so that a book
working in coordinates does not restate it.

## Rockafellar, *Convex Analysis*

`TdafSurface.Rockafellar` is the surface for R. T. Rockafellar, *Convex Analysis* (Princeton,
1970), covering all thirty-nine sections of the book over `Tdaf.Analysis.Convex`. Every numbered
result is formalized except the five making up §22's elementary-vector development, which is
combinatorial matroid theory that the book itself presents as independent of convexity. That module
is the project's index: it carries the section-by-section outline and the places where formalizing
the book corrected it.

**Surface declarations are named for the results they state**, so the name is the index:
`theorem_33_1` is Theorem 33.1 and `corollary_37_5_2` is Corollary 37.5.2. Where one numbered
result needs several declarations — its clauses, or the two directions of an equivalence — a
trailing word distinguishes them, as in `theorem_37_5_a` and `theorem_34_2_dom₁`. Everything sits
in the flat `Rockafellar` namespace.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970.
-/
