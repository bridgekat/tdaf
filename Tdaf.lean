import Tdaf.Analysis.Convex
import Tdaf.Analysis.Convex.Bifunction.Algebra
import Tdaf.Analysis.Convex.Bifunction.Cofinite
import Tdaf.Analysis.Convex.Bifunction.LinearProcess
import Tdaf.Analysis.Convex.Bifunction.Process
import Tdaf.Analysis.Convex.Bifunction.ProcessDuality
import Tdaf.Analysis.Convex.Caratheodory
import Tdaf.Analysis.Convex.Closure
import Tdaf.Analysis.Convex.Concave
import Tdaf.Analysis.Convex.Continuity
import Tdaf.Analysis.Convex.Convergence
import Tdaf.Analysis.Convex.Duality.Barrier
import Tdaf.Analysis.Convex.Duality.ConcaveConj
import Tdaf.Analysis.Convex.Duality.ConcaveOps
import Tdaf.Analysis.Convex.Duality.Conjugate
import Tdaf.Analysis.Convex.Duality.Continuity
import Tdaf.Analysis.Convex.Duality.Exact
import Tdaf.Analysis.Convex.Duality.FiniteProduct
import Tdaf.Analysis.Convex.Duality.Gauge
import Tdaf.Analysis.Convex.Duality.GaugeLike
import Tdaf.Analysis.Convex.Duality.HomConePolar
import Tdaf.Analysis.Convex.Duality.InnerPairing
import Tdaf.Analysis.Convex.Duality.Level
import Tdaf.Analysis.Convex.Duality.Ops
import Tdaf.Analysis.Convex.Duality.Pairing
import Tdaf.Analysis.Convex.Duality.Polar
import Tdaf.Analysis.Convex.Duality.PolarBounded
import Tdaf.Analysis.Convex.Duality.Relint
import Tdaf.Analysis.Convex.Duality.RelintSeparation
import Tdaf.Analysis.Convex.Duality.Support
import Tdaf.Analysis.Convex.Duality.SupportRelint
import Tdaf.Analysis.Convex.Epigraph
import Tdaf.Analysis.Convex.Eponyms
import Tdaf.Analysis.Convex.EuclideanProd
import Tdaf.Analysis.Convex.Exposed
import Tdaf.Analysis.Convex.Face
import Tdaf.Analysis.Convex.Helly
import Tdaf.Analysis.Convex.HellyRefined
import Tdaf.Analysis.Convex.Homogeneous
import Tdaf.Analysis.Convex.Homogenize
import Tdaf.Analysis.Convex.HullDirections
import Tdaf.Analysis.Convex.Indicator
import Tdaf.Analysis.Convex.Lattice
import Tdaf.Analysis.Convex.Line
import Tdaf.Analysis.Convex.LinearInequalities
import Tdaf.Analysis.Convex.Operations.Basic
import Tdaf.Analysis.Convex.Operations.Closed
import Tdaf.Analysis.Convex.Operations.Epi
import Tdaf.Analysis.Convex.Operations.Hull
import Tdaf.Analysis.Convex.Operations.Image
import Tdaf.Analysis.Convex.Operations.InfConv
import Tdaf.Analysis.Convex.Optimization.Adjoint
import Tdaf.Analysis.Convex.Optimization.ConeDuality
import Tdaf.Analysis.Convex.Optimization.Fenchel
import Tdaf.Analysis.Convex.Optimization.Lagrangian
import Tdaf.Analysis.Convex.Optimization.Maximum
import Tdaf.Analysis.Convex.Optimization.Minimum
import Tdaf.Analysis.Convex.Optimization.Moreau
import Tdaf.Analysis.Convex.Optimization.MoreauGradient
import Tdaf.Analysis.Convex.Optimization.Normal
import Tdaf.Analysis.Convex.Optimization.Perturbation
import Tdaf.Analysis.Convex.Optimization.Program
import Tdaf.Analysis.Convex.Optimization.Prox
import Tdaf.Analysis.Convex.Polyhedral.Closedness
import Tdaf.Analysis.Convex.Polyhedral.Cone
import Tdaf.Analysis.Convex.Polyhedral.Conjugate
import Tdaf.Analysis.Convex.Polyhedral.Defs
import Tdaf.Analysis.Convex.Polyhedral.Duality
import Tdaf.Analysis.Convex.Polyhedral.Faces
import Tdaf.Analysis.Convex.Polyhedral.Function
import Tdaf.Analysis.Convex.Polyhedral.Homogeneous
import Tdaf.Analysis.Convex.Polyhedral.NormalForm
import Tdaf.Analysis.Convex.Polyhedral.Ops
import Tdaf.Analysis.Convex.Polyhedral.Recession
import Tdaf.Analysis.Convex.Polyhedral.Separation
import Tdaf.Analysis.Convex.Polyhedral.Simplicial
import Tdaf.Analysis.Convex.Recession.Closedness
import Tdaf.Analysis.Convex.Recession.Cone
import Tdaf.Analysis.Convex.Recession.ConeHull
import Tdaf.Analysis.Convex.Recession.Conjugate
import Tdaf.Analysis.Convex.Recession.Function
import Tdaf.Analysis.Convex.Recession.PiSum
import Tdaf.Analysis.Convex.RelativeInterior
import Tdaf.Analysis.Convex.Representation
import Tdaf.Analysis.Convex.Saddle.Closure
import Tdaf.Analysis.Convex.Saddle.Conjugate
import Tdaf.Analysis.Convex.Saddle.Continuity
import Tdaf.Analysis.Convex.Saddle.Correspondence
import Tdaf.Analysis.Convex.Saddle.Defs
import Tdaf.Analysis.Convex.Saddle.Differential
import Tdaf.Analysis.Convex.Saddle.Equiv
import Tdaf.Analysis.Convex.Saddle.Existence
import Tdaf.Analysis.Convex.Saddle.Kernel
import Tdaf.Analysis.Convex.Saddle.Minimax
import Tdaf.Analysis.Convex.Saddle.Monotone
import Tdaf.Analysis.Convex.Saddle.Rademacher
import Tdaf.Analysis.Convex.Saddle.Subgradient
import Tdaf.Analysis.Convex.Separation
import Tdaf.Analysis.Convex.Simplicial
import Tdaf.Analysis.Convex.Subgradient.Approx
import Tdaf.Analysis.Convex.Subgradient.BoundaryDirDeriv
import Tdaf.Analysis.Convex.Subgradient.Bounded
import Tdaf.Analysis.Convex.Subgradient.Calculus
import Tdaf.Analysis.Convex.Subgradient.Cofinite
import Tdaf.Analysis.Convex.Subgradient.Convergence
import Tdaf.Analysis.Convex.Subgradient.Defs
import Tdaf.Analysis.Convex.Subgradient.Differentiability
import Tdaf.Analysis.Convex.Subgradient.EssentiallySmooth
import Tdaf.Analysis.Convex.Subgradient.Existence
import Tdaf.Analysis.Convex.Subgradient.Gradient
import Tdaf.Analysis.Convex.Subgradient.GradientLimit
import Tdaf.Analysis.Convex.Subgradient.Integral
import Tdaf.Analysis.Convex.Subgradient.Legendre
import Tdaf.Analysis.Convex.Subgradient.LegendreType
import Tdaf.Analysis.Convex.Subgradient.Monotone
import Tdaf.Analysis.Convex.Subgradient.OneDim
import Tdaf.Analysis.Convex.Subgradient.Preservation
import Tdaf.Analysis.Convex.Subgradient.Primitive
import Tdaf.Analysis.Convex.Subgradient.Rademacher
import Tdaf.Analysis.Convex.Subgradient.Reconstruction
import Tdaf.Analysis.Convex.Subgradient.StrictlyConvex
import Tdaf.Analysis.Convex.Subgradient.Uniqueness
import Tdaf.Analysis.Convex.Tangent
import Tdaf.LinearAlgebra.Subspace
import Tdaf.Order.EReal
import Tdaf.Order.GaloisConnection

/-!
# TDAF

A formal library of applied mathematics, built in two layers. This is the **backbone**: general
mathematics, named for its subject and stated at the weakest hypotheses that carry the proof. It is
meant to be read and used without reference to any particular text.

The **surfaces** are `TdafSurface`, a library of its own, one directory per textbook and each
aligned to its text section by section. A surface proves almost nothing: each declaration
instantiates a backbone result at the book's own hypotheses, so a surface reads as an integration
test of this library against a published account of the subject. The dependency runs that way and
never the other, which is why the surfaces are separate and the backbone builds without them.

## Convex analysis

`Tdaf.Analysis.Convex` is the backbone for convex analysis over real vector spaces, developed at
four levels of generality — a bare real vector space, a topological vector space, a locally convex
space, and finite-dimensional Euclidean space — with each result stated at the weakest of the four
that supports it. `TdafSurface.Rockafellar` is the surface that tests it, against R. T.
Rockafellar, *Convex Analysis* (Princeton, 1970), covering all thirty-nine sections of the book.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970.
-/
