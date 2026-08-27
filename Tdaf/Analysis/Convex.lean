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

/-!
# Convex analysis

The **backbone** for convex analysis: the theory of convex sets and of extended-real-valued convex
functions over real vector spaces, named for its subject and stated at the weakest hypotheses that
carry each proof. Nothing here is tied to a particular text. `Tdaf.Surface.Rockafellar` is the
surface that tests it against one.

This module imports the whole of `Tdaf.Analysis.Convex` and adds nothing of its own.

## Four levels of generality

Every result is stated at the weakest of these that supports it, so a reader can see from a
declaration's hypotheses what its proof actually uses.

* **A real vector space**, `[AddCommGroup E] [Module ℝ E]` — convexity, epigraphs, the functional
  operations, and conjugacy against a dual pair.
* **A topological vector space**, adding `[TopologicalSpace E]` with continuous addition and
  scalar multiplication — closures, lower semicontinuity, continuity.
* **A locally convex space**, adding `[LocallyConvexSpace ℝ E]` — separation, and through it
  biconjugation and the existence of subgradients.
* **Finite-dimensional Euclidean space**, `[NormedAddCommGroup E] [NormedSpace ℝ E]`
  `[FiniteDimensional ℝ E]` — relative interiors, and everything that rests on `ri C` being
  non-empty for non-empty convex `C`.

A handful of results — proximal mappings, Moreau's decomposition, the gradient theory — additionally
want `[InnerProductSpace ℝ E]`, because they are about a self-pairing rather than a general one.

**Duality is stated for a dual pair**, a bilinear `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, rather than for a
topological dual. `F` is then whatever the application supplies: the continuous dual of a locally
convex space, or `E` itself under an inner product. `Duality.Pairing` collects the two side
conditions a pairing may satisfy — that `⟨·, y⟩` is continuous, and that every continuous linear
functional is some `⟨·, y⟩` — and results ask for them only where they are needed.

## The modules

**The basics.** `Epigraph` introduces `ConvexFn` through the convexity of `epi f`, with `dom f` and
`Proper f`; `Concave` mirrors it. `Closure` builds the closure of a convex function and
`RelativeInterior` the relative interior `ri`. `Continuity` and `Convergence` give continuity on
`ri (dom f)` and the equi-Lipschitz behaviour of convergent families. `Separation` proves the
separation theorems the duality layer runs on. `Face`, `Exposed`, `Representation` and `Tangent`
describe a closed convex set from its boundary; `Caratheodory`, `HullDirections` and `Simplicial`
from its interior. `Helly`, `HellyRefined` and `LinearInequalities` are the theorems of the
alternative. `Homogeneous`, `Homogenize`, `Indicator`, `Lattice`, `Line` and `EuclideanProd` are
the small standing pieces, and `Eponyms` collects the results that have names.

**`Operations`.** Sums, suprema, images and inverse images, infimal convolution: which preserve
convexity, and which preserve closedness.

**`Duality`.** Conjugates and biconjugates, support functions, polars of sets and of functions,
gauges and obverses, and the dual operations table that matches each functional operation with its
conjugate. `Relint`, `Continuity` and `Exact` are the constraint qualifications under which a
closure may be dropped from a duality formula.

**`Recession`.** Recession cones and recession functions, lineality and constancy spaces, and the
closedness criteria for images and sums that they govern.

**`Subgradient`.** Subgradients, normal cones and directional derivatives; gradients and where a
convex function is differentiable; monotonicity and cyclic monotonicity of `∂f`; the Legendre
transformation, essential smoothness and essential strict convexity.

**`Polyhedral`.** Polyhedra by their two descriptions and the Minkowski–Weyl theorem relating them,
the polyhedral calculus, polyhedral functions and their conjugates, and the sharper qualifications
polyhedrality allows.

**`Optimization`.** The minimum and the maximum of a convex function, ordinary and generalized
convex programs, Lagrange multipliers, adjoint bifunctions and dual programs, normality and duality
gaps, Fenchel's duality theorem, and the Moreau envelope with its proximal mapping.

**`Saddle`.** Concave-convex functions, their two partial closures and the equivalence classes
these generate, continuity and differentiability, minimax problems, and the conjugacy that carries
the existence theory of saddle-values.

**`Bifunction`.** The algebra of convex bifunctions — addition, scalar multiplication, application,
composition, and their adjoints — and convex processes, the multivalued maps whose graphs are
convex cones containing the origin.

## Named results

`Eponyms` aliases the results that carry a name, and is the quickest way in: `fenchel_moreau`
(`f** = cl f`), `fenchel_inequality`, `jensen`, `caratheodory`, `krein_milman`, `minkowski_weyl`,
`moreau_decomposition`, `subgradient_maximalMonotone`, and `perspective`. Beyond those, the
headline theorems are `fenchel_duality` in `Optimization.Fenchel`, the separation theorems in
`Separation`, `helly_finite` in `Helly`, `polyhedral_iff_finitelyGenerated` in `Polyhedral.Defs`,
and `ae_differentiableAtFn` in `Subgradient.Rademacher`.

## Conventions

* A convex function is `E → EReal`, total, taking `⊤` off its effective domain and `⊥` only when
  improper. This makes the functional operations total and the lattice complete, at the cost of
  carrying properness as a hypothesis wherever `⊥` would spoil an identity.
* `ri` is scoped notation for `intrinsicInterior ℝ`.
* `f*` is `conj B f`, against an explicit pairing `B`; there is no ambient dual.
* Concave counterparts are separate definitions rather than `-f` rewrites, so that a statement about
  concave functions reads as one.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970.
-/
