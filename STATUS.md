# Implementation status

## Implemented and checked

The library has 105 modules and 1078 named public theorems. All compile on the
pinned Lean/mathlib v4.33.1 toolchain.

| Module | Implemented scope |
| --- | --- |
| `NLS.SequenceSpaces.Basic` | Integer-indexed complex `lp` coefficients |
| `NLS.SequenceSpaces.Truncation` | Finite projections; coefficient formula; linearity; composition and idempotence; projection and tail norm bounds; continuous linear projections; convergence for finite `p`; density of finite-support coefficients |
| `NLS.SequenceSpaces.Weighted` | Positive, unit, and real-exponent Sobolev weights; weighted coefficient spaces; weighting equivalence and isometry; normed complex vector space and completeness; coefficient decay; weighted truncation bounds and convergence |
| `NLS.SequenceSpaces.Multiplier` | Bounded diagonal symbols; norm bound; continuous linear operator; commutation with truncations |
| `NLS.SequenceSpaces.Translation` | Reindexing by an integer equivalence preserves the norm; shifts as linear isometry equivalences |
| `NLS.SequenceSpaces.Convolution` | Absolutely convergent Banach-space construction; coefficient formula; `lp × l1 → lp` norm bound, including `p=∞`; continuous bilinear map; single-mode shift identity |
| `NLS.SequenceSpaces.Embedding` | General weighted Hölder embedding into `l1` when the reciprocal weight belongs to the conjugate space; explicit bound and injectivity |
| `NLS.SequenceSpaces.SobolevEmbedding` | Reciprocal one-derivative weight is in `lq` for `q>1`, including infinity; continuous embedding `FL^{1,p} → FL^1` for every finite `p≥1` with an explicit constant |
| `NLS.SequenceSpaces.ReciprocalSeries` | Appendix B.1 with its exact conjugate-exponent constants; summability; one-sided integral tail bounds; bilateral punctured-lattice identities and estimates; invariance under frequency translation |
| `NLS.SequenceSpaces.SobolevConstant` | Numerical reciprocal-weight norm and Sobolev embedding constant at most `2p`, including the `p=1` endpoint |
| `NLS.SequenceSpaces.ReciprocalNorm` | Conjugate-space reciprocal-tail norm bound `4p h^(-1/p)`; central-coefficient decomposition and the additional `1/h` term |
| `NLS.ZakharovShabat.Potential` | Scalar Fourier-side potential multiplication on the one-derivative domain; convolution coefficient formula; norm and operator-norm bounds; constant unit potential identity |
| `NLS.ZakharovShabat.Domain` | Contractive, injective scalar inclusion with dense range for finite `p`; period-two differentiation and its norm bound; scalar Fourier modes |
| `NLS.ZakharovShabat.Operator` | Pair domain inclusion and density; free, potential, and total operators; coefficient formulas; maximum-pair-norm bounds; nonzero signed free eigenmodes; zero and unit potential identities; spectral pencil |
| `NLS.SequenceSpaces.Compact` | Compactness of finite Fourier projections; uniform symbol-tail bound for the cutoff error; operator-norm convergence and compactness of vanishing diagonal multipliers, including `p=∞` |
| `NLS.ZakharovShabat.FreeResolvent` | Closed free lattice and positive spectral gap; inverse into the one-derivative domain; both inverse identities and continuous linear equivalence; domain and base-space bounds; signed-mode formulas and resolvent identity |
| `NLS.ZakharovShabat.FreeResolventCompact` | Uniform decay of reciprocal symbols; operator-norm convergence of scalar resolvent cutoffs; compactness of scalar and pair free resolvents for all Banach exponents |
| `NLS.ZakharovShabat.ResolventEstimates` | Reciprocal symbols in the conjugate space; scalar and pair `FL^p → FL^1` maps and Hölder bounds; the endpoint bound `1 / abs(Im z)` for `p=1` |
| `NLS.ZakharovShabat.PerturbedResolvent` | Potential/free-resolvent composition; explicit Neumann condition; convergent geometric correction; factorization and both inverse identities; domain and base-space norm bounds; compactness; an admissible parameter for every `l1` potential |
| `NLS.SequenceSpaces.DominatedConvergence` | Coordinatewise convergence plus an `lp` majorant implies norm convergence at finite Banach exponents, along arbitrary filters |
| `NLS.ZakharovShabat.UniformResolvent` | Explicit reciprocal envelopes; convergence of their conjugate norms; Fourier recentering; bounds uniform in real parts and bounded potential sets; existence of a compact two-sided inverse for every finite-p potential |
| `NLS.ZakharovShabat.ClosedOperator` | Partial linear map on the base space; exact one-derivative domain; agreement with the domain-to-base operator; dense domain; closed graph via a bounded inverse; stability under base-norm graph limits |
| `NLS.ZakharovShabat.ResolventAnalytic` | Full resolvent set and joint open domain; potential dependence in operator norm; totalized inverse with both identities; nonempty resolvent set; agreement with Neumann construction; joint complex analyticity; compactness on the full resolvent set |
| `NLS.FunctionalAnalysis.CompactSpectrum` | Riesz-lemma proof of finiteness of compact-operator eigenvalues and spectral values away from zero; finite-dimensional nonzero eigenspaces, without self-adjointness |
| `NLS.ZakharovShabat.PeriodicSpectrum` | Closed periodic spectrum; spectral transformation through a compact resolvent; finiteness in every bounded region; discrete subspace topology; equivalence with domain eigenvalues; finite geometric multiplicities |
| `NLS.ZakharovShabat.ResolventCalculus` | General inverse difference identities; resolvent commutation; potential differences; joint Fréchet derivatives into the domain and base space; spectral and potential derivative formulas; compatibility with the free resolvent and the pre-Neumann identity |
| `NLS.FunctionalAnalysis.CompactGeneralized` | Compact shifted powers after removal of the constant term; finite-dimensional generalized eigenspaces at nonzero values; Riesz-lemma stabilization; finite-dimensional full generalized eigenspaces |
| `NLS.ZakharovShabat.RootSpaces` | Domain-aware recursive periodic root spaces; reference-independent definition; bounded compact-pencil representation; finite-dimensional closed full root spaces; finite stabilization; algebraic multiplicity and its spectral characterization |
| `NLS.FunctionalAnalysis.CompactDecomposition` | Fredholm bijectivity for injective compact perturbations of a nonzero scalar identity; topological kernel/range decomposition at a stabilized exponent; commutation of projections with maps preserving both summands |
| `NLS.ZakharovShabat.SpectralProjections` | Bounded finite-rank periodic root-space projections; independence of the reference resolvent parameter; idempotence and resolvent commutation; rank equals algebraic multiplicity; compactness; unique topological decomposition; vanishing exactly on the resolvent set |
| `NLS.ZakharovShabat.SpectralClusters` | Reciprocal resolvent representation of full root spaces; disjointness at distinct parameters; projection annihilation and commutation; finite cluster spaces and compact projections; range and kernel formulas; additive algebraic multiplicities; composition by intersection; unique cluster/complement decomposition |
| `NLS.FunctionalAnalysis.CircleIntegral` | Bounded linear maps and evaluation commute with Banach-valued circle integrals; interchange of continuous double circle integrals |
| `NLS.ZakharovShabat.ResolventContour` | Normalized resolvent circle integrals into the base space and domain; circle integrability, factorization, compactness, norm bound; Cauchy vanishing and annulus deformation; root-chain integral formula; inside/outside action on full root spaces; resolvent and projection commutation; finite-cluster selection |
| `NLS.ZakharovShabat.ContourProjection` | Existence of resolvent annuli; nested-circle product law; idempotence, finite rank, and topological range/kernel decomposition of the contour operator |
| `NLS.ZakharovShabat.ContourSpectrum` | Finite enclosed spectrum; identification of the whole contour range with enclosed root spaces; equality with the algebraic cluster projection; algebraic-multiplicity rank formula; kernel formula; equality for circles with the same enclosed spectrum; isolated-value projections |
| `NLS.FunctionalAnalysis.CircleIntegrationMap` | Normalized circle integration as a bounded linear map on continuous functions with the uniform norm; agreement on the circle; norm at most the radius |
| `NLS.FunctionalAnalysis.ProjectionRank` | Injectivity on the range of a projection under perturbations smaller than one; equality of ranks for nearby finite-rank projections; norm gap for nonzero idempotents; zero and fixed-range containment persist under preconnected continuous deformations; rank constancy for arbitrary continuous preconnected finite-rank projection families |
| `NLS.ZakharovShabat.ContourAnalytic` | Open admissible-potential domain for a fixed circle; operator-norm analytic dependence of base-space and domain-valued contour projections; locally constant rank and total enclosed algebraic multiplicity |
| `NLS.FunctionalAnalysis.ProjectionTransport` | Explicit projection intertwiner; invertible ambient and range equivalences; analytic transport and inverse; fixed-range compression, analytic dependence, and exact intertwining |
| `NLS.ZakharovShabat.SpectralReduction` | Bounded analytic `L P` through the domain contour lift; projection/operator intertwining; fixed-range analytic spectral reduction on an open neighborhood; reference and enclosed-eigenvector identities |
| `NLS.FunctionalAnalysis.FiniteSpectralTrace` | Two-dimensional characteristic roots with repetition; first, second, and centered trace identities; bounded trace functional and analytic traces |
| `NLS.ZakharovShabat.ContourTrace` | Exact conjugacy of local and intrinsic restrictions; reference-independent traces of all powers; analyticity of power traces and symmetric trace expressions |
| `NLS.ZakharovShabat.SymmetricEigenvalues` | Exact enclosed-eigenvalue characterization of the restriction; midpoint and squared-gap trace identities; free values; Lemma 3.7 uniformly on the counting neighborhood, with counted eigenvalue pairs |
| `NLS.ZakharovShabat.FreeMultiplicity` | Resonant coefficient embedding; independence of the signed free modes; support of every free root chain; equality of ordinary and full root spaces; free algebraic multiplicity two |
| `NLS.ZakharovShabat.DiskMultiplicity` | Constant contour rank and total multiplicity on preconnected admissible families; isolated free disk spectrum; Proposition 1.1(i)’s high-frequency rank and algebraic-multiplicity count, uniform on a convex neighborhood containing zero |
| `NLS.ZakharovShabat.DiskParity` | Free contour range in index parity; parity preservation under preconnected deformations; generalized root-space and domain eigenfunction parity; opposite-parity contour annihilation; uniform multiplicity and parity package for Proposition 1.1(i) |
| `NLS.ZakharovShabat.CentralRectangle` | Compact closed rectangle and boundary; vertical edge strip coverage; uniform resolvent inclusion on every larger boundary and exterior; equality of open, closed, and mixed central spectra |
| `NLS.ZakharovShabat.CentralSpectrum` | Finite central spectrum and boundary-convention independence; exact free lattice interval; free multiplicity `4N+2`; compact idempotent central algebraic projection, rank formula, and free rank |
| `NLS.ZakharovShabat.CentralDeformation` | Half-integer-radius lattice gap; enlarged-circle geometry; exact spectral selection and whole central/circle projection equality; analytic central projection and total count `4K+2`, uniform in the potential and every larger cutoff |
| `NLS.ZakharovShabat.CentralParity` | Signed parity index count; free parity projector equals filtered spectral cluster; finite rank and exact range intersection; analytic components; uniform `2N+2`/`2N` parity split with the total central count on one neighborhood |
| `NLS.ZakharovShabat.PeriodicCounting` | One cutoff and neighborhood for localization, central and disk counts, parity, and analytic projections; unique high-disk classification; eigenvalue pairs with repetition and exact multiplicities |
| `NLS.SequenceSpaces.Pairing` | Absolutely convergent `lp`/`l1` coefficient duality; norm bound and linearity; positive squared energy; product-index summability and conjugate-reflected convolution adjoint identity |
| `NLS.ZakharovShabat.RealType` | Fourier-coordinate real type; conjugate single-mode potentials; domain duality, Hermitian inclusion and operator symmetry; positive energy; real periodic spectrum and resolvent inclusion for every nonreal parameter |
| `NLS.ZakharovShabat.VerticalStrips` | Punctured vertical strips; denominator geometry and free-lattice avoidance; uniform `2p/r` reciprocal-symbol bound and Lemma 3.2(iii)’s `8p/r` operator bound; explicit Neumann condition; common spectral circles and disk localization for small potentials |
| `NLS.ZakharovShabat.HeightResolvent` | Lemma 3.2(ii)’s numerical height bound; explicit Neumann region and Corollary 3.3 analyticity; decay to zero; larger-height inclusion; uniform heights on bounded potential sets; nonempty region and agreement with the constructive inverse |
| `NLS.FunctionalAnalysis.SquaredNeumann` | Geometric inversion of `1-K²`; both inverse identities for `(1+K)(1-K²)⁻¹`; correction norm bound; terminating inverse for square-zero operators |
| `NLS.ZakharovShabat.DoubleResolvent` | `FL^1 → FL^p` potential convolution; double free resolvent and both coefficient formulas; global norm bound; square factorization and sandwich criterion; domain inverse identities; agreement with the full resolvent and quantitative bounds; nilpotence and exact two-term resolvents for one-sided potentials |
| `NLS.SequenceSpaces.FourierTail` | Strict low-frequency cutoffs and closed centered windows; separation of opposite near windows; symmetric tails retaining the boundary; single-mode behavior; contraction, composition, monotonicity, and convergence |
| `NLS.SequenceSpaces.ConvolutionSandwich` | Conjugate-space multipliers and weighted convolution `FL^p → FL^1`; norm bounds; exact far-output/far-input/potential-tail decomposition and the corresponding three-term estimate |
| `NLS.SequenceSpaces.ReciprocalTail` | Half-window reciprocal-tail norm bounds, including the supremum endpoint; recentering and rescaling; explicit `8p/r * N^(-1/p)` decay |
| `NLS.ZakharovShabat.DoubleResolventEstimates` | Pair Fourier remainders and convergence; scalar sandwich identification; reciprocal-symbol tails; Lemma 3.4 with `c_p = 32p²`; explicit squared Neumann, punctured-strip, and spectral-circle criteria |
| `NLS.ZakharovShabat.FrequencyLocalization` | Continuous linear pair tails; monotone tail norms; open convex norm-and-tail neighborhoods containing zero; reciprocal-frequency decay; common half-size squared Neumann bounds and high-frequency resolvent strips |
| `NLS.ZakharovShabat.SpectralLocalization` | Exact central boxes and high-frequency disks; exterior coverage including vertical edges; common open convex potential neighborhoods; Corollary 3.5 compact analytic resolvent and spectral enclosure; retained uniform positive integer height and strip bounds, including height equality |
| `NLS.SequenceSpaces.Parity` | Contractive residue-class Fourier projections; coefficient and single-mode formulas; closed complementary even/odd subspaces; even-potential convolution commutation and invariance; parity masks on arbitrary weighted coefficient spaces |
| `NLS.ZakharovShabat.PeriodicParity` | Closed complementary pair parity spaces and closed domain parity spaces; domain/base projection intertwining; Lemma 3.6; spectral-pencil, domain-resolvent, base-resolvent, and contour-projection parity preservation; signed free-mode parity |
| `NLS.SequenceSpaces.Reflection` | Frequency reversal as a linear isometry, involution, and convolution identity; reflection for every real Sobolev weight |
| `NLS.FunctionalAnalysis.ReflectionSplit` | Closed complementary positive/negative graphs of an isometry; isometric amplitude coordinates; contractive complementary projections and their algebraic identities |
| `NLS.ZakharovShabat.BoundarySpaces` | Section 4 equations (1.8)–(1.9): closed Dirichlet/Neumann coefficient spaces at every Sobolev regularity; amplitude isometries; domain/base projection compatibility; nonzero signed free boundary modes |
| `NLS.ZakharovShabat.BoundaryOperators` | Coefficient form of Lemma 4.4 for already-reflected potentials: both invariant subspaces, bounded restricted operators, projection intertwining, and exact positive/negative mode-action signs |
| `NLS.ZakharovShabat.BoundaryResolvent` | Actual Dirichlet/Neumann pencils and full resolvent sets; fixed-free normalization; two-sided inverses; compactness; joint analyticity and openness; agreement with periodic restrictions on the common domain; boundary preservation by resolvents and circle projections |
| `NLS.ZakharovShabat.BoundarySpectrum` | Closed discrete boundary spectra, finite bounded portions, compact-resolvent spectral transformation and eigenvector characterization; periodic resolvent intersection and spectral union |
| `NLS.ZakharovShabat.BoundaryRootSpaces` | Actual restricted-pencil root chains; exact periodic boundary intersections; domain representatives; finite dimension, stabilization, and closed full root spaces; spectral characterization of algebraic multiplicity; periodic multiplicity as the sum of both boundary contributions |
| `NLS.ZakharovShabat.FreeBoundaryMultiplicity` | Signed free boundary modes and exact lattice spectra; algebraic multiplicity one and absence of longer free chains; rank one in each free quarter-pi contour summand; free central count `2N+1` for each boundary condition |
| `NLS.ZakharovShabat.BoundaryClusters` | Boundary-preserving individual and cluster projections; finite sums of actual boundary root spaces and exact periodic intersections; bounded restricted and ambient projections, idempotence, and rank/multiplicity formulas; contour identification and operator-norm analyticity |
| `NLS.ZakharovShabat.BoundaryCounting` | Actual finite boundary spectra in disks and central boxes; coefficient Theorem 1.4 counts on one neighborhood for every larger cutoff; central ranks/counts `2N+1`, high-disk ranks/counts one, unique simple eigenvalues, and shared analytic projection families and localization |
| `NLS.FunctionalAnalysis.ProjectionTrace` | Intrinsic restriction and trace on varying projection ranges; conjugacy under local transport; analytic traces for commuting analytic families; trace equals the eigenvalue on a one-dimensional range |
| `NLS.ZakharovShabat.BoundarySpectralReduction` | Analytic contour lifts into the actual weighted boundary domains; inclusion and projection identities; bounded analytic `L P`; spectral support, commutation, and exact action on enclosed boundary eigenvectors |
| `NLS.ZakharovShabat.BoundaryEigenvalues` | Trace-defined boundary eigenvalues; analytic intrinsic traces on reflected potentials; rank-one identification with the actual spectrum; signed free values; coefficient Lemma 4.5 on one open convex neighborhood with uniform counting data and actual domain eigenvectors |
| `NLS.Fourier.IntervalKernel` | Actual half-period Fourier integrals; reflected waves; exact even and odd overlap coefficients with normalization |
| `NLS.Fourier.FoldedInterval` | Piecewise reflected integral formula for continuous inputs; finite Fourier synthesis and even/odd half-coefficients |
| `NLS.Fourier.IntervalKernelLp` | Translation identity; reciprocal norm envelope; kernel membership for every `p>1`; failure at `p=1` via the harmonic series |
| `NLS.ZakharovShabat.IntervalExtension` | Physical reflected/swapped linear maps; Fourier reflection relation; normalized finite-input amplitudes; constant and one-sided coefficient formulas |
| `NLS.ZakharovShabat.FiniteIntervalExtension` | Linear finite-input maps into actual boundary `ℓp` spaces; exact equality with physical Fourier integrals; physical `p=1` counterexample |
| `NLS.SequenceSpaces.FiniteCoefficients` | Canonical linear inclusion of finite coefficients into `ℓp`; dense range for finite Banach exponents; exact finite Hilbert energy; finite-input convolution formula |
| `NLS.Fourier.IntervalParseval` | Agreement with mathlib interval Fourier coefficients; square integrability across reflected joins; Parseval; polynomial and reflected-block energy identities |
| `NLS.ZakharovShabat.HilbertIntervalExtension` | Exact finite-input energy and uniform contraction; completion to all Hilbert pairs; physical agreement on polynomials; closed boundary membership; exact energy, injectivity, and uniqueness after completion |
| `NLS.Fourier.ShiftedHilbert` | Contractive odd-index sampling; normalized shifted Hilbert operator on all `ℓ2`; explicit norm bound and exact finite reciprocal kernel |
| `NLS.Fourier.HilbertKernel` | Ordinary/shifted kernel comparison; reciprocal and square-decay bounds; absolutely summable correction and its bounded convolution on every Banach exponent |
| `NLS.Fourier.DiscreteHilbert` | Ordinary Hilbert transform on `ℓ2`; exact source kernel and zero diagonal; uniform bound; finite synthesis at every `p>1` |
| `NLS.Fourier.CotlarIdentity` | Scalar cancellation at all index collisions; finite complex-sequence Cotlar identity with both discrete correction terms |
| `NLS.Fourier.HilbertSquare` | Absolutely summable square kernel; bounded remainder operator at all Banach exponents; equality with the finite rational remainder |
| `NLS.SequenceSpaces.QuarticProduct` | Hölder product `ℓ4 × ℓ4 → ℓ2`; norm bound and exact square-product norm identity |
| `NLS.Fourier.QuarticHilbert` | Uniform finite-input quartic estimate from Cotlar; completed ordinary and shifted `ℓ4` transforms; explicit bounds and exact finite reciprocal formulas |
| `NLS.SequenceSpaces.DoublingProduct` | General Hölder product `ℓq × ℓq → ℓp` at `q=2p`; norm bound and exact square-product norm identity; specializes to the quartic product |
| `NLS.Fourier.HilbertEstimate` | Quantitative finite-input estimates; unique continuous ordinary and shifted completions; exact coefficient formulas and bounds; independence of the estimate package |
| `NLS.Fourier.HilbertDoubling` | General Cotlar quadratic estimate and its solution; constructs a proved estimate at `2p` from one at `p` |
| `NLS.Fourier.DyadicHilbert` | Recursive ordinary and shifted operators at every `2^(n+1)`; exact finite formulas; explicit recurrence and closed bound; unboundedness of the proved exponents |
| `NLS.SequenceSpaces.ConjugateDuality` | Absolutely convergent bounded bilinear Hölder pairing; finite coefficient formulas; finite norming tests for truncations; norm detection by finite conjugate tests and their unit ball |
| `NLS.Fourier.HilbertDuality` | Finite Hilbert antisymmetry; conjugate-exponent estimate with unchanged constant; transposition identity on arbitrary completed inputs |
| `NLS.Fourier.ConjugateHilbert` | Ordinary and shifted operators at dyadic conjugates `2, 4/3, 8/7, …`; exact coefficients and bounds; exponents in `(1,2]` arbitrarily close to one; transposition with the dyadic family |
| `NLS.SequenceSpaces.InterpolationFamily` | Entire complex phase/power families with fixed finite support; exact coefficient norms and interior recovery; normalized edge norms and strip coefficient bounds |
| `NLS.SequenceSpaces.FiniteInterpolation` | Finite complex kernel pairings; entire scalar strip family and explicit strip bound; three-lines interpolation of endpoint estimates on normalized input/test pairs |
| `NLS.Fourier.HilbertInterpolation` | Hilbert kernel endpoint pairing bounds; interpolation of conjugate reciprocal exponents; finite unit estimate and rescaling; completed intermediate Hilbert estimate |
| `NLS.Fourier.HilbertBoundedness` | Admissible interpolation parameters; completed ordinary and shifted transforms for every `1<p<∞`; bounds, uniqueness, exact finite formulas, and full-range transposition |
| `NLS.Fourier.HilbertSeries` | Absolutely convergent ordinary and shifted reciprocal series; exact coefficient formulas for arbitrary inputs via conjugate tests and density |

## Current mathematical milestone

For every `1 ≤ p < ∞`, we have constructed the coefficient-space operator

`operator hp φ : Domain p →L[ℂ] PairSpace p`

with `Domain p = ScalarDomain p × ScalarDomain p` and
`ScalarDomain p = WeightedCoeff (Weight.sobolev 1) p`. The domain inclusion is
injective, contractive, and has dense range. With the maximum norm on pairs,

`‖operator hp φ f‖ ≤ (π + C_p * ‖φ‖) * ‖f‖`.

Here `C_p` is the norm of the reciprocal weight in the Hölder conjugate space.
Potential multiplication is the previously proved convolution construction,
which establishes the coefficient estimate underlying Appendix A, Lemma A.8.

Both scalar components use modes `exp(i π n x)` on the period-two circle.
Differentiation has symbol `i π n`; the free operator therefore has symbols
`-π n` and `+π n`. The dissertation's signed modes use scalar frequencies `-n`
and `n`, respectively. Their included vectors are proved nonzero and satisfy
`L₀ eₙ⁻ = π n eₙ⁻` and `L₀ eₙ⁺ = π n eₙ⁺`.

The domain and operator follow Chapter 1, §3, printed page 23; the signed-mode
convention follows §2, equation (1.2). The spectral pencil is explicitly a map
from the domain to the base space. The unbounded realization is now proved
closed, as detailed below. The physical Fourier/distribution realization remains
unproved.
The dissertation's pair norm is not used for these numerical bounds; its
comparison with the chosen maximum norm is a separate proof obligation.

For every `1 ≤ p ≤ ∞` and every `z ∉ πℤ`, the free equation is now a
continuous linear equivalence between the one-derivative domain and base space.
The inverse `freeResolventToDomain z hz` satisfies both inverse identities.
Writing `δ(z) = dist(z, πℤ) > 0`, we prove

- `‖freeResolvent z hz‖ ≤ 1 / δ(z)` on the base space;
- `‖freeResolventToDomain z hz‖ ≤ 1 / δ(z) + (1 + ‖z‖ / δ(z)) / π`;
- `R₀(z) - R₀(w) = (w - z) R₀(z) R₀(w)`;
- compactness of `freeResolvent z hz` on the base space.

The compactness proof constructs finite Fourier cutoffs and proves convergence
in operator norm from uniform decay of the reciprocal symbol. This establishes
the coefficient-space content of Chapter 1, Lemma 3.2(i), printed page 24, and
extends it to all Banach exponents. It does not assert compactness of the inverse
as a map into the stronger domain norm.

For finite `p≥1`, the free resolvent now also maps into `FL^1`. Let `B_p(z)` be
`freeL1Bound p hp z hz`: the maximum of the conjugate-space norms of the two
reciprocal symbols. These are finite by the reciprocal Sobolev-weight estimate.
Hölder and convolution give

`‖Φ R₀(z)‖ ≤ B_p(z) * ‖φ‖`.

Under the explicit sufficient condition `B_p(z) * ‖φ‖ < 1`, the geometric series
converges in operator norm and defines the correction `Q = (1 - Φ R₀(z))⁻¹`.
We prove the factorization `z - L(φ) = (1 - Φ R₀(z)) (z - L₀)` and construct
`Rφ = R₀(z) Q`, with both inverse identities on their correctly typed spaces.
The inverse takes values in the one-derivative domain, is compact on the base
space, and satisfies

`‖Rφ‖ ≤ δ(z)⁻¹ / (1 - B_p(z) * ‖φ‖)`.

This establishes the coefficient-space Neumann construction used before
Corollary 3.3, printed pages 23–24. For `p=1`, `B_1(z) ≤ 1 / |Im z|`, so
`|Im z| > ‖φ‖` suffices. Every `l1` potential therefore has an admissible
parameter; the proof chooses `z = i (‖φ‖ + 1)`.

For every finite `p≥1`, uniform high-imaginary-part regions are now established.
Define `U_p(N)` as the conjugate-space norm of the explicit envelope

`n ↦ min (1 / (N + 1)) (3 / (1 + abs(n)))`.

We prove `U_p(N) → 0` and `B_p(z) ≤ U_p(N)` whenever `abs(Im z) ≥ N + 1`,
uniformly in `Re z`. The proof shifts frequencies by `floor(Re z / π)` and
uses dominated convergence at finite conjugate exponents; the infinite conjugate
exponent uses the uniform height cap directly.

Consequently, every bounded set of potentials has a common height above which
the Neumann condition holds, for both signs of the imaginary part. Every
potential in `PairSpace p`, for any `1 ≤ p < ∞`, has a two-sided inverse into
the one-derivative domain whose base-space realization is compact. The theorem
`exists_compact_inverse` states this without a smallness hypothesis on the
potential.

The envelope proof above establishes qualitative uniform regions. It is now
supplemented by the numerical bounds of Lemma 3.2(ii–iii), proved below using
Appendix B.1. Analytic dependence and spectral discreteness are also established.

The numerical series estimate used in those sharper bounds is now proved:
Appendix B, Lemma B.1 (printed page 124). For real conjugate exponents `p,q > 1`
and `α ≥ 0`,

`∑_{m≥1} (α+m)⁻ᵠ ≤ (q+α)/(q−1) * (1+α)⁻ᵠ ≤ p/(1+α)^(q−1)`.

The proof computes the improper integral and applies the integral test to the
nonnegative decreasing reciprocal-power function. It includes the zero-shift
case, summability, and the explicit tail estimate

`∑_{k≥0} (α+k+N+1)⁻ᵠ ≤ (α+N)^(1−q)/(q−1)` for `α+N > 0`.

The punctured integer lattice is twice the one-sided series, giving bounds
`2q/(q−1) * (1+α)^(1−q)` for `α ≥ 0`, and
`2/(q−1) * α^(1−q)` for `α > 0`. The former bound is also proved around any
integer Fourier center. They are now applied to the inverse one-derivative weight,
proving `sobolevEmbeddingConstant p hp ≤ 2 * p.toReal`, including `p=1`.

Define `verticalStrip n r` by `abs(Re z − πn) ≤ π/2` and `r ≤ abs(z − πn)`.
For `0 < r ≤ π/4`, the denominator geometry gives

`r * (1 + abs(m−n)) ≤ abs(z−πm)`.

Every such strip avoids the free lattice. Fourier recentering and the reciprocal
weight bound imply `freeL1Bound p hp z hz ≤ 2p/r`, and hence the
`FL^p → FL^1` operator estimate `‖R₀(z)‖ ≤ 8p/r` in Lemma 3.2(iii), printed
page 24. The stronger `2p/r` estimate and all pair norms here use the library's
maximum norm; comparison with the dissertation's pair norm remains separate.

When `2p * ‖φ‖ < r`, the Neumann condition holds throughout every punctured
strip. Thus every circle of radius `r` about `πn` lies in the resolvent set.
Choosing a nearest Fourier frequency for each spectral parameter also proves
that the entire periodic spectrum is contained in the union of the open disks
of radius `r` around `πℤ`. This is a uniform small-potential localization result;
localization for arbitrary potentials uses the frequency-tail estimate and
uniform neighborhood construction below.

For nonzero imaginary part, Lemma 3.2(ii), printed page 24, is now proved with
the stated height-decay rate:

`B_p(z) ≤ 4p / abs(Im z)^(1/p) + 1 / abs(Im z)`.

The same bound holds for the free `FL^p → FL^1` resolvent operator. Centering
at a nearest Fourier frequency and removing its coefficient separates a
`1/abs(Im z)` contribution from the tail. The remaining reciprocal denominators
are bounded by `2/(abs(Im z) + abs(m−n))`. Appendix B.1, raised to the conjugate
power, bounds that tail by `4p * abs(Im z)^(-1/p)`. The endpoint `p=1` uses
the earlier supremum estimate. These are bounds in the current maximum norm
on pairs; the physical-space realization and pair-norm comparison remain open.

`heightNeumannRegion φ` is the set where `Im z ≠ 0` and the displayed height
bound times `‖φ‖` is less than one. Every point in this numerical region lies
in the full resolvent set, where the inverse agrees with the constructed
Neumann inverse and is compact and analytic, giving the coefficient-space
assertion of Corollary 3.3. The numerical bound tends to zero as height tends
to infinity. A sufficient height controls every larger absolute imaginary
part, uniformly in real parts and both signs. Every bounded potential set
has a common such height, and the numerical region is nonempty for every
finite-p potential.

The squared Neumann construction preceding Lemma 3.4 is now proved. With
`K = Φ R₀` and `S = R₀ Φ R₀ : PairSpace p →L[ℂ] PairSpace 1`, we have

`K² = potentialFromL1 φ ∘ S` and `‖K²‖ ≤ ‖φ‖ * ‖S‖`.

The explicit criterion `‖K²‖ < 1` yields the correction
`C = (1 + K) (1 - K²)⁻¹`, proved to be both a left and right inverse of
`1 - K`. The geometric series is taken in `K²`, with
`‖C‖ ≤ (1 + ‖K‖) / (1 - ‖K²‖)`. Composition with the free domain inverse
solves both spectral equations and agrees with the full resolvent. In
particular, `‖φ‖ * ‖S‖ < 1` suffices and gives an explicit resolvent bound.
Both raw Fourier coefficient formulas for `S` are proved, retaining the
opposite signs of the two free symbols.

This criterion extends the earlier Neumann construction. For a one-sided
potential (either component zero), `K² = 0` for every parameter off the free
lattice and every potential norm, and the exact resolvent is `R₀ + R₀ K`.
The checked constant potential `(2,0)` at `z=i` has `‖K‖ ≥ 2`, fails the
original Neumann condition, and satisfies the squared criterion.

**Lemma 3.4 is now proved in the coefficient spaces**, with the explicit
constant `c_p = 32p²` in the maximum pair norm. If `0 < r ≤ π/4` and
`z ∈ verticalStrip n r`, then

`‖R₀ Φ R₀‖ ≤ (32p² / r²) * (‖φ‖ / abs(n)^(1/p) + ‖pairFourierTail abs(n) φ‖)`.

The tail retains the boundary frequencies `|k| ≥ |n|`, as in the dissertation.
For nonzero `n`, the proof splits the first reciprocal symbol about `-n`
and the second about `n`, each with window radius `floor(|n|/2)`.
Outside either window the conjugate-space norm is at most
`8p/r * |n|^(-1/p)`, including `p=1`. Inside both windows, convolution can
only use potential frequencies `|j-k| ≥ |n|`. The separate three-term bound
has constants `32p²` for the frequency decay and `4p²` for the potential tail.
The zero strip uses the global composition estimate and its full potential tail.

Multiplying this explicit bound by `‖φ‖` and requiring it to be less than one
puts the entire punctured strip, and its central boundary circle, in the full
resolvent set. The symmetric potential tails converge to zero for every finite
Banach exponent.

**Corollary 3.5 is now proved in the coefficient spaces.** For every potential
`φ` there are a natural cutoff `N` and an open convex neighborhood `U` containing
both `φ` and zero such that every `ψ ∈ U` has resolvent on

`C \ (centralSpectralBox N ∪ highSpectralDisks N (π/4))`.

Here the box has exactly `abs(Re z) < Nπ + π/2` and `abs(Im z) ≤ N`, and the
open disks have centers `nπ` with `|n| > N`. The full resolvent is compact and
analytic on this entire common exterior. Equivalently, the periodic spectrum
of every potential in `U` is contained in the stated box-and-disk union.
The result includes the connected neighborhood containing zero used after
Corollary 3.5; convexity also gives the whole straight line from zero to `φ`.

The construction bounds `‖ψ‖` by `M = ‖φ‖ + 1` and a single tail by
`δ = 1/(4 M C)`, where `C = 32p²/r²`. Tail monotonicity and reciprocal-frequency
decay then give a common squared Neumann bound at most `1/2` in all sufficiently
far strips. The uniform height estimate covers the remaining exterior after
increasing the integer cutoff. On the strict vertical edges of the central
box, the strip argument includes the edge index `|n| = N`; it does not assume
these boundary points lie inside the box.

**Lemma 3.6 is now proved in the coefficient spaces.** The residues `0` and
`1` modulo two define closed complementary subspaces of the scalar and pair
spaces. Contractive coordinate projections give the even/odd decomposition,
including negative indices and the `p=∞` projection endpoint. Transporting the
same masks through the weighted norm gives projections on the operator domain.
The domain parity spaces are closed and agree with the base parity condition
under the canonical inclusion.

For a potential with both components supported on even frequencies,
convolution commutes with each parity projection. The operator therefore
satisfies `Lφ P_domain = P_base Lφ` and preserves both domain parity classes.
The same identity holds for the spectral pencil. Both the full inverse into
the domain and the base-space resolvent preserve parity at every resolvent
parameter. The spectral circle integrals commute with the parity projections
and preserve both subspaces, supplying the invariant spaces used in (1.5).
Both signed free modes have the parity of their spectral index, since `n`
and `-n` have the same residue modulo two.

The physical Fourier realization and canonical period-one embedding remain
open. Identification with a rectangular contour integral remains to be proved.

**The high-frequency disk count in Proposition 1.1(i) is now proved.**
Every free root vector at `π n` has first component supported at `-n` and second
component supported at `n`, by induction on the domain-aware root chain.
The full root space is exactly the range of the injective two-coefficient
embedding, so it equals the ordinary eigenspace and has complex dimension two.
An open disk centered at `π n` with positive radius at most `π` contains exactly this
free spectral value; adjacent lattice points on the boundary are excluded.

Local rank stability now gives constant rank and total enclosed multiplicity on
any preconnected family with a common resolvent circle; openness of the family
is unnecessary. Applying this to the convex neighborhood from Lemma 3.4 proves
that, for any `0 < r ≤ π/4`, every disk about `π n` with `|n| ≥ N` has contour
rank two and total algebraic multiplicity two, uniformly near the chosen
potential and along its deformation to zero. This counts algebraic multiplicity
and does not assert that the two eigenvalues are distinct.

**The parity assertion in Proposition 1.1(i) is also proved.** A bounded
nonzero projection has norm at least one. The intermediate value theorem
therefore shows that a continuous family of projections on a preconnected
set remains zero if it is zero at one point; finite rank is unnecessary.
For a fixed commuting projection `A`, this transports `A P = P` along the
family. Apply this with `A` the projection onto index parity `n`, using the
free contour range as the starting point and intersecting the convex
potential neighborhood with the even subspace.

Consequently, the whole contour range, every enclosed full root space,
and every enclosed eigenfunction in the weighted domain have parity `n`.
A contour with this range annihilates every input of the opposite parity.
One cutoff and one open convex ambient neighborhood supply both multiplicity
two and the parity statement, the latter conditional on the nearby potential
being even-supported. This is the coefficient-space periodic/antiperiodic
distinction; its physical Fourier interpretation remains separate.

**The central boundary and free central count are now proved.** The fully
closed and open central rectangles are defined alongside the dissertation's
mixed-boundary box. Their compact boundary includes all four edges and corners.
The proof retains a positive integer height from the uniform Neumann estimate,
so the horizontal edges themselves are resolvent points; this does not follow
from exterior inclusion because those edges belong to the mixed-boundary box.
The vertical edges lie in strips centered at `±N`. One open convex neighborhood
containing the potential and zero works for every larger cutoff, simultaneously
for all boundary points, exterior points, and farther spectral circles.

When the boundary is in the resolvent set, the open, closed, and mixed rectangles
contain exactly the same spectrum. The finite central spectrum is therefore
well-defined without boundary ambiguity. For the free potential it is exactly
the image of the integer interval `[-N,N]` under `n ↦ π n`, and the sum of
algebraic multiplicities is `4N+2`. The central algebraic spectral projection is
constructed as the finite cluster projection: it is compact and idempotent,
its rank is the central multiplicity sum, and its free rank is `4N+2`.

**The total central count in Proposition 1.1(ii) and its analytic deformation
are now proved for general potentials.** Starting from localization with
cutoff `N`, choose any `K ≥ 2N+1`. The circle of radius `πK+π/2` stays at least
`π/2` from every free lattice point and lies outside the original central box.
It is therefore uniformly in the resolvent set. On the localized spectrum,
this circle and the box `B_K` select exactly the same parameters: the original
central part lies inside both, and the other disks are selected precisely when
`|n| ≤ K`. This argument does not assume geometric containment of all corners
of `B_K` by its associated circle.

Equality of the finite selected spectra proves equality of the entire central
and circle projection operators. Their local equality on an open neighborhood
gives analytic dependence of the central projection. Circle rank stability
along the convex neighborhood containing zero then gives rank `4K+2`, hence
the same total central algebraic multiplicity. One neighborhood works for every
cutoff above the threshold.

**The central parity split in Proposition 1.1(ii) is now proved.** The central
indices with residue `r` have cardinality `N+1` when `N` has that residue and
`N` otherwise. This is proved by adding the two signed endpoints at each
cutoff, including the base case `N=0`. On each free root space, the pair parity
projection selects or kills both signed modes together. Thus the free central
parity projection is the spectral cluster filtered by those indices, with
rank `2N+2` or `2N`.

Rank is now proved constant on any continuous preconnected family of
finite-rank projections, including families defined on a parameter subspace.
Intersecting the potential neighborhood with the even subspace and using
commutation with the large-circle projector transfers the free parity ranks.
The component ranges are exactly the intersections of the full central
spectral space with the corresponding parity subspaces. Hence for even `N`,
the even/odd dimensions are `2N+2`/`2N`; for odd `N`, they are `2N`/`2N+2`.
The total count, parity dimensions, and analytic central and parity-component
projection families share one open convex neighborhood and one threshold,
valid for every larger cutoff. The physical Fourier interpretation and
characteristic-function zero-order interpretation are still separate.

**The coefficient-space localization and counting conclusions now share one
cutoff and neighborhood.** `exists_uniform_periodicCountingData` gives a positive
threshold and an open convex neighborhood containing the potential and zero.
For every potential in that neighborhood and every larger cutoff, the record
`PeriodicCountingData` supplies the exterior and boundary resolvents, central
rank and multiplicity `4N+2`, high-disk rank and multiplicity two, and the parity
conclusions for even-supported potentials. Central, parity-component, and high-disk
projections are analytic on this same neighborhood.

Distinct quarter-pi disks are disjoint, and every high disk is disjoint from
the central box. Every spectral value belongs either to the finite central
cluster or to exactly one high disk. Each high disk contains one double value
or two distinct simple values; `disk_eigenvalue_pair` returns the corresponding
unordered pair, allowing repetition. Root-space and eigenfunction parity follow
from the same counting data.

This uses Corollary 3.5's height-`N` central box. The overview's Theorem 1.1 uses
a norm-dependent height; transferring that exact numerical convention, as well
as the physical Fourier realization and pair norm, remains a separate obligation.

**The real-type clause (iv) is now proved in coefficient space.** Real type means
`φ₂(n) = conj(φ₁(-n))`, including the reversal of Fourier frequency. For every
finite `p≥1`, domain coefficients lie in `l1` and potential coefficients are
bounded. The pairing `∑ a(n) conj(b(n))` therefore converges absolutely, as does
the double convolution pairing, bounded by the product of the two domain
`l1` norms and the potential norm. Exchanging the two summation indices proves
the adjoint identity for conjugate-reflected kernels.

The real diagonal symbols and off-diagonal adjoint identity imply
`domainPairing (Lφ f) g = conj(domainPairing (Lφ g) f)` for every pair of domain
vectors. The inclusion pairing of a nonzero vector with itself has strictly
positive real part: it is the sum of squared coefficient magnitudes. Applying
symmetry to an eigenvector gives `z E = conj(z) E` with `E ≠ 0`, hence `Im z = 0`.
The previously proved eigenvector characterization extends this conclusion to
the entire periodic spectrum. Every nonreal parameter is consequently in the
full resolvent set, with no amplitude restriction and no restriction to `p≤2`.
Physical Fourier identification remains separate; no self-adjointness or
Hilbert-space spectral theorem is assumed.

**The local analytic reduction in Lemma 3.7 is constructed.** For projections
`P,Q`, the explicit transport `T = QP + (1-Q)(1-P)` satisfies `QT = TP` and
is the identity at `Q=P`. Banach-algebra inversion gives a neighborhood where
`T` is invertible and both `T` and its inverse vary analytically. The resulting
continuous linear equivalence maps the whole reference range onto the varying
range, including nonorthogonal projections.

The contour projection is now analytic with values in operators into the
one-derivative domain. Consequently `Aφ = Lφ P_D,φ` is a bounded analytic
operator on the base space. The contour projection intertwines `Lφ` with its
domain lift, and `Pφ Aφ = Aφ Pφ = Aφ`. Thus `Aφ` is the actual spectral
restriction, retaining its action on every enclosed eigenvector.

The operator `P₀ Tφ⁻¹ Aφ Tφ`, restricted to the fixed reference range, is
analytic in operator norm. It satisfies the exact intertwining identity with
`Aφ`, and at the reference potential it equals the original spectral restriction.
An open neighborhood supports the transport, its inverse, the reduced operator,
and the range equivalences simultaneously. For the high-frequency circles,
the earlier disk count makes the reference range two-dimensional.

**Lemma 3.7 is now proved in coefficient space.** The range equivalence
conjugates each local reduction to the intrinsic restriction at the current
potential. Traces of every power are invariant under this equivalence. Since
trace is a bounded linear functional on the fixed finite-dimensional operator
space, these intrinsic power traces are analytic wherever the circle is
admissible.

The intrinsic restriction has exactly the eigenvalues enclosed by the contour.
For the forward implication, its nonzero eigenvector lifts into the weighted
domain and satisfies the original eigenvalue equation. A value outside the
closed disk would have its root vector annihilated by the same projection,
contradicting its range membership. Boundary values are resolvent points.
Conversely, each enclosed eigenvector is fixed by the projection and becomes
an eigenvector of the restriction.

In dimension two, the characteristic polynomial is `(X-a)(X-b)`, allowing
`a=b`. Cayley–Hamilton and trace linearity give `Tr A = a+b` and
`Tr A² = a²+b²`. Thus the intrinsic definitions

- `τ = Tr A / 2`;
- `γ² = 2 Tr A² - (Tr A)²`

are exactly `(a+b)/2` and `(a-b)²`. The source's centered identity
`Tr (A-τI)² = γ²/2` is proved as well. No diagonalization or analytic labeling
of individual eigenvalues is assumed. `periodicMidpoint` and
`periodicSquaredGap` use the quarter-pi disks; one positive cutoff and open
convex neighborhood support their analyticity for every high index, the full
counting data, and eigenvalue pairs with the correct algebraic multiplicities.
For the free potential, the midpoint is `π n` and the squared gap is zero
at every signed index.

**Section 4's coefficient boundary spaces and operator invariance are proved.**
With frequency reflection `J a(n) = a(-n)`, Dirichlet amplitudes embed as
`(J a,a)` and Neumann amplitudes as `(-J b,b)`. Both graphs are closed and
complementary, with isometric scalar amplitude coordinates in the maximum pair
norm. Their projections are contractive. The same construction works for every
real Sobolev regularity, including the one-derivative operator domain, and the
domain projections commute with inclusion into the base space.

The free modes `Eₙ^dir = eₙ⁺+eₙ⁻` and `Eₙ^neu = eₙ⁺-eₙ⁻` are nonzero and have
free eigenvalue `π n`. For a potential already satisfying `φ₋ = J φ₊`, potential
multiplication sends these modes to the Dirichlet embedding of
`shift(-n) φ₊`, respectively the negative of the Neumann embedding of that
amplitude. The full operator preserves both spaces and intertwines their
projections. Its restrictions are bounded from the respective weighted domains
into the base subspaces, with the existing explicit operator bound.

This proves the coefficient content of Lemma 4.4 for every finite Banach
exponent, including `p=1`, under the already-reflected-potential hypothesis.
The physical endpoint interpretation and Sobolev-domain isomorphisms in
Lemmas 4.1–4.2 remain open. The later finite interval-extension construction
below connects physical integrals to these base coefficient spaces, but the
uniform discrete-Hilbert-transform estimate in Lemma 4.3 is now proved at
`p=2` below; the other exponents in `1<p<∞` still require proof.

**The full boundary resolvents and spectral decomposition are proved.**
`BoundaryCondition` selects either restriction without changing its operator.
Each resolvent set consists exactly of the parameters at which that restriction's
pencil is bijective. A fixed free inverse at `i` normalizes each pencil to a
bounded endomorphism. Banach-algebra inversion then supplies the full
boundary-domain inverse, extended by zero only outside its own resolvent set.
Both inverse identities are proved. The base resolvents are compact and jointly
analytic on their open domains in the reflected potential space and parameter.

The periodic resolvent set is the intersection of these two resolvent sets,
and the periodic spectrum is exactly the union of the boundary spectra. Each
boundary spectrum is closed, discrete and finite in every bounded region.
Transformation to the nonzero spectrum of a compact boundary resolvent proves
that every boundary spectral point has an eigenvector in that boundary domain.
On the common periodic resolvent set, the boundary inverses equal the restrictions
of the periodic inverse. The periodic resolvent and the circle projectors commute
with both boundary projections and preserve both subspaces.

The distinction between the individual and common resolvent sets matters:
for the constant potential `(1,1)`, `1` is a Dirichlet eigenvalue but a Neumann
resolvent point. The Neumann inverse is proved nonzero and analytic there.

**Boundary root spaces and free algebraic counts are proved.** Each root chain
is defined recursively using the actual boundary pencil and inclusion, requiring
a boundary-domain representative at every step. Its image in the periodic base
space is exactly the intersection of the periodic root space with that boundary
space. This holds at every finite level and for the full root space. Finite
dimension, stabilization, closedness, and domain representatives follow.
Algebraic multiplicity is the dimension of the full root space; it is positive
exactly on the boundary spectrum and zero on the individual resolvent set.

The boundary projections preserve every periodic root level, giving a direct
sum decomposition of both finite and full periodic root spaces. Consequently,
periodic algebraic multiplicity equals Dirichlet plus Neumann multiplicity,
including at eigenvalues with Jordan chains. Both free boundary spectra equal
the signed lattice `πℤ`. Nonzero free modes and periodic multiplicity two give
multiplicity one in each boundary space, with no longer free chains. Each free
quarter-pi contour has rank one in either summand; the free central sum is
`2N+1` for either boundary condition.

**The coefficient counting argument of Theorem 1.4 is proved.** Commutation with
one resolvent implies commutation with every individual periodic spectral
projection. Thus boundary projections commute with every finite cluster, and
the boundary cluster space is precisely the boundary part of the periodic
cluster. These spaces are finite sums of actual restricted root spaces, with
bounded projections on the boundary space itself as well as the periodic
ambient space. Their ranks are sums of the full boundary algebraic
multiplicities; no diagonalizability assumption is used. Circle components
have exactly the corresponding cluster ranges and inherit operator-norm
analyticity from the periodic contour.

The finite boundary spectra are filtered from the periodic spectra, with exact
membership characterizations. Removing points outside an individual boundary
spectrum leaves its multiplicity sum unchanged. `BoundaryCountingData` connects
these actual spectral sets and multiplicities to the projection ranks. Rank
constancy on the reflected part of a convex neighborhood containing zero and
the given potential proves the nonzero-potential counts: `2N+1` central values
counted algebraically and one simple value per high disk for each boundary
condition. Both counts, the analytic central and disk projector families, and
periodic localization share one neighborhood and work for every larger cutoff.
Singleton disk spectra and algebraic multiplicity one are proved explicitly.

**The coefficient form of Lemma 4.5 is proved.** The boundary contour projector
has an analytic lift into the actual one-derivative boundary domain. Inclusion
recovers the base projector, and the lift is unchanged by first applying that
projector. The original operator composed with the lift gives a bounded
analytic operator supported on the same finite-dimensional spectral range.
On every enclosed boundary eigenvector, the lift returns the original domain
vector and the bounded operator has exactly its original eigenvalue action.

The general `ProjectionTrace` construction takes the trace on a varying range,
using projection transport to prove independence of the local reference range
and analyticity for any commuting analytic operator family. On a one-dimensional
range, this trace is the eigenvalue of a nonzero eigenvector. Applying it to
the boundary restriction defines the Dirichlet and Neumann high-index functions.
Their trace formulas agree with the unique simple values already obtained from
`BoundaryCountingData`; the functions have free values `πn` and actual nonzero
weighted-domain eigenvectors. Both are analytic on one open convex neighborhood
of reflected potentials containing the given potential and zero, with the same
cutoff and counting data for every larger central box. The total trace definition
has an eigenvalue interpretation under these rank-one hypotheses.

The uniform interval-extension estimates remain necessary to transfer
Theorem 1.4 and Lemma 4.5 to the original period-one potentials.

**Physical interval extensions are constructed for finite Fourier input.**
The piecewise map retains the input on `[0,1]` and swaps its components at
`2-x` on `(1,2]`, with a plus sign for Dirichlet and a minus sign for Neumann.
Its normalized period-two Fourier integrals are proved by splitting the
interval and changing variables; the join point does not require continuity
of the extension. No global periodic or physical Sobolev realization is asserted.

For raw period-one input coefficients `(u,v)`, the even boundary amplitude at
`2l` is `(v(l)+εu(-l))/2`. The odd amplitude is the finite sum of
`v(k)i/[π(2k-2l-1)] + εu(k)i/[π(2k+2l+1)]`. The first component uses raw
negative frequencies consistently with the existing signed boundary modes.
These constants follow from equations (1.8)–(1.9), including the factor `1/2`.
The calculation on printed page 31 omits that half-normalization and the odd
kernel's `π` denominator. In particular, the Dirichlet extension of `(1,1)`
has zeroth coefficient `1`; the printed even formula would give `2`.

The overlap kernel obeys `|K(n)| ≤ 2/(1+|n|)` and belongs to every `ℓp` with
`p>1`. Finite linear combinations of its shifts therefore define actual
`PairSpace p` elements, with proved linearity, selected boundary membership,
and equality of both component sequences with the physical Fourier integrals.
This finite-input construction also works at `p=∞`, without claiming a uniform
`ℓ∞` input bound. For either boundary condition the constant input `(0,1)` has
odd amplitude `-i/[π(2l+1)]`; comparison with the harmonic series proves its
physical coefficient sequence is not in `ℓ1`.

Kernel membership and finite synthesis alone do not justify completion by
density. The uniform estimate at `p=2` is now proved using Parseval as follows;
the full-range Hilbert bounds established below must still be assembled into
the interval-map estimate for other exponents. Only boundedness of the relevant
discrete Hilbert transform is needed; no invertibility assertion from Appendix C.1
is assumed.

**The uniform Hilbert-space interval extension is proved.** The actual
period-two coefficient integrals agree with mathlib's interval Fourier
coefficients. Parseval computes the energy of each finite period-one polynomial.
Splitting at the reflected join gives the sum of the two input energies, even
when that join has a jump. Thus, for either boundary sign, the output amplitude
has squared `ℓ2` norm `(‖u‖²+‖v‖²)/2`. The reflected pair has exactly the
amplitude norm, so the finite extension is contractive in the maximum pair norm,
with a bound independent of Fourier support.

The canonical finite coefficient inclusion has dense range at every finite
Banach exponent. At `p=2`, the uniform bound constructs
`hilbertIntervalExtension : PairSpace 2 →L[ℂ] PairSpace 2`. It agrees with the
physical Fourier formulas on polynomial input and is the unique continuous
linear map with that agreement. Closedness carries boundary membership and
the exact energy identity to arbitrary coefficient pairs. The latter also
proves injectivity. Physical Sobolev-domain identification and surjectivity
onto the boundary space are not asserted by this construction.

Odd-index sampling is a contraction on `ℓ2`. Applied to the second component
of the completed extension of `(0,a)`, and multiplied by `-2i`, it gives
`shiftedHilbert : Coeff 2 →L[ℂ] Coeff 2`, with norm at most `2`. Its finite-input
formula is `Σₖ a(k) 2/[π(2k-2n-1)]`, the shifted reciprocal transform needed in
Lemma 4.3. This bound is sufficient and is not claimed optimal. The argument
below proceeds through quartic, dyadic, and conjugate exponents to full-range
Hilbert boundedness. Interval completions beyond `p=2` remain open.

**Ordinary and shifted Hilbert transforms are bounded on `ℓ4`.** The ordinary
source kernel is `h(j)=-1/j`, with `h(0)=0`. Its difference from the unnormalized
shifted kernel is `d(0)=2` and `d(j)=-1/[j(2j+1)]` elsewhere. The proved bound
`|d(j)|≤4/(1+|j|)²` puts it in `ℓ1`, so its convolution is bounded even at
`p=1` and `p=∞`. Adding it to `π` times the shifted `ℓ2` operator constructs
the actual ordinary transform, with coefficient `Σₖ a(k)/(k-n)` on finite input.
The diagonal term is zero. One uniform constant is `B₂=2π+‖d‖₁`.

The scalar partial-fraction identity explicitly handles every collision of
indices. Summing it proves the discrete Cotlar identity
`(Ha)²=2H(aHa)+R(a²)+2aRa`, where `R` has convolution kernel `h(j)²`.
Products retain the finite support of `a`; both correction terms are necessary.
The square kernel is in `ℓ1`, and `R` is bounded at every Banach exponent.
Hölder constructs the actual `ℓ4 × ℓ4 → ℓ2` product with norm at most one;
its square product has norm exactly `‖a‖₄²`.

Finite Hilbert images already belong to `ℓ4` by the reciprocal kernel bound,
independently of any uniform estimate. The Cotlar identity therefore gives
`x²≤2B₂yx+3My²`, with `x=‖Ha‖₄`, `y=‖a‖₄`, and `M=‖h²‖₁`. Solving it proves
`x≤B₄y` for the explicit constant `B₄=2B₂+3M+1`. Dense finite coefficient
inclusion constructs `discreteHilbertFour` on all `Coeff 4`, and subtraction of
the same correction constructs `shiftedHilbertFour`, with bound
`(B₄+‖d‖₁)/π`. Both maps have the exact finite-input reciprocal formulas.
This proves the quartic Hilbert-kernel step; it does not yet complete the
quartic interval map or prove the whole exponent range in Lemma 4.3.

**Exponent doubling is proved and iterated at every dyadic exponent.**
`HilbertEstimate p` packages a uniform finite-input bound together with
`1<p<∞`. Density constructs its unique continuous ordinary transform; subtracting
the same summable correction gives the normalized shifted transform. Both retain
the exact finite formulas, and uniqueness makes the ordinary operator independent
of the bound or proof used to construct it.

Hölder now constructs `ℓq × ℓq → ℓp` for general doubled exponents `q=2p`,
with exact square norm `‖a²‖p=‖a‖q²`. The old quartic product specializes this
construction. The general Cotlar inequality is `x²≤2Byx+3My²`, and its proved
solution gives the uniform bound `2B+3M+1`, including zero input. This produces
an actual `HilbertEstimate q`, so the argument can be iterated.

At exponent `2^(n+1)`, `dyadicHilbert` and `dyadicShiftedHilbert` are continuous
linear operators on the entire coefficient space. The ordinary bound is
`Cₙ=2^n B₂+(2^n-1)(3M+1)` and the shifted bound is `(Cₙ+‖d‖₁)/π`.
The proved exponents exceed every prescribed real number. Duality and
interpolation then supply the whole range `1<p<∞`, as described next.

**Hilbert bounds transfer to conjugate exponents without increasing the constant.**
The bilinear coefficient pairing `Σ a(n)b(n)` is a continuous map on conjugate
sequence spaces, with the Hölder norm bound. Mathlib's finite nonnegative Hölder
extremizer, combined with complex phases, constructs a finite conjugate test of
norm at most one realizing the norm of each truncation. Truncation convergence
then proves that bounds against all finite conjugate tests detect the full norm.
Zero coefficients and empty truncations are included.

The finite ordinary kernel is antisymmetric, including the zero diagonal, giving
`Σ(Ha)b = -Σa(Hb)`. Combining it with norm detection transfers a proved finite
estimate at `q` to conjugate `p`, with exactly the same bound. The resulting
`HilbertEstimate.conjugateTo` supplies the unique completed ordinary transform
and its shifted correction. Double density extends the transposition identity
to arbitrary inputs in the two conjugate spaces.

Applying this to every dyadic estimate constructs `conjugateHilbert` and
`conjugateShiftedHilbert` at `rₙ=2^(n+1)/(2^(n+1)-1)`. Their bounds are `Cₙ` and
`(Cₙ+‖d‖₁)/π`, respectively, and their finite-input coefficients retain the exact
reciprocal formulas. Every `rₙ` lies in `(1,2]`, and for every real `r>1` some
`rₙ<r`. Thus proved exponents occur arbitrarily close to one as well as arbitrarily
far above two. Interpolation between them is now established as follows.

**Ordinary and shifted Hilbert transforms are bounded for every `1<p<∞`.**
For a nonzero complex coefficient `a`, the analytic power curve is its phase
`a/‖a‖` times `exp(w log ‖a‖)`; zero coefficients stay identically zero. It is
entire in `w`, has norm `‖a‖^(Re w)` when `Re w>0`, and recovers `a` at `w=1`.
Applying it coefficientwise preserves a fixed finite support. The affine weight
`r((1-z)/p₀+z/p₁)` gives endpoint unit norms when the original input has `ℓr`
norm at most one, with no restriction on the imaginary part of `z`.

The finite kernel pairing of two such families is entire and uniformly bounded
on the closed unit strip by a finite sum of kernel magnitudes. Endpoint operator
and Hölder bounds control the two edges. Mathlib's three-lines theorem then gives
the interior bound `max(B₀,B₁)`; this sufficient constant is not claimed optimal.
The conjugate reciprocal exponents use the same interpolation parameter.
Finite conjugate unit tests detect the output norm, and rescaling gives the
support-independent estimate for arbitrary finite input. Density turns it into
`HilbertEstimate.interpolate` on the entire intermediate coefficient space.

An intermediate-value argument supplies the interpolation parameter whenever
proved exponents bracket the desired one. The dyadic and conjugate families
bracket every finite `p>1`. Consequently, `hilbertTransform` and
`shiftedHilbertTransform` are continuous linear maps on every `Coeff p` in that
range, with ordinary bound `hilbertTransformBound` and shifted bound
`(hilbertTransformBound+‖d‖₁)/π`. Uniqueness identifies the ordinary construction
with all previous estimates at the same exponent; full conjugate transposition
continues to hold.

The series definitions are identified on all inputs as well. Ordinary
single-mode Hilbert images and reflected shifted single-mode images in the
conjugate space represent the two coefficient functionals. Hölder proves
absolute convergence of `Σ a(k)/(k-n)` and
`Σ a(k) 2/[π(2k-2n-1)]`. Density proves that these series equal the completed
ordinary and shifted output coefficients for arbitrary inputs. This establishes
the boundedness needed from Appendix C.1. Its additional invertibility assertion
is not used. Completing the physical interval maps beyond `p=2` remains open.

The actual unbounded realization is now defined as

`unboundedOperator hp φ : PairSpace p →ₗ.[ℂ] PairSpace p`.

Its domain is exactly the range of `domainInclusion`, independently of the
potential, and its evaluation agrees with `operator hp φ`. It is densely defined
and closed for every finite Banach exponent. For any constructed two-sided
inverse `R` at `z`, its graph is characterized by the base-space equation

`domainInclusion (R (z • x - y)) = x`.

Continuity of this equation proves graph closedness. The accompanying limit
lemma shows that if included domain vectors converge to `x` and their operator
images converge to `y`, then `x` has a domain representative with image `y`.
This establishes the coefficient-space closedness assertion on printed page 23.

The full resolvent set `resolventSet hp φ` is now defined by bijectivity of the
spectral pencil, with no exclusion of the free lattice. Normalizing the pencil
by the fixed free inverse at `i` gives an endomorphism of `PairSpace p`;
bijectivity of the pencil is equivalent to invertibility of this endomorphism.
Banach-algebra inversion then defines `resolventToDomain hp φ z` and its included
base-space version `resolvent hp φ z`. Both functions are extended by zero outside
the resolvent set; inverse identities and analyticity are asserted only on it.

The joint domain `{(φ,z) | z ∈ resolventSet hp φ}` is open. On that domain,
the resolvent is jointly complex analytic in `(φ,z)`, in operator norm, both
into the one-derivative domain and into the base space. In particular it is
analytic in `z` for each fixed potential, as in Corollary 3.3, printed page 24.
It agrees with the constructive Neumann inverse wherever the Neumann condition
holds, so every potential has a nonempty resolvent set. The full base-space
resolvent is compact by factoring through the fixed compact free resolvent.
These results establish compactness and analytic dependence throughout the full
coefficient-space resolvent set; the corollary's specific numerical region
remains an open proof obligation.

The periodic coefficient-space spectrum is now defined as the complement of
the full resolvent set. At any fixed resolvent point `w`, we prove, for `z ≠ w`,

`z ∈ periodicSpectrum hp φ ↔ (w-z)⁻¹ ∈ spectrum ℂ (resolvent hp φ w)`.

The generic compact-operator argument is proved using Riesz's lemma on the
successive finite-dimensional spans of eigenvectors. Infinitely many distinct
eigenvalues bounded away from zero would produce bounded vectors whose compact
images stay a fixed distance apart. Together with mathlib's Fredholm alternative,
this gives finiteness of the compact spectrum away from zero, with no
self-adjointness hypothesis. Nonzero compact-operator eigenspaces are also
proved finite dimensional by compactness of their identity map.

The spectral transformation implies that every bounded part of the periodic
spectrum is finite. The spectrum is closed and has the discrete subspace topology;
every spectral point has a nonzero eigenvector in the one-derivative domain.
The domain eigenspaces embed into nonzero eigenspaces of the compact resolvent,
so their geometric multiplicities are finite. This proves the coefficient-space
discreteness conclusion of Corollary 3.3. Generalized eigenspaces, algebraic
multiplicities, and spectral projections are constructed below. The uniform
box-and-disk localization for arbitrary potentials is proved above.

The general inverse difference formula is now proved for simultaneous changes
of potential and spectral parameter. It specializes to

`Rφ(z) - Rφ(w) = (w-z) Rφ(z) Rφ(w)`

and commutation of the resolvents. Varying the potential at a fixed parameter gives

`Rφ(z) - Rψ(z) = Rφ(z) Φ(φ-ψ) R_D,ψ(z)`.

Here `R_D` takes values in the one-derivative domain, so each potential operator
is applied on its actual domain. Differentiating the inverse equations proves
the explicit joint complex Fréchet derivative in operator norm. Applied to an
increment `(δφ,δz)` and a base vector `a`, it is

`Rφ(z) (Φ(δφ) (R_D,φ(z) a)) - δz • Rφ(z) (Rφ(z) a)`.

The domain-valued derivative is proved as well. In particular,
`∂z Rφ(z) = -Rφ(z)²` and `Dφ Rφ(z)[ψ] = Rφ(z) Φ(ψ) R_D,φ(z)`.
These formulas are available through both derivative predicates and mathlib's
`deriv`/`fderiv`. All derivative assertions are restricted to the open full
resolvent domain. The zero-potential inverse agrees with the free inverse, and
the pre-Neumann identity on printed page 23,
`Rφ(z) (I - Φ R₀(z)) = R₀(z)`, now holds whenever both resolvents exist,
without imposing the sufficient Neumann smallness condition.

Periodic root spaces are now defined directly from the unbounded operator:

`G₀(z) = {0}`, `Gₙ₊₁(z) = {domainInclusion f | (z-L)f ∈ Gₙ(z)}`.

The definition enforces one-derivative domain membership at each step, and
contains no choice of reference parameter. Its first level is the included
ordinary eigenspace. For every resolvent point `w`, we prove

`Gₙ(z) = ker (I + (z-w) Rφ(w))ⁿ`.

Equivalently, these are the generalized eigenspaces at `-1` of the compact
operator `(z-w) Rφ(w)`. This representation remains valid at `z=w`.
The full root space is the increasing union of all finite levels.

The generic compact-operator proof establishes finite-dimensional generalized
eigenspaces and finite stabilization at every nonzero value. Finite-level
dimensionality follows by removing the constant term from a shifted operator
power; stabilization follows from Riesz vectors in successive kernels and
compactness. Consequently, each periodic full root space is finite dimensional,
closed in the base space, and reached at a finite level. Its dimension defines
`periodicAlgebraicMultiplicity hp φ z`, which is positive exactly on the periodic
spectrum and zero exactly on the resolvent set.

Bounded projections onto these full root spaces are now constructed. For any
stabilized exponent `n` and resolvent point `w`, the root space and
`range (I + (z-w) Rφ(w))ⁿ` are topologically complementary. The generic proof
compresses a shifted power to an arbitrary complement of its finite-dimensional
kernel, applies the Fredholm alternative, and constructs a bounded projection.
It requires no self-adjointness.

`periodicSpectralProjection hp φ z` has exactly the full root space as its range,
is idempotent and compact, and has rank equal to the algebraic multiplicity.
It commutes with every resolvent. Changing the reference resolvent point gives
the same projection; one stabilized exponent describes its kernel at every such
point. Every base vector has a unique decomposition into a root vector and a
vector in the closed projection kernel. The projection is zero exactly on the
resolvent set.

Distinct full root spaces are now proved disjoint by representing them as
generalized eigenspaces of the same resolvent at distinct reciprocal values.
Any bounded map commuting with that resolvent preserves every full root space.
Consequently, projections at distinct parameters annihilate each other, and
all individual spectral projections commute.

For a finite set `s` of parameters, `periodicClusterSpace hp φ s` is the sum of
the associated root spaces and `periodicClusterProjection hp φ s` is the sum of
their projections. We prove that it is bounded, idempotent, and compact, has
exactly the cluster space as its range, and has kernel equal to the intersection
of the individual kernels. It commutes with every resolvent, and its rank is
`∑ z ∈ s, periodicAlgebraicMultiplicity hp φ z`. Cluster and kernel form a
topological direct sum with unique decomposition of every base vector.
Multiplying cluster projections selects their intersection; disjoint clusters
therefore have annihilating projections. Parameters in the resolvent set
contribute zero, so no separate spectral-membership assumption is needed.

The actual normalized circle integral is now defined as

`resolventCircleIntegral hp φ c r = (2πi)⁻¹ • ∮ ζ in C(c,r), Rφ(ζ)`.

For a nonnegative-radius circle contained in the resolvent set, circle
integrability is proved in operator norm. A second integral valued in the
one-derivative domain gives a bounded factorization through `domainInclusion`,
which also proves compactness. A uniform bound `M` on the resolvent along the
circle gives the bound `r*M` on the normalized integral. The contour operator
vanishes if the closed disk is contained in the resolvent set; changing the
radius through a closed annulus of resolvent points leaves it unchanged.

The root-chain recurrence gives a weighted integral formula for every finite
root space: all higher pole terms integrate to zero, leaving the simple-pole
term. Consequently the contour operator fixes full root vectors at values
inside the circle and annihilates those outside the closed disk. It commutes
with every resolvent and every individual algebraic spectral projection. For
any finite parameter set `s`, its product with `periodicClusterProjection s` is
the cluster projection filtered to the open disk. Boundary parameters are
resolvent points and have zero algebraic projection.

The Cauchy–Riesz projection properties from Section 3, equation (1.4), are now
proved. For two concentric resolvent circles with `0 ≤ r < R`, the product of
their contour operators is the inner operator. The proof exchanges circle
integrals of a continuous function on the product of circles and uses the
resolvent identity plus the scalar Cauchy integral formulas. The annulus between
the two circles need not be free of spectrum for this product law.

Every resolvent circle has a slightly larger resolvent annulus, using local
spectral finiteness and a positive radial gap. Radius deformation then proves
idempotence. Its range is the eigenspace at one of a compact operator and is
therefore finite dimensional; range and kernel form a topological direct sum.

`enclosedPeriodicSpectrum hp φ c r` is the finite set of spectral values in the
open disk. The finite-dimensional contour range is invariant under any reference
resolvent, so its restriction decomposes into generalized eigenspaces over `ℂ`.
Injectivity excludes a generalized eigenvalue at zero. The reciprocal spectral
transformation and contour selection law identify the range with the sum of
the enclosed periodic root spaces. Consequently the contour integral equals
`periodicClusterProjection hp φ (enclosedPeriodicSpectrum hp φ c r)` as a bounded
operator on the entire base space. Its rank is the sum of enclosed algebraic
multiplicities, and its kernel is the intersection of the corresponding
individual projection kernels. Circles with the same enclosed spectral values
give equal operators, even with different centers; an isolated single value
gives its individual root-space projection.

For any fixed circle, the potentials whose resolvent set contains the entire
circle form an open set. The normalized spectral pencils along that circle
form an affine analytic family in the Banach algebra of continuous
operator-valued functions with the uniform norm. Pointwise invertibility is
invertibility in this algebra. Analytic inversion, followed by bounded linear
circle integration, proves operator-norm analytic dependence of the contour
projection on the potential. The integration map has norm at most the radius.

If two bounded projections are less than one apart in operator norm, each is
injective on the range of the other. For finite-rank projections this implies
equal rank. Consequently, near any admissible potential, the circle remains
in the resolvent set and both the contour rank and total enclosed algebraic
multiplicity stay constant. Individual spectral values may move or split.
These statements implement the fixed-contour analytic-dependence assertion
used with Section 3, equation (1.4). The spectral circles are now uniformly
admissible at all sufficiently large frequencies on a common neighborhood
of any potential, by the uniform strip result above. The high-frequency
free-to-perturbed rank counts are proved. The central boundary is admissible
as described above. The central projection equals a large-circle integral,
and its perturbed rank count is now proved. Identification with the integral
over the rectangular boundary remains separate.
Agreement of multiplicities with characteristic-function zero orders remains open.

The weighted topology is induced by the weighted `lp` norm. A type synonym
prevents accidental inheritance of pointwise convergence from raw sequences.

## Verification

Run `./scripts/check.sh` to build, check public-API examples, and audit transitive
axioms. The current audit covers 2304 declarations under `NLS`, including generated
definitions and instances. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed.

The examples exercise multiplication at `p=1,2,3`, convolution and differentiation
at `p=∞`, domain density at `p=1`, the operator bound at `p=3`, the frequency-shift
sign, both signed free spectral equations, and nonzero off-diagonal coupling.
Resolvent checks use the concrete parameter `z=i`, exercise both inverse identities,
the bounds, compactness at `p=1,3,∞`, cutoff convergence, signed-mode denominators,
and the resolvent identity. Perturbation checks cover the Hölder and convolution
bounds at `p=3`, convergence of the Neumann series, and a concrete nonzero
potential with both entries equal to one at `z=2i`: both inverse identities,
compactness, and the norm bound are checked. Uniform-estimate checks exercise
`p=1,3`, a parameter with a far-negative real part, one height for a whole norm
ball, and compact inverse existence for an arbitrary `p=3` potential. Closed-operator
checks cover `p=1,3`, domain density, evaluation on included vectors, and preservation
of the graph under sequential base-norm limits. Analytic-resolvent checks cover
`p=1,3`, the open joint domain, nonempty resolvent sets, joint and separate
analyticity, both full inverse identities, compactness, and agreement with the
concrete nonzero Neumann example at `z=2i`. Spectral checks cover `p=1,3`,
finiteness in balls and arbitrary bounded sets, the discrete topology, domain
eigenvectors, finite geometric multiplicity, the free Fourier eigenvalues, and
the spectral transformation at the nonzero test potential. Calculus checks
cover `p=1,3`, general differences, commutation, joint derivatives into both
spaces, the potential derivative, the spectral derivative sign on the zero
Fourier mode at `z=i`, and the pre-Neumann identity for the nonzero potential.
Root-space checks cover `p=1,3`, finite stabilization, finite dimensionality,
compatibility with ordinary eigenspaces, the bounded representation for arbitrary
reference points, positive/zero algebraic multiplicity, and a two-dimensional
Jordan block distinguishing generalized from ordinary eigenvectors. Projection
checks cover `p=1,3`, the unique decomposition, idempotence, rank, compactness,
resolvent commutation, one kernel exponent for all reference points, a fixed
signed free eigenmode, vanishing at the nonzero test potential's resolvent point,
and the generalized kernel/range decomposition of a Jordan block. Cluster
checks cover `p=1,3`, the reciprocal representation, disjoint root spaces,
annihilation, idempotence, unique decomposition, kernel intersections, compactness,
rank additivity, the intersection of two overlapping clusters, and the preservation
or annihilation of actual free Fourier modes. Contour checks cover `p=1,3`,
domain factorization, compactness, commutation, norm bounds, vanishing on
resolvent disks, annulus deformation, generalized root vectors, and selection
within finite clusters. A circle of radius `π/2` about zero is explicitly proved
to avoid the free lattice; its normalized integral fixes the constant free mode
and kills the mode at `π`, checking both the orientation and the inside/outside
selection. Further contour checks cover nested-circle products, idempotence,
finite rank, whole-space equality with the enclosed cluster projection, and the
rank and kernel formulas. The explicit free circle of radius `π/2` is proved to
enclose exactly zero, and its entire contour operator equals the individual
projection at zero. Further checks cover openness at `p=1`, analytic dependence
at the free `p=3` potential, local preservation of the multiplicity in the free
half-pi disk, and the zero-radius integration functional. No admission or extra
project axiom is used by the library. Reciprocal-series checks cover the
zero-shift reciprocal squares, the non-Hilbert conjugate pair `p=3, q=3/2`,
the explicit tail after five terms, arbitrary integer centers, and the sharper
positive-shift lattice estimate. Strip checks include the real parameter `π/4`,
endpoint and non-Hilbert exponents, every spectral circle for an explicit nonzero
small potential, analyticity on the resulting `p=3` potential ball, and global
small-potential localization into quarter-pi disks. Height-bound checks include
`p=1` and `p=3`, a nonzero potential valid above both height ten half-planes,
compactness and analyticity at a negative imaginary parameter, a nonzero
`p=3` potential in the numerical region, and uniform heights for a norm ball.
Double-resolvent checks include each Fourier sign on single-mode inputs,
the global bound at `p=3`, a nonzero one-sided potential with perturbation
norm at least two, failure of its original Neumann condition, both inverse
identities under the squared criterion, compactness and analyticity there,
and the exact terminating expansion for arbitrary one-sided `p=3` potentials.
Frequency-tail checks cover both retained cutoff boundaries, removal of interior
single modes, tail convergence, negative strip centers, `p=3`'s constant `288`,
the zero-index estimate, and admissible quarter-pi circles about `±200π` for
the two-sided constant potential `(1,1)`. That potential is explicitly checked
to fail the earlier uniform small-potential strip condition. Localization checks
cover open and convex neighborhoods at `p=1,3`, monotone tails, inclusion of the
horizontal box boundary, exclusion and strip coverage of the vertical boundary,
exclusion of a high-disk center, a common cutoff along every `tφ` for `0 ≤ t ≤ 1`,
and the complete compactness/analyticity/spectral-enclosure package at `p=1`.
Parity checks cover negative even/odd single modes, an infinity-exponent
projection, closed complementary pair spaces, nonconstant even potentials
coupling odd modes to frequencies `±3`, resolvent commutation at a verified
nonzero-potential parameter, and contour preservation at `p=3`. An explicit odd
potential sends an even input to a nonzero odd coefficient, checking the need
for the even-support hypothesis. Multiplicity checks cover the free constant
value, negative spectral indices at `p=3`, absence of longer free root chains,
and a radius-`π` disk whose adjacent lattice points lie on the boundary. The
uniform high-frequency count is instantiated at `p=3`. A whole preconnected
family of one-sided potentials, with no size restriction, has count two in
every quarter-pi disk by the squared Neumann criterion and deformation.
Parity-deformation checks cover disjoint negative residues at `p=3`, arbitrary
nonconstant even two-mode potentials, and a concrete even one-sided potential
with every spectral circle admissible. Its negative odd disk annihilates any
even input. At zero, the same potential has an explicit length-two root chain
whose top vector is verified not to be an ordinary eigenvector; its contour
fixes that vector, and its full root space has even parity. Central-region
checks include a horizontal edge outside the exterior region, a negative
corner, the degenerate zero-height boundary, simultaneous admissibility for
every larger cutoff, inclusion of a negative free endpoint, exclusion of the
next index, the singleton free spectrum at cutoff zero, and free multiplicity
ten at `N=2` and projection rank fourteen at `N=3`. Horizontal boundary
parameters are excluded from the finite spectrum under the admissibility
hypothesis. Central-deformation checks include a corner lying in the closed
rectangle but outside its associated circle, full negative endpoint disks
selected by both regions, and the next negative disk excluded from both.
The total central count is instantiated at `p=1`, and one cutoff is checked
along every `tφ`, `0 ≤ t ≤ 1`, at `p=3`, together with analyticity at the
chosen potential for every larger cutoff. Central-parity checks cover signed
index sets with negative residue representatives, zero cutoff (even rank two
and odd rank zero), even cutoff two (ranks six/four), and odd cutoff three
(ranks six/eight). Further checks exercise both signed free modes, arbitrary
nonconstant even two-mode potentials, dimensions of the actual parity
intersections, addition of both parity ranks to `4N+2`, and analyticity of the
parity components on the shared neighborhood. Unified counting checks cover
negative adjacent disks, central/high-disk separation, every larger cutoff along
`[0,φ]` at `p=3`, unique exterior disk indices at `p=1`, the free double-value
case, actual spectral membership and multiplicities of the returned eigenvalue
pair, and a common neighborhood for analytic central and high-disk projections.
Real-type checks verify the pairing's conjugation convention, negative reflected
frequencies, failure of real type without index reversal, arbitrary amplitudes
and nonreal resolvent parameters at `p=3`, the real spectrum at `p=1`, and energy
positivity in the second component. A constant imaginary potential has a
verified eigenvalue `i`, testing the necessity of the real-type hypothesis.
The full two-vector operator symmetry is also checked for nonconstant potentials.
Reduction checks construct nonorthogonal projections onto the lines `(x,t*x)`;
the transport is the explicit shear `(x,y) ↦ (x,t*x+y)`, is invertible for every
`t`, and has an analytic inverse. Its range equivalence and compression of the
identity are checked. Spectral checks verify the action on a negative free mode,
analytic reductions of arbitrary `p=3` potentials on two-dimensional reference
ranges, the stronger domain norm at `p=1`, and equality with the original
spectral restriction at the reference potential.
Symmetric-eigenvalue checks use upper triangular operators with both distinct
eigenvalues and a repeated eigenvalue having a nontrivial Jordan chain. Their
trace midpoints and squared gaps are verified explicitly. Further checks cover
the free double value at a negative index, analyticity of the exact source
normalization `γ²/2` on the common convex neighborhood at `p=3`, eigenvalue-pair
identification at `p=1`, and exclusion of a free eigenvalue outside its contour.

Boundary-space checks cover reflection without conjugation, negative Sobolev
regularity at `p=∞`, the complementary decomposition, negative free indices,
and separation of the two boundary conditions. A nonconstant complex potential
has the exact positive Dirichlet and negative Neumann coupling from index `-3`
to `5`. Further checks cover restricted norm bounds, odd-frequency reflected
potentials and projection intertwining at `p=1`, and failure of invariance for
a potential lacking reflection symmetry.

Boundary-resolvent checks distinguish the two spectra for the constant potential
`(1,1)`: `1` is a Dirichlet eigenvalue and a Neumann resolvent point, with a
nonzero Neumann inverse, its inverse identity, compactness, and joint analyticity.
They also verify totalization outside the individual resolvent set, compatibility
with the preceding bounded operator, the spectral union and bounded spectral
finiteness at `p=1`, and boundary preservation by a negative-index circle.

Boundary-root checks construct a nonconstant complex reflected potential with a
length-two Dirichlet Jordan chain at `π`. Its top vector is outside the ordinary
eigenspace, and its algebraic multiplicity is at least two. Free checks cover a
negative Neumann index, absence of longer chains at `p=1`, zero multiplicity at
an off-lattice point, contour rank one at a negative index, and central counts
one and five at cutoffs zero and two. The multiplicity splitting is also
instantiated at the endpoint `p=1`.

Boundary-counting checks use a nonconstant complex reflected potential with
explicit norm `1/1000`; a connected small-potential ball proves rank one for
both boundary components in every disk, including a negative-index multiplicity
count. Its Dirichlet cluster annihilates Neumann input. A restricted cluster fixes
the earlier length-two Jordan-chain vector. Other checks cover empty clusters,
a two-index free cluster, one cutoff for every larger box along the full path
`[0,φ]`, unique simple boundary eigenvalues at `p=1`, and shared analytic projector
neighborhoods at `p=3`. For `(1,1)`, the value `1` belongs to the Dirichlet disk
spectrum but is excluded from the Neumann disk spectrum and contributes rank
zero to the Neumann cluster.

Boundary-eigenvalue checks evaluate the intrinsic trace on nonorthogonal moving
one-dimensional ranges and verify its analyticity. A nonzero imaginary constant
potential has trace-defined Dirichlet value `i/1000` and Neumann value `-i/1000`
in the same disk, using actual domain eigenvectors and an explicit rank-one
deformation. Further checks cover the signed negative free value, exact recovery
of a negative free boundary mode by the domain lift, analyticity into the weighted
boundary domain at `p=1`, shared neighborhoods for both analytic simple eigenvalue
functions at `p=3`, and actual weighted-domain eigenvectors at `p=1`.

Interval-extension checks evaluate physical reflected signs before and after the
join, normalized constant integrals, opposite odd-frequency signs, and the
first raw input index reversal on nonconstant data. They check physical/coefficient
agreement and boundary membership at `p=3`, finite-input membership at `p=∞`,
linearity at `p=2`, and the physical one-sided-constant obstruction at `p=1`.

Hilbert-extension checks verify polynomial energy at a negative frequency,
unequal component energies and the one-sided half-normalization, boundedness
and boundary membership for arbitrary coefficients, analyticity, injectivity,
and agreement with physical integrals on finite input. Shifted-kernel checks
cover negative odd reindexing, annihilation of even modes, opposite signs
across the half-integer pole, a complex negative-frequency input, and the
uniform bound and complex linearity.

Quartic-Hilbert checks verify the correction at zero and both neighboring
indices, its `p=1` bound, and the square-kernel bound at `p=∞`. They check
zero diagonal, signed negative-frequency action with a complex coefficient,
and multiplication without conjugation. A two-site input makes both Cotlar
correction terms visible. Other checks cover arbitrary-input quartic bounds,
analyticity, shifted-kernel signs, and agreement of the `ℓ2` and `ℓ4` finite
ordinary formulas.

Dyadic-Hilbert checks verify exponents eight and sixteen, the explicit constant
at exponent eight, signed complex single-mode action, the zero diagonal, and
both shifted-kernel signs. They instantiate bounds and analyticity on arbitrary
inputs, uniqueness against the existing Hilbert and quartic operators, and
independence of the estimate package. The next Hölder product is checked for
complex squaring without conjugation and the exact square-norm identity.

Hilbert-duality checks distinguish the bilinear convention on imaginary
coefficients, instantiate the Hölder bound at `p=1, q=∞`, and allow zero and
empty norming inputs. They verify the fractional exponents, existence below
`1.001`, zero-diagonal and signed complex action below two, and shifted-kernel
normalization. A nonzero nonreal pairing detects the transposition sign;
arbitrary-input bounds and transposition, analyticity, and independence after
two conjugate transfers are also checked.

Interpolation checks retain zero phases at negative powers and verify complex
phase recovery and norms with large imaginary parameters. They check endpoint
unit norms along an entire vertical line, the explicit `p=3` interpolation
parameter `2/3`, its bound, and uniqueness against the full-range operator.
Further checks use `p=3` and `p=3/2` for zero diagonal, signed complex input,
shifted normalization, arbitrary-input bounds and transposition, and analyticity.
They recover the old `p=2` operator, instantiate the all-exponent existence
statement, and verify absolute convergence and exact reciprocal series for
arbitrary inputs at both intermediate exponents.

## Next milestones

1. Use full-range shifted Hilbert boundedness to complete the interval maps
   for every `1<p<∞`, extending the already completed `p=2` case.
   Construct the physical Sobolev identifications in Lemmas 4.1–4.2, then
   transfer Theorem 1.4 and Lemma 4.5 to
   the original period-one potentials.
2. Identify the central projection with the rectangular contour integral and
   transfer the overview theorem's exact norm-dependent central-height convention.
3. Prove the periodic Fourier/distribution realization, physical period-one
   embedding, pair-norm comparison, and compatibility with physical multiplication.

Classical Birkhoff prerequisites and the main dissertation theorems remain
unimplemented. Further sequence-space work includes
embeddings between regularities and the full range of Young inequalities beyond
the `l1`-factor case.
