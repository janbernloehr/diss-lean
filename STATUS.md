# Implementation status

## Implemented and checked

The library has 398 modules and 3157 named public theorems. All compile on the
pinned Lean/mathlib v4.33.1 toolchain.

| Module | Implemented scope |
| --- | --- |
| `NLS.Fourier.HalfIntervalReality` | Conjugate-index compatibility of the completed half-interval map for all `1<p<∞`, including the odd shifted-Hilbert coefficients |
| `NLS.ZakharovShabat.AuxiliaryReality` | Real-type compatibility of source interval extensions and potential phase; real actual auxiliary spectra and nonreal resolvent inclusion, including source period-one potentials |
| `NLS.ZakharovShabat.ClassicalAuxiliaryReality` | A.e. original real type, actual Neumann Fourier-integral compatibility, representative invariance, and real physical auxiliary eigenvalues and spectra |
| `NLS.ZakharovShabat.ClassicalAuxiliaryRootSpaces` | Actual physical auxiliary Jordan-chain recursion, phase equivalence, full-root-space stabilization and finite dimension, and membership in the original unbounded domain |
| `NLS.ZakharovShabat.ClassicalAuxiliaryMultiplicity` | Actual physical full-root-space dimension, equality with ordinary physical and auxiliary coefficient multiplicities, positivity on spectrum, and signed free simplicity |
| `NLS.ZakharovShabat.ClassicalAuxiliaryCounting` | Actual physical central counts `2N+1`, simple high-disc eigenvalues, and analytic starred branches on common original L² neighborhoods |
| `NLS.ZakharovShabat.ClassicalAuxiliaryAsymptotics` | Physical starred Corollary 6.2: square-summable displacements, actual multiplicity counts, analytic simple branches, and all larger quantitative tails on one neighborhood |
| `NLS.ZakharovShabat.ClassicalAuxiliarySpace` | Actual auxiliary interval functions with exact physical H¹ norm; phase isometry, completeness, and bounded Fourier extension/restriction equivalence |
| `NLS.ZakharovShabat.AuxiliaryPhysicalL2` | Function and potential phase isometries on the original component-sum L² space, with actual a.e. representative identities |
| `NLS.ZakharovShabat.ClassicalAuxiliaryOperator` | Dense injective physical inclusion and bounded domain-to-base operator, realizing the actual differential expression for original representatives |
| `NLS.ZakharovShabat.ClassicalAuxiliaryResolvent` | Independently defined physical pencil and spectrum, two-sided inverse, compact physical resolvent, and equality with original auxiliary eigenvalues and coefficient spectrum |
| `NLS.ZakharovShabat.ClassicalAuxiliaryClosed` | Original auxiliary unbounded L² operator with exact endpoint domain, actual differential-expression evaluation, dense domain, and closed graph |
| `NLS.ZakharovShabat.ClassicalAuxiliaryPhase` | Original auxiliary H¹ endpoint conditions, actual differential-expression conjugation, and physical eigenvalue-set equivalence and discreteness |
| `NLS.ZakharovShabat.ClassicalAuxiliaryExtension` | Source phased reflection, exact Sobolev reconstruction on the original closed interval, and unique auxiliary coefficient-domain representatives |
| `NLS.ZakharovShabat.ClassicalAuxiliarySpectrum` | Actual Neumann potential Fourier coefficients, both equation-transfer directions in Lemma 5.1, and physical eigenvalue-set equality with the auxiliary coefficient spectrum |
| `NLS.ZakharovShabat.AuxiliaryRootSpaces` | Actual recursive auxiliary root chains, phase equivalence at every level, finite dimensionality and stabilization, and algebraic multiplicity equality |
| `NLS.ZakharovShabat.AuxiliaryCounting` | Actual finite spectral clusters, central algebraic count `2N+1`, simple high-disc eigenvalues, and common uniform counts after source period-one extension |
| `NLS.ZakharovShabat.AuxiliaryPhase` | Exact phase and potential isometries, reflected-potential compatibility, and conjugation of the actual operator, pencil, and eigenvalue equation |
| `NLS.ZakharovShabat.AuxiliarySpaces` | Closed complementary auxiliary base and Sobolev spaces, explicit ±i Fourier reflection conditions, domain/base isometries, and inclusion compatibility |
| `NLS.ZakharovShabat.AuxiliarySpectrum` | Actual auxiliary restricted pencils defined by bijectivity; spectral conjugation, closure, discreteness, finite bounded clusters, and actual-domain eigenvectors |
| `NLS.ZakharovShabat.AuxiliaryEigenvalueAsymptotics` | Source Neumann potential extension gives both starred coefficient branches global `ℓp` displacements, unique actual high-disc spectral values, and quantitative tails |
| `NLS.ZakharovShabat.SpectralDisplacementTail` | Quantitative single-sequence power tails and global `Memℓp` membership after adding finitely many omitted signed modes |
| `NLS.ZakharovShabat.PeriodicMidpointSummability` | Original contour midpoint displacement is in `ℓp`, with exactly half the corrected two-root tail budget |
| `NLS.ZakharovShabat.BoundaryDisplacementSummability` | Both ordinary reflected-potential boundary branches have full `ℓp` displacements and common quantitative tails |
| `NLS.ZakharovShabat.PeriodOneBoundaryAsymptotics` | Completed interval extension transfers ordinary Corollary 6.2 to source period-one coefficient pairs for every finite `p>1` |
| `NLS.ZakharovShabat.ClassicalBoundaryAsymptotics` | Original physical interval `L²` boundary eigenvalues have square-summable displacements and unique high-disc identification on one neighborhood |
| `NLS.ZakharovShabat.UnweightedResonantDeterminant` | Exact weight-forgetting compatibility and locally uniform equivalence of weighted determinant zeros with the original periodic spectrum |
| `NLS.ZakharovShabat.SpectralRootPair` | Enclosed spectrum equals the scalar pair; algebraic count two identifies its individual spectral multiplicities with scalar analytic orders |
| `NLS.ZakharovShabat.PeriodicRootSequence` | The same original periodic eigenvalue pair has exact multiplicities, contour invariants, localization, and both corrected power sums, independently of label exchange |
| `NLS.ZakharovShabat.PeriodicGapSummability` | Corrected weighted gap power sum for the original intrinsic contour-defined squared-gap sequence, locally uniformly for every larger cutoff |
| `NLS.ZakharovShabat.ResonantGapMajorant` | Weighted product-supremum bound and a branch-free power majorant retaining both leading coefficients and remainders |
| `NLS.ZakharovShabat.UniformGapMajorant` | Convergent weighted gap majorant tails with a corrected explicit budget, locally uniformly for every larger cutoff |
| `NLS.ZakharovShabat.RootGapSequence` | The same roots retain exact analytic orders and simultaneous corrected displacement and weighted gap power sums |
| `NLS.SequenceSpaces.SampledPowerTail` | Injective Fourier sampling gives convergent power tails bounded by the exact source remainder norm |
| `NLS.ZakharovShabat.ResonantLeadingPowerTail` | Both signed weighted leading coefficients have a convergent power sum with no extra potential-norm factor |
| `NLS.ZakharovShabat.ResonantDisplacementMajorant` | One actual-supremum sequence bounds both root displacement powers for every pair of strip zeros |
| `NLS.ZakharovShabat.RootDisplacementBudget` | Explicit exponent-only constant and corrected budget retaining the additive leading Fourier tail |
| `NLS.ZakharovShabat.DisplacementMajorantSum` | Exact convergent majorant sum and quantitative combination of all four component series |
| `NLS.ZakharovShabat.UniformDisplacementMajorant` | Common open convex potential neighborhood and cutoff control every larger actual majorant tail |
| `NLS.ZakharovShabat.RootDisplacementSequence` | Corrected Lemma 6.9: two roots with exact analytic orders, localization, gap bound, and all convergent displacement power tails |
| `NLS.ZakharovShabat.SingleResonantPotential` | Signed single-mode potentials, vanishing complementary sources, exact actual determinant, and Hilbert norm |
| `NLS.ZakharovShabat.RootDisplacementSourceAudit` | Formal failure of the printed Lemma 6.9 displacement budget locally uniformly at zero, on the actual small-square domain |
| `NLS.ZakharovShabat.RootDisplacementPower` | Branch-free residual and power bounds for actual roots, retaining both signed leading Fourier modes |
| `NLS.ComplexAnalysis.LogDerivativeLocal` | Analytic remainder after subtracting the exact analytic-order principal part of a logarithmic derivative |
| `NLS.ComplexAnalysis.FinitePoleRemoval` | Meromorphic normal form fills all finitely many removable logarithmic-derivative remainders |
| `NLS.ComplexAnalysis.AnalyticZeroCount` | Natural analytic zero count, finite zeros and finite orders on compact connected analytic domains |
| `NLS.ComplexAnalysis.ArgumentPrinciple` | Disc contour integral of `f'/f` equals `2πi` times the actual analytic zero count |
| `NLS.ComplexAnalysis.Rouche` | Strict boundary perturbations preserve contour integrals and scalar analytic multiplicity counts |
| `NLS.ComplexAnalysis.ZeroCountComparison` | Exact centered-monomial count, set transport, and open/closed disc count equality |
| `NLS.ComplexAnalysis.ZeroMultiset` | Roots represented with exact analytic multiplicities; count two gives two roots allowing coincidence |
| `NLS.ZakharovShabat.ResonantZeroCount` | Locally uniform count two for the actual determinant on closed/open refined discs and full signed strips |
| `NLS.ZakharovShabat.ResonantRoots` | Two roots exhausting each distant strip, exact analytic orders, localization, and factor-six gap bound |
| `NLS.ZakharovShabat.UniformPowerTail` | Open convex norm-and-tail neighborhoods giving uniform decay of general power-tail budgets |
| `NLS.ZakharovShabat.ResonantSupSmallness` | Arbitrarily small actual diagonal and weighted remainder suprema, uniformly on all distant strips |
| `NLS.ZakharovShabat.ResonantCoefficientSmallness` | Signed weighted leading-mode decay and locally uniform bounds on all three full coefficients |
| `NLS.ZakharovShabat.ResonantDeterminantAnalytic` | Actual scalar determinant, joint analyticity, matrix agreement, original spectral zero criterion, and exact free square |
| `NLS.ZakharovShabat.ResonantDeterminantBounds` | Strip-disc geometry, quadratic perturbation estimate, root radius 3π/32, and strict boundary comparison |
| `NLS.ZakharovShabat.ResonantDeterminantLocalization` | Common neighborhood and cutoff for analytic determinant localization, original matrix agreement, and circle comparison |
| `NLS.ZakharovShabat.ResonantCauchyGap` | Cauchy derivative bound 1/8, complex Lipschitz bound, and branch-free squared-residual gap estimate |
| `NLS.ZakharovShabat.ResonantRootGap` | Actual full-strip product supremum and locally uniform factor-six bound for any two determinant zeros |
| `NLS.SequenceSpaces.DoubleSeriesRegions` | Exact disjoint three-region decomposition of jointly absolutely convergent double series |
| `NLS.SequenceSpaces.DominatedDoubleTesting` | Pointwise two-index domination implies joint absolute convergence and the exact Hölder bound |
| `NLS.SequenceSpaces.HalfCutoffPower` | Full-cutoff power decay from an integer half cutoff, with loss at most three |
| `NLS.SequenceSpaces.SpectralReflectionTail` | Exact reflection of weighted tails, norm preservation, and cutoff antitonicity |
| `NLS.ZakharovShabat.OffDiagonalRegions` | Two far reciprocal-tail bounds and a near bound retaining both actual potential tails |
| `NLS.ZakharovShabat.OffDiagonalTailBound` | Refined bounds on both actual weighted remainders and their analytic extensions, locally uniformly |
| `NLS.ZakharovShabat.OffDiagonalPower` | Convergent regional majorant power sum retaining both potential norm and tail factors |
| `NLS.ZakharovShabat.OffDiagonalPairPower` | Explicit exponent-only constant, source pair-norm bound, and half-cutoff tail |
| `NLS.ZakharovShabat.OffDiagonalSup` | Actual full-strip weighted remainder suprema, weight-scaling identity, and uniform bounds |
| `NLS.ZakharovShabat.OffDiagonalSummability` | Proof-consistent Lemma 6.8(ii): convergent weighted supremum power sums and quantitative pair estimates for both coefficients |
| `NLS.SequenceSpaces.IteratedRowTesting` | Absolute two-index Hölder testing, joint convergence, and complex double-series norm bound |
| `NLS.SequenceSpaces.SpectralReflection` | Exact Fourier reflection isometry for every spectral weight and reversal of shifted norms |
| `NLS.ZakharovShabat.OffDiagonalSeries` | Actual second-iterate component series and both source off-diagonal remainder formulas |
| `NLS.ZakharovShabat.WeightedDoubleRow` | Weight transfer, normalized reciprocal test coordinates, joint convergence, and exact weighted row bound |
| `NLS.ZakharovShabat.OffDiagonalHolder` | Physical joint convergence and actual weighted off-diagonal bounds with component norms retained |
| `NLS.ZakharovShabat.OffDiagonalUniformBound` | One locally uniform cutoff for both row bounds and analytic-extension agreement on full strips |
| `NLS.SequenceSpaces.IteratedConvolutionRows` | Nested convolution rows, inner exponent contraction, and exact outer powered-Young sequence bounds |
| `NLS.SequenceSpaces.IteratedRowSums` | Joint convergence of the double power sum, exact row norm formula, and kernel-interchange symmetry |
| `NLS.SequenceSpaces.IteratedRowTails` | Three-region norm bound with two reciprocal tails at N/2 and the potential tail at N |
| `NLS.ZakharovShabat.DoubleReciprocalRows` | Source double reciprocal rows, equal far-region norms, and separate outer sequence majorants |
| `NLS.ZakharovShabat.DoubleReciprocalSums` | Signed physical two-index sum formula and explicit reciprocal region norm decay |
| `NLS.ZakharovShabat.DoubleReciprocalSummability` | Convergent source-conjugate far/near power sums with the exact decay exponent for all finite p>1 |
| `NLS.SequenceSpaces.ConvolutionRows` | Powered Young sequence of convolution row norms and contractive extraction at twice the frequency |
| `NLS.SequenceSpaces.ConvolutionRowTails` | Exact distant-frequency support split and outer norm majorant retaining both tails |
| `NLS.SequenceSpaces.PuncturedLatticeTail` | Explicit reciprocal-tail decay and compatible full reciprocal norm bound |
| `NLS.ZakharovShabat.ReciprocalRowSummation` | Signed reciprocal row reindexing, inner exponent inclusion, and outer sequence tail majorants |
| `NLS.ZakharovShabat.DiagonalSummationExponent` | Common inner exponent for both regimes and exact source decay exponent |
| `NLS.ZakharovShabat.DiagonalSupSummability` | Actual full-strip supremum tails in lp, with locally uniform quantitative norm bounds |
| `NLS.ZakharovShabat.DiagonalTailPower` | Explicit exponent-only constant and quantitative diagonal p-power tail inequality |
| `NLS.ZakharovShabat.DiagonalSummability` | Lemma 6.8(i): convergent actual diagonal sum and source unweighted pair bound, uniformly for all larger cutoffs |
| `NLS.SequenceSpaces.Basic` | Integer-indexed complex `lp` coefficients |
| `NLS.SequenceSpaces.TestDuality` | Complex bilinear `lp × l1` testing, absolute convergence, norm bound, and continuous coefficient-to-dual map |
| `NLS.Fourier.SchwartzSampling` | Signed half-integer samples in `l1`, controlled by a finite family of genuine Schwartz seminorms |
| `NLS.Fourier.DistributionSynthesis` | Actual tempered distributions for all Banach exponents; continuous linear injection; exact coefficient recovery; single-wave action; distributional convergence of finite Fourier sums including infinity |
| `NLS.Fourier.DistributionPeriodicity` | Physical period two; period one iff even support; doubled coefficients give period one; agreement with continuous synthesis under actual real-line integrals |
| `NLS.Fourier.DistributionDerivative` | Actual derivative multiplier `iπn`; exact scalar derivative graph and domain; weak integration by parts for continuous representatives; closed graph for all Banach exponents |
| `NLS.ZakharovShabat.DistributionFreeOperator` | Injective pair synthesis; actual signed free derivative; exact pair graph/domain; closedness and base-norm graph limits including infinity |
| `NLS.SequenceSpaces.TestConvolution` | Absolutely convergent bilinear test/convolution transposition with reflected multiplier and signed lattice reindexing |
| `NLS.Fourier.DistributionModulation` | Smooth temperate Fourier waves; exact Mathlib distribution multiplication as coefficient shifts; finite-polynomial multiplier identity |
| `NLS.Fourier.ProductTestSamples` | Summable actual Fourier integrals of continuous multiplier times Schwartz test; reflected convolution formula; norm control; compatibility with smooth tests |
| `NLS.Fourier.YoungDistributionProduct` | Appendix A.7 in the period-two model: actual periodic product for every Banach Young triple; exact Fourier norm bound; joint limits; genuine polynomial multiplication; uniqueness at both infinity endpoints; intrinsic coefficient characterization and exponent independence |
| `NLS.Fourier.DistributionProduct` | Unique continuous extension of smooth multiplication to Wiener coefficients; joint approximation independence; actual integral action; agreement with smooth and ordinary function products |
| `NLS.ZakharovShabat.DistributionPotential` | Actual extended domain product; absolute test-integral formula and norm bound; arbitrary smooth approximations; full distributional operator and eigenvalue-equation identification |
| `NLS.Fourier.SchwartzPeriodization` | Continuous period-two Schwartz periodization; absolutely convergent translates and Poisson formula; exact coefficient and integral normalization; polynomial lifts and uniform density; kernel and synthesized-distribution annihilator |
| `NLS.Fourier.SchwartzPeriodizationSmooth` | Classical differentiation of every order; continuous circle-valued derivative maps; globally bounded derivatives and temperate growth; absolute physical derivative sums; uniform Fourier approximation in every derivative order |
| `NLS.Fourier.SchwartzMultiplierConvergence` | Weighted Leibniz seminorm bound; smooth multiplier convergence in genuine Schwartz topology; windowed Fourier reconstruction; termwise action and absolute scalar convergence for every tempered distribution |
| `NLS.Fourier.SchwartzSeries` | Direct sum construction for series absolutely summable in every Schwartz seminorm; derivative and decay control; quantitative seminorm tails; convergence in actual Schwartz topology |
| `NLS.Fourier.SchwartzTranslateProduct` | Inverse-square decay of every weighted seminorm under separation of Schwartz factors; bilateral translated products sum in Schwartz space to the window times actual periodization |
| `NLS.Fourier.PeriodicDistributionKernel` | Intrinsic period-two invariance; all signed integer translations; periodization exchange and normalized window reconstruction; exact kernel-annihilation characterization |
| `NLS.Fourier.PeriodicDistributionIdentification` | Fourier reconstruction and absolute convergence for arbitrary periodic tempered distributions; coefficient uniqueness; intrinsic Banach `lp` regularity iff unique synthesis representation, including infinity |
| `NLS.SequenceSpaces.TemperedWeight` | Polynomial reciprocal-weight growth criterion; unit weight and every real Sobolev weight satisfy it |
| `NLS.Fourier.WeightedSchwartzSampling` | Absolutely summable reciprocal-weighted lattice samples; finite Schwartz seminorm control; continuous complex-linear sampling into `l1` |
| `NLS.Fourier.WeightedDistributionSynthesis` | Genuine weighted tempered-distribution synthesis; absolute raw-coefficient action; norm bound and continuity; injectivity and recovery; intrinsic periodicity; infinity-endpoint truncation convergence; weight/exponent independence |
| `NLS.Fourier.WeightedDistributionIdentification` | Intrinsic weighted Fourier regularity iff unique synthesis; continuous realization and exact coefficients for every real Sobolev exponent; distributional truncation convergence throughout the scale |
| `NLS.SequenceSpaces.Truncation` | Finite projections; coefficient formula; linearity; composition and idempotence; projection and tail norm bounds; continuous linear projections; convergence for finite `p`; density of finite-support coefficients |
| `NLS.SequenceSpaces.WeightedMultiplier` | General weighted symbol bound; bounded linear multipliers; contractive, injective monotone-weight inclusions |
| `NLS.SequenceSpaces.SobolevDerivative` | Monotone real regularity embeddings and composition; period-two derivative with norm bound `π`; exact one-unit regularity recovery from raw and derivative data |
| `NLS.Fourier.CircleTranslation` | Actual periodic `L²` translation isometries; almost-everywhere physical representatives; positive Fourier phase; composition, inversion, strong continuity; exact increment Parseval identity and period-two physical energy normalization |
| `NLS.Fourier.FractionalKernel` | Unit phase bounds; near-zero cancellation and tail decay; globally integrable model kernel for `0<s<1`; reflection, positivity between crossings, and positive core mass |
| `NLS.Fourier.FractionalKernelScaling` | Exact real/nonnegative kernel agreement including zero; positive-frequency integrability; change of variables yielding `n^(2s)` times model mass over `[-n,n]` |
| `NLS.SequenceSpaces.SobolevHomogeneous` | Exact weighted Hilbert square energy; equivalence of weighted membership with homogeneous moment summability on `ℓ²`; contractive unweighted inclusion; explicit two-sided inhomogeneous estimates |
| `NLS.Fourier.FractionalSobolevIdentification` | Physical periodic fractional regularity iff unique weighted Hilbert synthesis for `0<s<1`; actual Fourier coefficient recovery and both inverse identities; quantitative physical energy and weighted norm bounds retaining the zero mode |
| `NLS.Fourier.FractionalBoundaryKernel` | Arbitrary-length interval exterior kernel mass; exact nonnegative boundary-energy formula including infinity; genuine zero-extension mixed interaction; intrinsic interval difference energy and almost-everywhere invariance; magnitude monotonicity |
| `NLS.Fourier.FractionalBoundaryWeight` | Exact endpoint-weight integral and sharp half-regularity integrability threshold; constant exterior energies and critical divergence; explicit exterior bound for almost-everywhere bounded interval data |
| `NLS.Fourier.FractionalHardyKernel` | Exact averaging coefficient and annular mass; strict contraction below half; explicit absorption parameter; adjustable complex square estimate and local kernel domination |
| `NLS.Fourier.FractionalHardyAveraging` | Jointly measurable triangular kernel; exact Tonelli identity including infinite input; row normalization; uniform truncated mass bound; intrinsic difference-energy control |
| `NLS.Fourier.FractionalHardyPreestimate` | Actual truncated boundary square-energy estimate with adjustable and contracting constants; positive-cutoff finiteness from arbitrary interval `L²` data |
| `NLS.Fourier.FractionalHardyLeft` | Finite-energy absorption; cutoff-independent coercive Hardy estimate; increasing cutoff exhaustion and monotone limit; left endpoint finiteness from intrinsic energy and `L²` |
| `NLS.Fourier.FractionalHardy` | Measure-preserving interval reflection; energy invariance; quantitative control of both endpoint weights; finite exterior interaction for arbitrary interval representatives without global measurability or boundedness |
| `NLS.Fourier.FractionalZeroExtension` | Actual indicator zero extension; exact square norm and `L²` membership; full difference energy equals intrinsic plus twice exterior, including infinity; subcritical physical interval/line regularity equivalence for arbitrary positive length |
| `NLS.Fourier.FractionalLineTranslation` | Actual line translation energy; measure-preserving change of variables and Tonelli identity; almost-everywhere invariance; exact zero-extension translation-energy decomposition and subcritical finiteness |
| `NLS.Fourier.PeriodizationIncrement` | Three-translate formula for actual periodic increments away from endpoint crossings; almost-everywhere integrated square bound by nine times the line increment energy |
| `NLS.Fourier.FractionalPeriodization` | Real-kernel periodic energy identity including zero displacement; `9/2` physical periodization bound; arbitrary interval Fourier reconstruction gains periodic regularity and weighted square summability for `0<s<1/2`; bound in original interval energies |
| `NLS.SequenceSpaces.HilbertSobolevEmbedding` | Explicit auxiliary Hölder exponent; exact extended-exponent relation; injective continuous weighted Hilbert inclusion into every finite Banach target with `1/q<s+1/2`; raw coefficient recovery |
| `NLS.Fourier.FractionalIntervalEmbedding` | Explicit diameter bound for lowering intrinsic fractional regularity on arbitrary positive interval lengths; finiteness descends without endpoint matching |
| `NLS.Fourier.IntervalFourierLebesgue` | Appendix A.9 membership in the period-two model: actual interval Fourier coefficients for `0<s<1/2`, `q>1/(s+1/2)`; `s=0` from `L²` alone including target two and infinity; separate intrinsic half-regularity consequence for every finite `q>1` |
| `NLS.Fourier.IntrinsicIntervalEnergy` | Physical square integral plus intrinsic difference energy; almost-everywhere invariance; finiteness; real square-root size; explicit lowering bounds with finiteness before conversion to real values |
| `NLS.Fourier.FractionalHardyBound` | Positive coercive gap below half; explicit finite exterior constant; uniform exterior bound in full intrinsic energy for arbitrary interval `L²` representatives |
| `NLS.Fourier.IntervalSobolevBound` | Exact nonnegative Parseval normalization; combined uniform periodization bound; actual weighted interval coefficients and synthesis; finite spectral/Hardy constant and weighted square/norm estimates in original intrinsic data |
| `NLS.Fourier.IntervalFourierLebesgueBound` | Uniform period-two A.9 bounds in intrinsic size for positive subcritical and half regularity; explicit half-regularity index depending on `q`; zero-regularity bound from physical `L²` alone, including target two and infinity |
| `NLS.Fourier.IntervalDilation` | Exact restricted-measure transport under positive dilation; arbitrary nonnegative integral scaling; interval `MemLp` transport on open and half-open intervals; square-energy scaling |
| `NLS.Fourier.FractionalDilation` | Kernel homogeneity including the diagonal; exact `c^(2s-1)` intrinsic energy scaling including infinite values; separate inhomogeneous factors and a quantitative intrinsic size bound |
| `NLS.Fourier.IntervalCoefficientScaling` | Actual normalized Fourier integrals on length `L`; agreement with mathlib's interval coefficient; exact period-two dilation identity; square-integrable interval data transport |
| `NLS.Fourier.ArbitraryPeriodFourierLebesgue` | A.9 membership and uniform intrinsic norm bounds for every positive period, including the source's zero and half conclusions; weighted square summability; exact zero-regularity normalization `L^(-1/2)` including infinity |
| `NLS.Fourier.FractionalRestriction` | Interval energy bounded by full displacement energy; exact tail mass `1/s`; central real-kernel identity including zero displacement; reverse periodic-to-interval estimate and regularity restriction for every positive index |
| `NLS.Fourier.IntervalSobolevIdentification` | Exact interval/periodic regularity equivalence below half; actual weighted Fourier criterion for arbitrary `L²` representatives on every positive interval; bidirectional dilation finiteness; unique weighted representation |
| `NLS.Fourier.IntervalSobolevNormEquivalence` | Exact square-energy normalization; finite reverse restriction constant; intrinsic size controlled by weighted Fourier norm for `0<s<1`; two-sided intrinsic/Fourier bounds for original period-two interval data below half |
| `NLS.Fourier.FractionalDifferenceQuotient` | Measurable physical difference quotient; interval almost-everywhere invariance; linearity; finite fractional energy iff product-space square integrability; exact quotient `L²` norm |
| `NLS.Fourier.PhysicalIntervalL2` | Actual quotient representatives on every positive interval; exact length normalization; normalized coefficients; arbitrary-input reconstruction and faithful almost-everywhere identification |
| `NLS.Fourier.IntrinsicIntervalSobolev` | Intrinsic finite-energy normed complex quotient; exact graph norm square `N+E_s`; continuous `L²` and difference-quotient maps; reconstruction, input norm equality, and exact almost-everywhere class equality |
| `NLS.Fourier.IntrinsicFourierEmbedding` | Continuous complex-linear Fourier injections in the intrinsic norm for positive subcritical and half regularity on every positive interval; exact original coefficients; uniform norm bounds |
| `NLS.Fourier.IntrinsicGraphClosed` | Transfer of arbitrary circle almost-everywhere properties to physical coordinates; simultaneous `L²` graph limits identify the actual fractional difference quotient, including at half regularity |
| `NLS.Fourier.IntrinsicSobolevComplete` | Closed isometric graph image; complete intrinsic complex Hilbert space; exact length-normalized inner product; intrinsic convergence iff both graph components converge; existence of Cauchy limits |
| `NLS.Fourier.IntrinsicSobolevSynthesis` | Bidirectional physical coordinate energy finiteness; intrinsic norm dilation bound; injective continuous weighted synthesis for `0<s<1`; exact actual Fourier coefficients and arbitrary-length norm constant |
| `NLS.Fourier.IntrinsicSobolevEquivalence` | Actual weighted Fourier analysis; both inverse identities; continuous intrinsic/weighted Hilbert equivalence below half; explicit forward and inverse arbitrary-length bounds; A.9 factorization |
| `NLS.Fourier.IntrinsicSobolevApproximation` | Finite physical Fourier truncations; exact coefficient selection; uniform norm bound; convergence in the full intrinsic norm and density of finite Fourier support below half |
| `NLS.SequenceSpaces.WeightedFourierTail` | Weighted scalar and pair remainders retaining `|k|=N`; exact coefficient and weighting identities; contractivity and finite-exponent norm convergence |
| `NLS.SequenceSpaces.WeightedHolderMultiplier` | Arbitrary conjugate-space symbols from weighted `ℓᵖ` to weighted `ℓ¹`; linear dependence on the symbol and uniform scalar shifted bounds |
| `NLS.SequenceSpaces.WeightedSandwich` | Actual weighted double-multiplier product; shifted estimate; near/far decomposition and exact potential-tail substitution |
| `NLS.SequenceSpaces.SandwichMajorant` | Norm-preserving complex magnitude coefficients; exact positive absolute sandwich rows and product norm estimate |
| `NLS.SequenceSpaces.WeightedSandwichGain` | Pointwise weight gains on two finite windows imply the corresponding shifted `ℓ¹` sandwich norm gain |
| `NLS.ZakharovShabat.ResonantWindowGeometry` | Closed opposite half-radius windows; retained potential-tail boundary; signed distance comparisons and source's extra inverse-weight gain |
| `NLS.ZakharovShabat.ComplementaryReciprocalTail` | Complementary inverse-bracket envelope; uniform conjugate-space tail decay for both signs, including resonance and the `p=1` endpoint |
| `NLS.ZakharovShabat.WeightedResonantSandwich` | Refined scalar near/far estimate with the potential tail divided by `w(n)` |
| `NLS.ZakharovShabat.ComplementaryDoubleEstimate` | Scalar double-complementary estimate throughout the closed strip; both signs and zero center; inhomogeneous bracket and explicit exponent-only constant |
| `NLS.ZakharovShabat.WeightedSquareEstimate` | Lemma 6.5 for every finite Banach exponent; actual square factorization; exact shifted pair norm and conjugated operator norm with both source terms |
| `NLS.ZakharovShabat.UnweightedComplementary` | Contractive inclusion into the exact unit-weight pair norm; shift isometries; compatibility of tails and the actual complementary potential operator |
| `NLS.ZakharovShabat.WeightedContraction` | Locally uniform simultaneous weighted/unweighted square bounds on an open convex potential neighborhood, for every positive tolerance; the source half-size contraction |
| `NLS.ZakharovShabat.WeightedDomainPotential` | Weighted one-derivative Hölder embedding into weighted `ℓ¹`; continuous actual domain potential; original coefficients and exact composition giving `T_n` |
| `NLS.ZakharovShabat.WeightedCorrection` | The convergent squared Neumann inverse in the source shifted norm, transported back; two-sided inversion, source factorization, commutation, and weighted/unweighted compatibility |
| `NLS.ZakharovShabat.WeightedQEquation` | Actual complementary derivative-domain solution, source potential formula, Q-equation, uniqueness, and locally uniform existence on full closed strips |
| `NLS.ZakharovShabat.ResonantCoordinates` | Continuous physical-mode extraction and synthesis, actual resonant projection, domain lift, free-pencil action, and complementary identities |
| `NLS.ZakharovShabat.WeightedResonantReduction` | Explicit `2×2` resonant matrix, eigenfunction reconstruction, exact residual identity, both kernel directions, and weighted-domain determinant criterion |
| `NLS.ZakharovShabat.UnitWeightedRealization` | Coefficient-preserving equivalences for the original base and derivative domain; exact equation and periodic-spectrum identification |
| `NLS.ZakharovShabat.PeriodicResonantReduction` | Lemma 6.6 for the original periodic spectrum, valid with a locally uniform cutoff over full closed strips for every finite Banach exponent |
| `NLS.SequenceSpaces.ReflectedTestSymmetry` | Commutativity of original `ℓ¹` convolution and symmetric reflected bilinear tests; free-symbol sign reversal |
| `NLS.ZakharovShabat.BilinearGreen` | Unconjugated cross-component Green identity for the actual weighted differential pencil and arbitrary complex potentials at every finite Banach exponent |
| `NLS.ZakharovShabat.ResonantDiagonalSymmetry` | Lemma 6.7(i), equal diagonal corrections, named source coefficients, and the common-diagonal resonant matrix form |
| `NLS.ZakharovShabat.ConstantResonantCoefficient` | Actual constant component potentials, exact complementary action, and the diagonal correction `ab/(λ+nπ)` for nonzero indices |
| `NLS.ZakharovShabat.ResonantRealityCounterexample` | Constant `(1,i)` violates the printed unconditional reality clause at arbitrarily large positive resonances within the half-size contraction regime |
| `NLS.SequenceSpaces.ConjugateReflection` | Physical conjugation on arbitrary symmetric weighted coefficients, norm preservation including infinity, involution, and conjugated convolution sums |
| `NLS.ZakharovShabat.WeightedReality` | Signed conjugation on weighted pairs and derivative weights; source potential star and exact Fourier coefficient characterization of `φ*=εφ` |
| `NLS.ZakharovShabat.ConjugateComplementary` | Closed-strip conjugation invariance and conjugation of the actual domain potential, complementary inverse, and `T_n` under the reality hypothesis |
| `NLS.ZakharovShabat.ConjugateCorrection` | Conjugation of the actual inverse from uniqueness; exact signed action on resonant amplitudes and corrected synthesis |
| `NLS.ZakharovShabat.ResonantConjugation` | Corrected Lemma 6.7(ii) for both reality signs, both off-diagonal identities, real-axis diagonal reality, and locally uniform cutoffs throughout closed strips |
| `NLS.FunctionalAnalysis.SquaredNeumannInvariant` | Continuous testing of convergent even operator series and preservation of every closed kernel invariant under the operator square |
| `NLS.ZakharovShabat.WeightedComponentParity` | The actual `T_n` exchanges physical components; even powers and their convergent Neumann sum preserve component subspaces |
| `NLS.ZakharovShabat.SourceResonantMatrix` | Exact source basis order, displayed matrix form, determinant preservation under reversal, and the source-order eigenvalue criterion |
| `NLS.ZakharovShabat.ResonantPotentialModes` | Actual potential applied to either resonant domain mode; exact component shifts and signed leading Fourier coefficients |
| `NLS.ZakharovShabat.ResonantParityExpansion` | Equations (1.14)–(1.15): odd diagonal part, even off-diagonal parts, and second-iterate Fourier remainders |
| `NLS.ZakharovShabat.ResonantCoefficientSeries` | Individual unwanted parity terms vanish; actual convergent odd series for `a_n` and positive even series for both Fourier remainders |
| `NLS.FunctionalAnalysis.ConjugatedNeumannBounds` | Exact transported inverse bound and geometric finite-series remainder, including trivial Banach spaces |
| `NLS.ZakharovShabat.ResonantSourceNorm` | Signed modulation cancels each resonant wave; exact single-component source norms |
| `NLS.ZakharovShabat.WeightedEvenApproximation` | Actual even partial sums, exact remainder, and shifted error bounded by `2·2⁻ᵐ` at half contraction |
| `NLS.ZakharovShabat.ResonantEvenBounds` | Factor-two shifted and unweighted component bounds; uniform geometric approximation on a potential neighborhood and distant closed strips |
| `NLS.ZakharovShabat.ComplementaryResolventIdentity` | Scalar, base-space, and derivative-domain resolvent identities on full closed strips |
| `NLS.ZakharovShabat.ComplementaryAnalytic` | Entire center normalization, explicit two-sided inverse, and analytic domain-valued extension agreeing with the actual complementary inverse, including infinity |
| `NLS.ZakharovShabat.WeightedPotentialAnalytic` | Weighted potential as a continuous linear operator-valued map; exact bilinear bound; jointly analytic extension of the actual `T_n` |
| `NLS.ZakharovShabat.WeightedCorrectionAnalytic` | Open joint correction domain; analytic even and full extensions equal to the shifted Neumann inverses |
| `NLS.ZakharovShabat.ResonantAnalytic` | Lemma 6.8's analytic assertion for all three source coefficients, with a uniform potential neighborhood and cutoff and explicit agreement on distant closed strips |
| `NLS.ZakharovShabat.UnweightedEvenCorrection` | Unit-weight square norm identity, even inverse/source-vector compatibility, and factor-two bounds retaining unweighted potential norms |
| `NLS.ZakharovShabat.ComplementaryRowEstimate` | Actual reciprocal rows, parameter-independent row envelopes, exact conjugate row norm, and absolute Hölder testing |
| `NLS.ZakharovShabat.ResonantDiagonalEstimate` | Exact diagonal Fourier series and uniform Hölder bound using unweighted component norms and the source reciprocal sum |
| `NLS.ZakharovShabat.ResonantDiagonalSup` | Actual full-strip supremum, bounded image, and uniform bounds between source coefficient values and the reciprocal majorant |
| `NLS.SequenceSpaces.SpectralConvolution` | Weighted Young convolution `ℓᵖ_w × ℓ¹_w → ℓᵖ_w` including infinity; exact constant one; Banach-space summation; bilinear continuity; unweighted product identification and shifted estimate |
| `NLS.SequenceSpaces.PuncturedLattice` | Punctured reciprocal lattice in every `ℓᑫ`, `q>1`, including infinity; Hilbert norm at most two; exponent-only complementary constant with exact `c₂=2` |
| `NLS.ZakharovShabat.ComplementaryL1` | Actual reciprocal in conjugate `ℓᑫ`; weight-independent gain from weighted `ℓᵖ` to weighted `ℓ¹`; uniform bounds in every scalar shift, including `p=1` |
| `NLS.ZakharovShabat.WeightedPotentialInverse` | Lemma 6.4 for all finite Banach exponents with sign reversal and `c₂=2`; original potential/domain-inverse identification; operator norm and same-shift squared bound |
| `NLS.SequenceSpaces.WeightedPairMap` | Componentwise continuous linear maps preserve a common scalar bound in the exact finite-exponent pair norm |
| `NLS.ZakharovShabat.ComplementaryStrip` | Unpunctured closed strip; nonresonant denominator lower bound; zeroed reciprocal symbol; uniform base and one-derivative bounds |
| `NLS.ZakharovShabat.WeightedResonance` | Correctly signed resonant and complementary projections; decomposition, idempotence, mutual annihilation, coefficient characterization and contractivity |
| `NLS.ZakharovShabat.WeightedFreePencil` | Arbitrary positive weighted derivative domain; coefficient-preserving inclusions; free pencil with exact identification with the existing differential operator |
| `NLS.ZakharovShabat.ComplementaryFreeInverse` | Base and domain-valued complementary inverse at every strip point including resonance; quantitative derivative gain; both projected inverse identities and uniqueness |
| `NLS.ZakharovShabat.ComplementaryShiftedNorm` | Coefficient norm monotonicity; projections and complementary inverse contract every signed shifted finite-exponent pair norm uniformly |
| `NLS.SequenceSpaces.SpectralWeight` | Section 6's exact weight class; signed monotonicity; unit, constant, scaled Sobolev and physical `π` weights; tempered reciprocal; forward and reverse translation comparisons |
| `NLS.SequenceSpaces.ShiftedWeight` | Contractive unweighted inclusion; continuously equivalent translated-weight spaces; exact scalar shifted energy; coefficient modulation and group law; isometric shift-weight identification; scalar comparisons including infinity |
| `NLS.SequenceSpaces.ShiftedPairNorm` | Opposite physical component modulations; exact finite-`p` signed energy; both norm comparisons with factor `w(i)`; additive shift law and zero shift |
| `NLS.Fourier.SpectralWeightModulation` | Weighted realization agrees with unweighted synthesis; coefficient modulation equals actual multiplication by the physical Fourier wave as tempered distributions |
| `NLS.Fourier.FractionalSpectralBounds` | Positive integral comparison constants; uniform two-sided bounds for all integer frequencies; finite and positive nonzero weights; physical-energy comparison and conventional homogeneous square-sum regularity criterion |
| `NLS.Fourier.FractionalTranslationEnergy` | Physical nonnegative translation energies; exact Tonelli diagonalization for arbitrary measurable kernels and displacement measures; genuine double-integral formula; fractional kernel, spectral finiteness criterion, translation invariance, single modes, constants, and frequency reflection |
| `NLS.Fourier.SobolevDistributionDerivative` | Embeddings preserve actual distributions; genuine derivative multiplier; exact graph and closedness at every real regularity including infinity; intrinsic periodic regularity criterion |
| `NLS.SequenceSpaces.Weighted` | Positive, unit, and real-exponent Sobolev weights; weighted coefficient spaces; weighting equivalence and isometry; normed complex vector space and completeness; coefficient decay; weighted truncation bounds and convergence |
| `NLS.SequenceSpaces.PairNormInfty` | Actual frequencywise sum then supremum norm on signed pairs; complete `lp` construction; continuous equivalences to signed and scalar maximum products; sharp factor two and reflected first component |
| `NLS.SequenceSpaces.WeightedPairNormInfty` | Complete weighted endpoint pairs; isometric weighting; exact weighted and real Sobolev supremum formulas; sharp comparisons; scalar-coordinate conversion with the source's first-component reflection |
| `NLS.Fourier.PairDistributionInfty` | Continuous injective actual endpoint pair synthesis; signed coefficient recovery; physical periodicity; exact source norm from distributional coefficients; unique representation of arbitrary periodic endpoint pairs |
| `NLS.SequenceSpaces.PairNorm` | Actual finite-`p` component-sum coefficient and weighted pair spaces; exact combined energies; arbitrary Sobolev exponent `sp`; continuous linear norm equivalences; sharp factor `2^(1/p)` |
| `NLS.ZakharovShabat.PairNormHeight` | Resolvent and strict strip bounds in the source's finite pair norm; uniform open convex parameter neighborhoods; analytic actual norm-height contours with rank `4N+2` |
| `NLS.SequenceSpaces.Multiplier` | Bounded diagonal symbols; norm bound; continuous linear operator; commutation with truncations |
| `NLS.SequenceSpaces.Translation` | Reindexing by an integer equivalence preserves the norm; shifts as linear isometry equivalences |
| `NLS.SequenceSpaces.PowerCoefficients` | Positive powers of magnitudes divide the coefficient exponent with exact norm identity, including original exponents below one |
| `NLS.SequenceSpaces.PowerYoung` | Scaled real Young relations; powered convolution summability and root representatives with exact constant-one norm bound |
| `NLS.SequenceSpaces.MixedYoungExponents` | Source reciprocal identity and order constraints construct the intermediate exponent and both scaled Young relations |
| `NLS.SequenceSpaces.MixedYoung` | Appendix B.3 for finite positive exponents: exact nested norm estimate; convergence at all three levels; unit modes attain constant one |
| `NLS.SequenceSpaces.YoungTrilinear` | Weighted arithmetic-geometric mean estimate for three factors; translated finite energy bounds; unit and homogeneous finite convolution-pairing estimates with exact constant one |
| `NLS.SequenceSpaces.YoungFinite` | Single-frequency decomposition and convolution expansion; exact finite dual kernel; uniform finite-input Young norm estimate |
| `NLS.SequenceSpaces.YoungExponents` | Exact reciprocal exponent relation; input/output comparisons; conjugate endpoint and real dual-exponent identities |
| `NLS.SequenceSpaces.YoungInequality` | Appendix B.2 for every Banach Young triple; pointwise absolute convergence; finite-cutoff convergence; `lp` Fatou membership; exact norm bound including infinity |
| `NLS.SequenceSpaces.YoungConvolution` | Continuous complex bilinear convolution with norm exactly one; commutativity; old-construction compatibility; single-mode action; joint limits and full output-norm cutoff convergence |
| `NLS.SequenceSpaces.Convolution` | Absolutely convergent Banach-space construction; coefficient formula; `lp × l1 → lp` norm bound, including `p=∞`; continuous bilinear map; single-mode shift identity |
| `NLS.SequenceSpaces.ExponentEmbedding` | Contractive increasing-exponent embeddings including infinity; injectivity and composition; weighted transport and simultaneous regularity decrease |
| `NLS.SequenceSpaces.HolderEmbedding` | General Banach Hölder products; weighted ratio embeddings with explicit constants; exact finite-exponent Sobolev reciprocal threshold; fractional Sobolev embeddings into smaller exponents |
| `NLS.Fourier.DistributionEmbeddings` | Exponent and weighted Hölder embeddings preserve actual distributions; arbitrary periodic source data has a unique target representative |
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
| `NLS.ZakharovShabat.ExplicitHeight` | Explicit norm-ball height `(1+8pM)^p` for every finite exponent; printed Hilbert height `(1+8M)^2`; boundary resolvent inclusion and strict spectral strip bounds |
| `NLS.ZakharovShabat.HeightSpectralBox` | Independent-height central boxes and finite spectra; height transfer; uniform Hilbert count `4N+2` and agreement with the existing rectangular projection |
| `NLS.ZakharovShabat.RectangleSpectrum` | Arbitrary ordered resolvent rectangles; finite enclosed spectrum; whole cluster projection formula; exact range and rank; contour equality from spectral selection |
| `NLS.ZakharovShabat.HeightRectangleContour` | Independent-height corners and actual contours; boundary admissibility; whole central projection equality; uniform analyticity and rank at Hilbert and all-exponent norm heights |
| `NLS.FunctionalAnalysis.SquaredNeumann` | Geometric inversion of `1-K²`; both inverse identities for `(1+K)(1-K²)⁻¹`; correction norm bound; terminating inverse for square-zero operators |
| `NLS.FunctionalAnalysis.ConjugatedSquaredNeumann` | Transport of small-square inversion through a continuous linear equivalence; original-space geometric series, two-sided inverses, uniqueness, and commutation |
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
| `NLS.SequenceSpaces.Insertion` | Zero insertion along an integer embedding as a linear isometry at every Banach exponent; image and outside-image formulas; even/odd index embeddings |
| `NLS.SequenceSpaces.PeriodDoubling` | Isometric even insertion; equivalence onto the even subspace; contractive even sampling and projection identity; convolution compatibility |
| `NLS.Fourier.PeriodOneCoefficients` | Actual integrable period-one Fourier integral identity; even/odd coefficient formulas; preservation of coefficient norm; injective continuous absolute-series realization |
| `NLS.ZakharovShabat.PeriodOneEmbedding` | Isometric pair insertion; exact even-potential range; physical absolute-series identification; automatic resolvent and contour parity |
| `NLS.Fourier.HalfIntervalBoundedness` | Bounded half-interval Fourier map for every `1<p<∞`; exact even/odd coefficients, finite integral agreement, explicit bound, and injectivity |
| `NLS.ZakharovShabat.BoundedIntervalExtension` | Full-range Dirichlet/Neumann interval maps into the actual boundary spaces; bounds and analyticity; finite physical integral agreement, uniqueness, parity formulas, and equality with the Parseval completion at `p=2` |
| `NLS.Fourier.ContinuousSynthesis` | Uniformly convergent period-two synthesis from `ℓ1`; contraction, injectivity, continuous coefficient extraction, actual normalized interval integrals, and single-mode agreement |
| `NLS.Fourier.SobolevSynthesis` | Continuous representatives for every finite Banach exponent; explicit `2p` bound, uniform finite approximation, uniqueness, bounded traces, physical reflection, odd endpoint vanishing, and agreement with the normalized `L²` Fourier inverse |
| `NLS.FunctionalAnalysis.IntegralAbsoluteContinuity` | Absolute continuity of vector-valued integral primitives via scalar norm control; invariance under equality on the interval and addition of constants |
| `NLS.Fourier.CirclePrimitive` | Physical `L²` pullback, transfer of almost-everywhere equality, normalized full-period bound, bounded primitive functionals on `[0,2]`, and agreement with physical Fourier integrals |
| `NLS.Fourier.SobolevDerivative` | Actual `L²` Fourier derivative; integral reconstruction from finite modes, absolute continuity, almost-everywhere classical differentiation, square integrability of the actual derivative, and exact physical derivative coefficients |
| `NLS.FunctionalAnalysis.ComplexAbsoluteContinuity` | Bounded linear preservation of absolute continuity, complex almost-everywhere differentiability, vector-valued fundamental theorem, and complex integration by parts |
| `NLS.Fourier.AbsoluteContinuousCoefficients` | Smooth physical waves; derivative coefficient formula with endpoint jump at every frequency, periodic cancellation, and Parseval square summability |
| `NLS.Fourier.SobolevIdentification` | Classical periodic `H¹` criterion via absolute continuity and the actual `L²` derivative; weighted Fourier recovery, both inverse identities, and unique-representative characterization |
| `NLS.Fourier.FoldedSobolev` | Original interval `H¹` regularity without periodic endpoints; integrable and `L²` folding, half-coefficient formula, matching-join integral reconstruction, absolute continuity, and the reflected derivative sign |
| `NLS.Fourier.PeriodicSobolevLift` | Matching-endpoint circle lift; exact values on the closed period, derivative agreement almost everywhere, classical `H¹` and weighted Fourier recovery, including reflected interval coordinates |
| `NLS.ZakharovShabat.ClassicalIntervalExtension` | Original Dirichlet/Neumann endpoint domains; signed-swap extension into actual weighted boundary domains; normalized physical coefficients, closed-period reconstruction, exact restriction recovery, and injectivity on the original interval |
| `NLS.ZakharovShabat.ClassicalIntervalRestriction` | Physical restriction to the original classical endpoint domain; signed reflection and exact extension right inverse; surjectivity, equality precisely on the closed interval, injectivity of restriction, and unique weighted representatives |
| `NLS.Fourier.SobolevEnergy` | Physical classical energy, invariance under interval equality, exact function and derivative Parseval formulas, coefficient graph-energy comparison, and explicit two-sided weighted norm bounds |
| `NLS.Fourier.FoldedEnergy` | Classical interval square integrability, exact folded `L²` energy for arbitrary square-integrable halves, derivative energy through a.e. reflection, and additive `H¹` energy |
| `NLS.ZakharovShabat.ClassicalIntervalNorm` | Physical component-sum interval pair energy and norm; exact extended-component energy, maximum weighted pair norm comparison with constants `1` and `√2 π`, restriction bounds, and zero norm precisely for the zero interval function |
| `NLS.Fourier.SobolevEnergyEmbedding` | Injective linear embedding into the Euclidean product of the physical `L²` function and derivative spaces; exact unnormalized physical Sobolev energy and norm |
| `NLS.ZakharovShabat.ClassicalIntervalSpace` | Actual functions on `[0,1]` with pointwise linear structure; membership exactly from original classical endpoint data; algebraic Fourier restriction equivalence, original-function constructors and representatives, continuity, and both endpoint conditions |
| `NLS.ZakharovShabat.ClassicalIntervalIsomorphism` | Exact physical `H¹` norm and Banach-space structure on both original interval domains; Lemma 4.2 as continuous linear extension equivalences, exact Fourier-integral forward maps, physical restriction inverses, and operator-norm bounds `1` and `√2 π` |
| `NLS.Fourier.CircleMultiplication` | Actual multiplication of continuous circle functions and arbitrary `L²` classes; a.e. product, uniform-norm bound, bounded complex bilinearity, unit identity, and physical-period pullback |
| `NLS.Fourier.PhysicalConvolution` | Physical Fourier modulation and norm preservation; exact `ℓ2 × ℓ1` convolution/product identification, Sobolev potential multiplication, physical square integrability, and normalized real-interval coefficient integrals |
| `NLS.ZakharovShabat.PhysicalOperator` | Actual base and domain representatives, full physical differential expression with opposite derivative signs, square-integrable output, a.e. coefficient/operator realization, injectivity and nonzero preservation, and equivalence of physical and coefficient eigen-equations |
| `NLS.Fourier.IntervalL2Realization` | Actual normalized coefficients of arbitrary physical `L²` period data; a.e. reconstruction through a measurable circle lift, the other inverse, and invariance under a.e. equality |
| `NLS.ZakharovShabat.IntervalEquationReflection` | Physical operator congruence on a period, a.e. signed-reflection congruence, differential-expression intertwining with Dirichlet potential reflection for both boundary signs, and the original physical equation transfer |
| `NLS.ZakharovShabat.ClassicalIntervalTransfer` | Arbitrary original `L²` potential extension, exact physical coefficients and reconstruction, Dirichlet coefficient membership, Lemma 4.1 in the existing coefficient operator, nonzero eigenvector preservation, and original eigenvalue inclusion in boundary and periodic spectra |
| `NLS.ZakharovShabat.ClassicalIntervalEigenvalues` | Converse physical restriction and nonzero preservation; original eigenvalues defined by the differential equation and classical endpoints; equality with coefficient boundary spectra; a.e. potential invariance; closedness, discreteness, bounded-region finiteness, periodic union, and exact free lattice |
| `NLS.ZakharovShabat.PhysicalIntervalL2` | Original scalar and pair Lebesgue `L²` classes with the component-sum Hilbert norm; representative construction, a.e. equality criterion, linear operations, and exact physical energy |
| `NLS.ZakharovShabat.PhysicalPotentialExtension` | A.e.-invariant, complex-linear Dirichlet potential extension; exact norm factor `√2/2`; bounded analytic map into the actual Dirichlet coefficient space; agreement with original Fourier integrals and injectivity |
| `NLS.ZakharovShabat.ClassicalIntervalAnalytic` | Original physical potential parameterization of trace eigenvalues; analytic branches on one open convex neighborhood and cutoff for both boundary conditions; unique classical eigenvalue in each high disk; uniform coefficient counting data and exact free branches |
| `NLS.ZakharovShabat.DirichletIntervalL2` | Dense weighted boundary inclusions; compatibility of physical Dirichlet extension with classical restriction; closed dense image and surjectivity; full Dirichlet `L²` continuous linear equivalence, exact norm factors, and physical inverse restriction |
| `NLS.ZakharovShabat.IntervalComponentFlip` | Isometric component sign changes on physical classes and coefficient boundary spaces; a.e. physical realization; exact relation between Dirichlet and Neumann signed reflection |
| `NLS.ZakharovShabat.IntervalL2Isomorphism` | Both signed base-space continuous linear equivalences; exact forward/inverse norm factors; physical reconstruction and actual Fourier integrals; inverse restriction; compatibility with classical functions, weighted restriction, and domain inclusion |
| `NLS.ZakharovShabat.ClassicalIntervalOperator` | Physical domain inclusion and operator maps; injective dense inclusion; arbitrary-interval differential congruence; exact action on original representatives and square-integrable outputs |
| `NLS.ZakharovShabat.ClassicalIntervalResolvent` | Independently defined physical pencil and resolvent set; full intertwining and equality with boundary resolvents; bounded two-sided physical inverse; compact base-space resolvent; original spectrum equals coefficient boundary spectrum and classical eigenvalues |
| `NLS.ZakharovShabat.ClassicalIntervalClosed` | Original physical unbounded partial linear operator; exact classical endpoint-domain membership; potential-independent dense domain; evaluation by the actual differential expression; physical graph recognition and closedness |
| `NLS.ZakharovShabat.ClassicalIntervalRootSpaces` | Independent physical pencil root chains; preservation of every chain level and full root space; original domain membership; linear equivalence, finite dimension, stabilization, and closedness |
| `NLS.ZakharovShabat.ClassicalIntervalMultiplicity` | Physical algebraic multiplicity as full root-space dimension; equality with coefficient multiplicity; spectral characterization; free simplicity; periodic multiplicity splitting into both original boundary contributions |
| `NLS.ZakharovShabat.ClassicalIntervalCounting` | Finite central set from the physical spectrum; common physical neighborhood for central multiplicity `2N+1`, high-disk algebraic simplicity, localization, and analytic branches for both boundary conditions |
| `NLS.FunctionalAnalysis.RectangleIntegral` | Actual four-edge Banach-valued integral; boundary integrability and congruence; evaluation and bounded linear maps; horizontal/vertical subdivision; Cauchy vanishing and analytic-strip deformation |
| `NLS.ZakharovShabat.ResolventRectangle` | Operator- and domain-valued rectangular resolvent integrals; domain factorization and compactness; commutation with resolvents and algebraic projections; zero on filled resolvent rectangles; edge deformation through resolvent strips |
| `NLS.ZakharovShabat.CentralRectangleContour` | Exact corner and boundary identification with the central box; actual central rectangular integral; domain factorization and compactness uniformly on a common neighborhood for all larger cutoffs |
| `NLS.FunctionalAnalysis.RectangleResidues` | Horizontal/vertical primitive formulas; closed-contour primitive cancellation; logarithmic evaluation of enclosed simple poles; exterior vanishing; all higher pole terms vanish when the boundary avoids the pole |
| `NLS.ZakharovShabat.RectangleRootSelection` | Weighted rectangular integration along all finite Jordan chains; full enclosed root spaces fixed and exterior root spaces annihilated; individual projection selection, including boundary points; exact finite-cluster filtering |
| `NLS.ZakharovShabat.CentralRectangleSelection` | Exact open-corner geometry; actual central contour selects individual root-space projections; absorption of the central algebraic projection and inclusion of its range in the rectangular integral range |
| `NLS.FunctionalAnalysis.RectangleCircleIntegral` | Integrability of continuous edge-integral families on a circle; edge/circle Fubini; interchange of the actual rectangular and circular Banach-valued integrals using only product-boundary continuity |
| `NLS.ZakharovShabat.RectangleCircleComparison` | Resolvent identity integrated against exterior resolvents; a rectangular contour operator is unchanged by multiplication with any admissible circle enclosing its filled rectangle, on the whole base space |
| `NLS.ZakharovShabat.CentralRectangleProjection` | Actual rectangular integral equals the central algebraic projection on the whole space; idempotence, exact generalized-eigenspace range, algebraic rank formula, and uniform operator-norm analyticity and rank `4N+2` |

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
closed, as detailed below. The forward realization of coefficients as periodic
distributions and exact free derivative graph are now proved below;
distributional potential multiplication is also identified below.
These original numerical operator bounds use the maximum pair norm. The finite-`p`
comparison with the dissertation's component-sum norm is now proved in `PairNorm`;
`PairNormHeight` transfers the spectral-height conclusions without increasing constants.

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
maximum norm; finite-`p` comparison with the dissertation's pair norm is proved below.

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
on pairs; the physical-space realization remains open. The finite pair-norm comparison is proved below.

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

The canonical period-one coefficient embedding and its physical integral
identification for integrable functions are now proved below. The forward
distributional realization and period-one characterization are also proved below;
distributional potential multiplication is also identified below. The actual rectangular contour
identification is also proved below.

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
a norm-dependent height. Its Hilbert case and finite coefficient pair-norm
transfer are now proved below. The printed general-`p` height and the full
physical Fourier realization remain separate obligations.

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
The classical endpoint interpretation and the Sobolev-domain isomorphisms of
Lemma 4.2 and the physical equation transfer in Lemma 4.1 are now proved below. The interval-extension construction below connects
physical finite integrals to these base coefficient spaces and gives the uniform
bounded, analytic extensions for every `1<p<∞`, proving the coefficient part
of Lemma 4.3.

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

The uniform interval-extension estimates needed for transfer are now available
below. The physical Fourier and Sobolev identifications still need to be connected
to Theorem 1.4 and Lemma 4.5 for the original period-one potentials.

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
the full-range Hilbert bounds established below then give the interval-map
estimates for all other finite exponents above one. Only boundedness of the relevant
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
Hilbert boundedness and the full-range interval completions.

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
This proves the quartic Hilbert-kernel step. Its interval-map consequence is
included in the full-range construction below.

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
is not used. The resulting interval maps are now constructed as follows.

**The coefficient form of Lemma 4.3 is proved for every `1<p<∞`.**
Zero insertion along an injective integer index map is a linear isometry for
every Banach exponent, including `∞`. It fills the complement of the image
with zero. Applying it to `n↦2n` and `n↦2n+1` assembles the half-interval map
`Q a`, with `(Q a)(2n)=a(n)/2` and `(Q a)(2n+1)=i(Sa)(n)/2`.
If `Kₚ=(hilbertTransformBound+‖d‖₁)/π` is the proved shifted bound, then
`‖Q a‖≤(1+Kₚ)‖a‖/2`. The even coefficients show that `Q` is injective.
On finite polynomials it is exactly `polynomialHalfCoeffs`, hence equals the
normalized physical integral over the original unit interval.

For either boundary sign `ε`, the completed amplitude is
`A(a₁,a₂)=Q a₂+ε reflection(Q a₁)` and the ambient extension is
`(ε reflection(A), A)`. Its norm equals the amplitude norm, and the bound
`(1+Kₚ)‖(a₁,a₂)‖` holds in the maximum pair norm. The map lands in the selected
Dirichlet or Neumann space for every input. `intervalExtensionToBoundary`
packages this actual boundary-valued continuous linear map, and its complex
analyticity is proved.

Both physical finite Fourier component integrals agree with the completed map.
Density makes the extension unique, and at `p=2` it equals the preceding
Parseval construction, preserving its sharper energy identity and injectivity.
For arbitrary inputs the even amplitude is `(a₂(n)+εa₁(-n))/2`; the odd amplitude
is `i(Sa₂(n)+εSa₁(-n-1))/2`, with the reflected odd index handled explicitly.
The finite source pair-norm comparison is now proved below. The full
Fourier/distribution realization and physical Sobolev-domain identifications
remain separate obligations before
claiming the entire physical formulation.

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
and its perturbed rank count is now proved. Identification with the actual
integral over the rectangular boundary is proved below.
Agreement with the resonant determinant zero orders is now proved on distant
strips below. A general global characteristic-function identification remains open.

The weighted topology is induced by the weighted `lp` norm. A type synonym
prevents accidental inheritance of pointwise convergence from raw sequences.

## Continuous Fourier representatives

Absolutely summable coefficients now synthesize to continuous functions on the
period-two circle, with uniform norm at most the coefficient `ℓ1` norm. The
normalized physical integrals over `[0,2]` recover every coefficient. Fourier
coefficients determine a continuous function everywhere, giving injectivity and
uniqueness of the representative.

Composing with the one-derivative embedding gives `sobolevSynthesis` for every
`1 ≤ p < ∞`, with uniform norm bounded by `C_p ‖a‖ ≤ 2p ‖a‖`. Its Fourier series
converges in the uniform norm, as do the finite weighted truncations. Evaluation
at every real point is a bounded linear trace functional. Weighted frequency
reflection agrees with physical reflection `x ↦ 2-x`; it fixes both original
interval endpoint traces, and odd reflection symmetry forces them to vanish.
All integer modes are retained. In particular, odd modes are period two and
need not be period one.

At `p=2`, the representative agrees as an `L²` class with the inverse of
mathlib's normalized Fourier Hilbert basis, so its normalized `L²` norm equals
the raw coefficient norm.

The Fourier derivative now has an actual square-integrable realization on the
physical interval. Pullback of circle Haar measure to a full interval retains the
normalization factor two. Integration from zero to any `x ∈ [0,2]` is a bounded
linear functional on the circle `L²` space; continuous extension of the single-mode
fundamental theorem yields

`f(x) = f(0) + ∫₀ˣ g(t) dt`,

where `f` is `sobolevSynthesis a` and `g` realizes the Fourier derivative. A
vector-valued absolute-continuity lemma proves that `f` is absolutely continuous
on `[0,2]`. The Lebesgue differentiation theorem identifies `g` with the actual
classical derivative almost everywhere. Consequently `deriv f` is in physical
`L²`, and its normalized Fourier integrals are exactly `i π n aₙ`. This proves
the forward classical Sobolev realization needed for Lemmas 4.1–4.2.

The converse is now proved on the period-two circle. Real and imaginary
projections give almost-everywhere complex differentiability of absolutely
continuous functions. A vector-valued fundamental theorem then gives complex
integration by parts. For any complex AC function on `[0,2]` with integrable
classical derivative, its derivative coefficient is

`(f′)ₙ = iπn fₙ + (f(2) - f(0))/2`,

including `n=0`. Matching endpoints cancel the boundary term. Parseval for both
`f` and `f′` then gives the one-derivative weighted `ℓ2` condition. The constructed
`sobolevCoefficients` and `sobolevSynthesis` satisfy both inverse identities, and
`HasPeriodicH1Regularity` is equivalent to existence of a unique weighted
representative. This classical regularity characterization supplies the physical
energy comparison and the original interval-domain isomorphisms below. The
general Fourier/distribution realization remains open.

## Classical interval reflection

`HasIntervalH1Regularity` now describes absolute continuity on `[0,1]` and square
integrability of the actual derivative. No period-one endpoint condition is
imposed. Arbitrary `L²` data can be folded across the midpoint; matching values
at the join give the integral reconstruction

`folded ε f g(x) = f(0) + ∫₀ˣ folded (-ε) f′ g′(t) dt`.

Thus the fold is absolutely continuous and its classical derivative agrees
almost everywhere with the reflected derivative of opposite sign. That derivative
is square integrable. Matching at the outer endpoints then gives a continuous
period-two lift, with the same classical regularity and exact physical values on
the whole closed period. Its weighted coefficients are the normalized interval
Fourier integrals.

For pairs, `HasClassicalIntervalDomain` uses the original equal-component
Dirichlet conditions or opposite-component Neumann conditions at both endpoints.
`classicalIntervalExtension` constructs the signed component-swap extension in
`Domain 2` and proves membership in the selected weighted boundary subspace.
Synthesis recovers the physical extension everywhere on `[0,2]`, and restriction
recovers the original pair everywhere on `[0,1]`. Equal extensions therefore
identify the original functions on that interval, independently of values outside
it.

Conversely, `classicalIntervalRestriction` synthesizes a weighted boundary pair.
Its components have classical `H¹` regularity on `[0,1]`, and the frequency
reflection graph implies the equal or opposite values at both endpoints.
Folding this restriction recovers its physical representative, and taking
coefficients recovers the original weighted pair. Extension and restriction are
therefore inverse after identifying original functions by equality on `[0,1]`.
Each original classical pair has a unique weighted boundary representative.
This proves the set-theoretic domain identification in Lemma 4.2. Physical norm
comparison, continuous linear equivalences, and the classical equation transfer
are now proved below. Both boundary cases use the Dirichlet extension of the
potential, including for Neumann eigenfunctions. The converse identification of
the original spectra remains open.

## Physical Sobolev norm comparison

`intervalH1Energy f a b` is the sum of the ordinary Lebesgue integrals of `|f|²`
and `|f′|²`. It depends only on the function on the closed interval. For a
weighted period-two representative, Parseval gives the exact identity

`E(synthesis a; 0,2) = 2 (‖scalarInclusion a‖² + ‖derivative a‖²)`.

The factor two is the physical period length, and the derivative includes the
symbol `iπn`. Comparing `(1+|n|)²` with `1+π²n²` gives

`‖a‖² ≤ E(synthesis a; 0,2) ≤ 2π² ‖a‖²`.

For arbitrary square-integrable halves, signed reflection adds their energies
without a cross term. Applied to classical `H¹` data, the derivative reflection
has the opposite sign almost everywhere, so the same identity holds for the
full Sobolev energy, even when the fold has a corner. No behavior outside the
original interval enters these formulas.

`classicalIntervalEnergy f` sums the two component energies on `[0,1]`, and
`classicalIntervalNorm f` is its square root. Each extended component has exactly
that total energy. The two weighted component norms agree by signed reflection,
so the repository's maximum pair norm satisfies

`‖classicalIntervalExtension f‖ ≤ classicalIntervalNorm f`

and

`classicalIntervalNorm f ≤ √2 π ‖classicalIntervalExtension f‖`.

The corresponding bounds hold under restriction of every weighted boundary
pair. For classical endpoint-domain data, zero physical norm means equality to
zero everywhere on `[0,1]`, including both endpoints. These are explicit norm
estimates for Lemma 4.2 and are used in the bundled equivalences below.

## Classical boundary-domain isomorphisms (Lemma 4.2)

`ClassicalIntervalDomain b` consists of actual functions on the closed interval
`[0,1]`. It has pointwise complex vector operations, and membership is equivalent
to coming from an original `HasClassicalIntervalDomain b` function. In particular,
every original classical input is admitted, and values outside the interval
have no role in equality. Stored functions are continuous and satisfy the equal
or opposite component condition at each endpoint.

The norm comes from an injective linear embedding into the Euclidean product
of the actual period-two `L²` function and derivative spaces, scaled by `√2`.
The exact energy identity proves that this norm is **equal** to the physical
component-sum `H¹` norm for every original classical input.

`classicalIntervalEquiv b` is a continuous linear equivalence from this physical
interval domain to `b.domain` at exponent two. The forward map is exactly the
signed extension with its normalized Fourier integrals, and the inverse is
physical restriction at every point of `[0,1]`. Their operator norms are bounded
by `1` and `√2 π`, respectively. Both original interval domains are complete.
This establishes Lemma 4.2 in the classical `H¹` realization. Lemma 4.1's physical
equation transfer, original eigenvalue-set identification, and high-index
analytic branches and the original operator/resolvent correspondence are proved
below, along with physical root-space and algebraic-multiplicity identification.

## Physical multiplication and the Hilbert operator

`circleMul` multiplies a continuous period-two function with an arbitrary `L²`
class. It agrees with their pointwise product almost everywhere and obeys
`‖circleMul f g‖₂ ≤ ‖f‖∞ ‖g‖₂`. The operation is bounded and complex bilinear.
Multiplication by a Fourier wave shifts coefficients and preserves the `L²`
norm. Applying this operation to a uniformly convergent Fourier series proves

`circleMul (continuousSynthesis a) (l2Synthesis φ) = l2Synthesis (convolution φ a)`

for every `φ : Coeff 2` and `a : Coeff 1`. Consequently the existing
`potentialMul` at exponent two is actual multiplication by an arbitrary `L²`
potential on the classical `H¹` domain. Its output is square integrable and its
normalized physical Fourier integrals equal the convolution coefficients.
No smoothness or finite support is imposed on the potential.

`physicalOperator` is the actual expression

`(i f₋′ + φ₋ f₊, -i f₊′ + φ₊ f₋)`.

The synthesized coefficient operator equals this expression almost everywhere
on `[0,2]`, and the physical output lies in `L²`. The continuous domain and base
representatives agree almost everywhere; equality on one physical period
determines the coefficient pair. A domain vector is zero exactly when its
physical representative is zero almost everywhere. Finally,
`operator_eq_smul_iff_physical` proves both directions between the coefficient
and physical eigen-equations on a full period.

These results establish the physical Hilbert-space multiplication and operator
bridge used in the interval transfer below. The general `FLᵖ` distribution
product beyond the Hilbert realization remains open.

## Classical interval equation transfer (Lemma 4.1)

`periodTwoL2Coefficients` takes the actual normalized Fourier integrals of
arbitrary square-integrable data on `[0,2]`. A measurable circle lift and Fourier
completeness prove reconstruction almost everywhere, including potentials with
jumps and without matching endpoints. Synthesis and extraction are inverse,
and the coefficients depend only on the original a.e. function.

For every original `L²` pair `φ`, `dirichletPotentialCoefficients φ` reconstructs
`intervalExtension .dirichlet φ` almost everywhere on `[0,2]` and lies in the
actual Dirichlet coefficient subspace. No endpoint regularity is required of
the potential.

For either classical endpoint domain, the actual differential expression obeys

`L(φdir)(extension_b f) = extension_b(L(φ) f)`

almost everywhere on the doubled interval. Reflection transports a.e. equations;
the derivative acquires the required minus sign. The potential is Dirichlet
reflected for **both** choices of `b`. Consequently an original equation
`L(φ)f = z f` yields the existing coefficient equation for
`classicalIntervalExtension b f`, with the same eigenvalue `z` and with the
reconstructed Dirichlet potential coefficients. The extended vector belongs
to the chosen weighted boundary domain and realizes the classical periodic
`H¹` extension. A nonzero original function on `[0,1]` remains nonzero.

This proves Lemma 4.1's classical eigenfunction transfer. The original eigenvalue
belongs to both the selected coefficient boundary spectrum and the periodic
spectrum of `φdir`.

## Original interval eigenvalue sets

`classicalEigenvalues b φ` is defined directly by the original physical equation
almost everywhere on `[0,1]`, classical `H¹` regularity, the selected endpoint
conditions, and nonvanishing on the interval. Its definition uses no Fourier
coefficients. A.e. equal potentials give the same eigenvalue set.

The coefficient potential restricts to the original potential almost everywhere.
Every coefficient eigen-equation therefore restricts to the original equation.
For boundary vectors, the restriction satisfies the classical endpoint domain;
injectivity of restriction ensures that a nonzero vector remains nonzero.
Together with forward extension, this proves exact equality with the selected
coefficient boundary spectrum.

Consequently the original eigenvalue sets are closed, have the discrete subspace
topology, and meet every bounded region in finitely many points. Their union is
the periodic coefficient spectrum of the Dirichlet-reflected potential. For the
zero potential both original sets are exactly `πℤ`, with odd indices retained.

These are eigenvalue-set identities. The independently defined original
interval operator and its resolvent correspondence are now constructed below.
Physical algebraic multiplicities require the independent root-space correspondence proved below.
Analytic branches and uniform coefficient counting data are now pulled back to
the physical potential space below.

## Physical potential parameters and analytic eigenvalue branches

`IntervalPairL2` is the original pair of scalar Lebesgue `L²[0,1]` classes with
the component-sum Hilbert norm. It is a complete complex normed space, has no
endpoint conditions, and is represented by actual square-integrable functions.
`intervalL2OfFunction` identifies exactly a.e. equal original functions. The
squared norm equals the sum of their two unnormalized interval energies.

The actual Dirichlet-reflected potential coefficients depend only on this class
and respect addition and complex multiplication. Parseval and reflection give

`‖intervalPotentialToDirichlet u‖ = (√2 / 2) ‖u‖`.

This is the exact normalization for the existing maximum coefficient-pair norm.
It proves boundedness and injectivity of the map into the actual Dirichlet
coefficient subspace. The map is complex analytic and agrees with the previously
constructed original Fourier integrals, even for nonsmooth potentials.

`classicalEigenvalue b u n` parameterizes the intrinsic trace branch by the
original physical potential. Pulling back the reflected-potential neighborhood
gives one open convex neighborhood containing both `u` and zero and one positive
cutoff for both boundary conditions. All larger cutoffs carry the existing
coefficient counting data. Every high disk contains exactly the corresponding
original classical eigenvalue, and the branch is analytic in the physical `L²`
norm. The original eigenvalue set is independent of the representative chosen.
Both free branches have the exact value `π n`.

This proves physical analyticity and uniqueness of the high-index classical
branches. The signed base-space, operator/resolvent, and root-space
correspondences below identify the coefficient multiplicities with independently
defined physical multiplicities and transfer simplicity and central counts.
The general-`p` physical parameter transfer and the exact central-height
convention also remain open.

## Signed physical base-space isomorphisms

The weighted domain inclusion has dense range in either coefficient boundary
space. Physical Dirichlet extension of a restricted classical domain vector
recovers precisely its unweighted coefficients, so the image of the physical
potential map contains this dense range. Its lower norm bound makes its image
closed, proving surjectivity onto the full Dirichlet coefficient subspace.

`dirichletIntervalL2Equiv` bundles this map as a continuous linear equivalence.
Negating the second physical component and then the second coefficient component
turns Dirichlet reflection into Neumann reflection; both sign changes are
complex-linear isometric involutions. This gives `neumannIntervalL2Equiv`.
`BoundaryCondition.intervalL2Equiv b` selects the corresponding isomorphism from
the complete original physical `L²` space to `b.space`.

For either choice, the forward norm factor is exactly `√2/2` and the inverse
norm factor is exactly `√2`. Synthesis of the forward output agrees almost
everywhere with the actual signed extension of the original function, and each
output coefficient equals its normalized physical Fourier integral. The inverse
is actual restriction to `[0,1]` almost everywhere, for every boundary base
vector, without weighted regularity or endpoint hypotheses.

These maps commute with the domain/base inclusions. For an original classical
function, its base-space image equals the raw coefficients of its weighted
classical extension. Conversely, inverse base restriction of an included
weighted boundary vector is the physical `L²` class of its classical restriction.
This supplies the base-space part of the original operator and root-space
correspondences constructed below.

## Original interval operator and resolvent

`classicalInclusion b` embeds the original physical `H¹` endpoint domain into
`IntervalPairL2`; it is injective and has dense range. `classicalOperator b u`
is the bounded domain-to-base operator for an arbitrary original `L²` potential.
On original representatives it is exactly the `L²` class of

`diag(i,-i) f′ + (φ₋ f₊, φ₊ f₋)`.

This realization uses actual derivatives and holds without global smoothness,
period-one domain conditions, or pointwise representatives of the potential.
The output is square integrable. A.e. potential equality and equality of domain
functions on the original interval preserve the physical differential action.

The physical pencil is defined as `z • classicalInclusion - classicalOperator`;
`classicalResolventSet` is defined by its bijectivity. The base and domain
isomorphisms intertwine it with the coefficient boundary pencil. Their resolvent
sets are equal, open, and nonempty. `classicalResolventToDomain` is a bounded
two-sided inverse on that set. The physical base-space resolvent is conjugate
to the coefficient boundary resolvent and is compact. `classicalSpectrum`,
defined as failure of physical-pencil invertibility, equals both the coefficient
boundary spectrum and the original classical differential-equation eigenvalues.

`classicalUnboundedOperator` is a partial linear map on the physical base space.
Its domain is exactly the `L²` classes admitting original classical `H¹`
representatives with the selected endpoint conditions, independently of the
potential. Evaluation is the class of the actual differential expression. The
domain is dense. A physical resolvent identity recognizes graph points using
only base-space data, proving that the graph and the unbounded operator are
closed. No convergence in the stronger domain norm is required for closedness.

## Original physical root spaces and algebraic counting

`classicalRootSpace b u z n` is defined recursively from the original physical
pencil and inclusion, requiring the classical domain at every step. Level one
is the included ordinary eigenspace; higher levels retain full Jordan chains.
The physical Fourier isomorphism preserves each level and the increasing union
`classicalRootSpaceTop`. The union lies in the actual unbounded operator domain,
is finite dimensional and closed, and stabilizes at a finite chain length.

`classicalAlgebraicMultiplicity` is the dimension of this full physical root
space. A proved linear equivalence identifies it with coefficient multiplicity.
It is positive exactly on the physical spectrum and zero exactly on the
resolvent set. All free boundary eigenvalues, including negative odd indices,
have multiplicity one. Periodic multiplicity of the reflected potential is the
sum of the two original physical boundary multiplicities.

`classicalCentralSpectrum` is the finite intersection of the independently
defined physical spectrum with the existing central box. On one open convex
physical neighborhood containing the chosen potential and zero, both boundary
conditions have central multiplicity sum `2N+1`, one algebraically simple
spectral point in each high disk, and no other spectrum. One cutoff works for
every larger cutoff, and the high-index branches are analytic on that same
neighborhood. These statements now use physical spectra and physical root-space
multiplicities throughout. The box still has height `N`; the overview theorem's
norm-dependent height and general-`p` physical interpretation remain open.

## Actual rectangular resolvent contours

`RectangleIntegral.integral` is the sum of four actual oriented Bochner edge
integrals. Ordered lower-left and upper-right corners give counterclockwise
orientation, with the factor `i` on the vertical edges. Continuity on the full
boundary gives all four integrability conditions without assuming anything in
the interior. Boundary equality determines the integral, and bounded complex
linear maps and evaluation commute with it.

Horizontal and vertical subdivision cancel the oppositely oriented common edge.
Cauchy's theorem makes the integral over an analytic filled rectangle vanish;
combined with subdivision, it proves invariance when an edge moves through an
analytic strip. These are Banach-valued results and apply to operator norms.

`resolventRectangleIntegral` and its domain-valued version use the same
normalization `(2πi)⁻¹` as the circular contour. On a resolvent boundary the
actual integral factors through the weighted domain and is compact. It commutes
with every full resolvent and every algebraic root-space projection. A filled
resolvent rectangle contributes zero, and moving either a horizontal or vertical
edge through a filled resolvent strip preserves the contour operator. The
retained rectangle's interior need not be in the resolvent set.

`centralLowerCorner` and `centralUpperCorner` give exactly the existing closed
central rectangle and its boundary, including corners. `centralRectangleIntegral`
is the actual integral along those four edges. The existing common neighborhood
makes every sufficiently large central contour integrable in the domain norm,
with a compact base-space integral. The enclosed-pole selection and
whole-space enclosing-circle comparison below prove equality with
`centralSpectralProjection`. The overview theorem's norm-dependent height
remains separate.

## Rectangular residues and full root-space selection

The scalar kernel `(ζ-a)⁻¹` integrates to `2πi` for every strictly enclosed pole
in an ordered rectangle. Horizontal and vertical fundamental-theorem formulas
use logarithmic primitives; changing to `log(a-ζ)` on the left edge accounts for
the two logarithm branch values. Poles outside the filled rectangle contribute
zero. Every higher inverse power has a single primitive along all four edges,
so its integral vanishes even when the pole lies inside the contour.

The resolvent recurrence along finite Jordan chains now gives the corresponding
weighted rectangular integral formula. The only nonzero contribution is the
simple-pole term. Thus the normalized integral fixes every vector of each full
root space strictly inside the rectangle and annihilates every full root space
outside it. Resolvent boundary points contribute zero. Composition with any
finite algebraic cluster projection filters exactly its enclosed full root
spaces, without a diagonalizability assumption.

For the actual central corners this proves

`centralRectangleIntegral * centralSpectralProjection = centralSpectralProjection`.

Consequently the range of the central algebraic projection lies in the range
of the actual rectangular integral. The whole-space comparison below supplies
the additional argument needed for operator equality, including the complementary
component outside finite spectral clusters.

## Whole-space rectangular contour identification

Continuous Banach-valued functions on the product of a rectangular boundary
and a circle satisfy the mixed-contour Fubini identity. Continuity on the
contours suffices; the interiors may contain poles. The proof uses integrability
on compact parameter rectangles and retains the orientation factors on all
four straight edges and the circle.

For a resolvent circle enclosing the entire filled rectangle, integrating the
resolvent identity in both parameters proves

`resolventRectangleIntegral * resolventCircleIntegral = resolventRectangleIntegral`.

This identity holds on the entire base space. A sufficiently large admissible
circle therefore captures all action of the rectangular operator. The circular
projection is already identified with its finite spectral cluster; rectangular
root-space selection filters that cluster to exactly the central spectrum.
Consequently `centralRectangleIntegral_eq_centralSpectralProjection` proves
equality of the actual four-edge integral and the central algebraic projection
whenever the central boundary lies in the resolvent set.

The rectangular integral is idempotent, its range is exactly the sum of the
central full generalized eigenspaces, and its rank is the sum of their algebraic
multiplicities. One open convex neighborhood containing the potential and zero
makes every sufficiently large rectangular projection analytic in operator norm
with rank `4N+2`. This closes the rectangular contour identification for the
existing height-`N` box. The overview's exact norm-dependent height and the
remaining physical Fourier/distribution interpretation are still open.

## Explicit heights and the Hilbert central box

`ExplicitHeight` proves the concrete norm-ball resolvent bound
`|Im z| ≥ (1 + 8 p M)^p` for `‖φ‖ ≤ M`, at every finite Banach exponent.
At `p=2`, the sharper printed height `(1 + 8 M)^2` suffices, including both
horizontal edges. Consequently every spectral value lies strictly inside the
corresponding horizontal strip. The estimates include zero potentials.

`HeightSpectralBox` defines bounded central boxes with independent heights and
their finite spectral sets. A global strip bound identifies their spectral
sets with the height-`N` central spectrum for sufficiently large `N`.
For `p=2`, one open convex neighborhood containing the potential and zero now
has count `4N+2` in each potential's box of height `(1 + 8 ‖ψ‖)^2`, for every
larger cutoff. Its full cluster projection equals the existing height-`N`
rectangular integral. The actual moving-height boundary integral is now
identified below as well.

Source fidelity: the printed Proposition 3.1 (p. 23) uses `(1 + 8 ‖φ‖ₚ)^p`,
while Lemma 3.2(ii) and Corollary 3.3 (p. 24) retain `4p` in the numerical
estimate. At `p=3`, norm bound one and printed height `729`, that numerical
expression is `12/9 + 1/729 > 1`. This only shows that direct substitution
cannot justify the height from this estimate; it does not refute the spectral
claim. A checked example also puts that parameter in the actual resolvent of
a nonzero real-type potential. The all-exponent result above deliberately
retains the factor `p`. The printed height for arbitrary finite `p` remains
open. These original estimates use coefficient maximum pair norms. The finite
component-sum norm comparison and height transfer are now proved below.

## Arbitrary rectangles and moving-height contours

`RectangleSpectrum` defines the finite enclosed spectrum of any rectangle and
proves agreement of open and closed selections when the ordered boundary lies
in the resolvent set. Every bounded set admits an enclosing resolvent circle.
The actual four-edge rectangular integral therefore equals its full finite
cluster projection, is idempotent, has exactly the enclosed generalized-eigenspace
range, and has rank equal to the total enclosed algebraic multiplicity. Any two
ordered admissible rectangles selecting the same spectrum define the same
operator. The previous central rectangle proof now uses this general theorem.

`HeightRectangleContour` constructs the two corners and actual integral at an
independent height. The global high strip controls the horizontal edges, while
the existing height-`N` boundary controls the vertical edges when `H ≤ N`.
The resulting actual integral equals the whole central spectral projection.
A uniformly bounded sufficient height function gives analytic integral operators
and rank `4N+2` on one open convex neighborhood containing the potential and zero,
for every sufficiently large cutoff. The height function itself needs no
continuity or analyticity assumption: local equality to the fixed-contour
projection supplies analyticity.

This applies both to the printed Hilbert height `(1+8‖ψ‖)^2` and to the proved
all-exponent height `(1+8p‖ψ‖)^p`. Thus the actual moving norm-height contour
formula is now proved for those heights. The finite coefficient pair-norm
transfer is proved below; the printed general-`p` height remains open.

## Finite-exponent source pair norms and parameter transfer

`CoeffPair p` and `WeightedCoeffPair w p` are actual complete complex normed
spaces with the component-sum `lp` norm. For every finite `p≥1`, their `p`-th
norm powers equal the sums of both coefficient energies. At arbitrary real
Sobolev regularity `s`, the weight in the combined energy is exactly
`(1+|n|)^(s*p)`, as in Chapter 1, equation (1.2), printed page 22.
Continuous linear equivalences preserve all coefficients while identifying
these spaces with the existing maximum-norm products. The forward norm bound
is one; the reverse factor is exactly `2^(1/p)`, attained by equal components.
The distinct infinity-endpoint construction is given in `PairNormInfty` below.

The source-norm parameter map is contractive, so all-exponent height
`(1+8pM)^p` and printed Hilbert height `(1+8M)^2` remain sufficient when `M`
bounds the component-sum norm. Their horizontal edges lie in the resolvent
set and the whole spectrum lies strictly inside. An open convex neighborhood
containing the parameter and zero is constructed in `CoeffPair p` itself.
The actual norm-height contour projections are analytic there and have rank
`4N+2` for every sufficiently large cutoff. The height function can be any
uniformly bounded sufficient height, with no regularity assumed.

This completes the finite coefficient pair-norm comparison and the potential
parameter transfer for the proved heights. Operators in these contour statements
still act on the original coefficient base space. The physical distributional
realization and the source's infinity norm are implemented below. The printed
general-`p` height remains open.

## Canonical period-one embedding and physical Fourier integrals

`PeriodDoubling` identifies a period-one frequency `n` with period-two frequency
`2n`, inserting zeros at odd indices. It is a complex linear isometry onto the
entire closed even coefficient subspace, including both scalar endpoints.
The inverse samples even frequencies. Sampling and reinserting any sequence
gives exactly the existing even projection, and sampling is contractive.
Convolution commutes with period doubling for the proved `lp × l1` product.
This supplies the canonical coefficient identification before Lemma 3.6
(Chapter 1, printed page 26).

`PeriodOneCoefficients` proves the physical integral formula by splitting
`[0,2]` into two halves and translating the second half. For a period-one
function integrable over `[0,1]`, the even normalized period-two coefficients
are exactly its unit-period coefficients and all odd coefficients vanish.
If its unit-period coefficients lie in `lp`, the actual period-two integral
sequence lies in the same `lp` space with exactly the same norm. This proof
allows jumps. Absolutely summable input coefficients have an injective
continuous physical period-one synthesis, whose actual unit-interval integrals
recover every input coefficient. Its series uses `exp(2πinx)`.

`PeriodOneEmbedding` applies insertion to both components in the source's
finite-exponent component-sum norm. The pair map is isometric; the operator
parameter map is contractive and covers exactly the even potential subspace.
At absolute summability, both components are identified with actual physical
period-one functions. These embedded parameters automatically satisfy the
existing resolvent and spectral contour parity hypotheses.

The following milestone extends this construction to general Banach coefficient
data, without assuming an integrable function representative.

## Genuine distributional Fourier synthesis

`SchwartzSampling` bounds the signed half-integer samples `g(-n/2)` by
`16 S(g)/(1+|n|)^2`, where `S` is a finite supremum of standard Schwartz
seminorms of decay degree at most two and derivative degree zero. This gives a
continuous complex-linear map from mathlib's Schwartz space into `Coeff 1`.
`TestDuality` supplies the bounded, unconjugated coefficient pairing, so the
test action is complex-linear rather than conjugate-linear.

`DistributionSynthesis` maps each `a : Coeff p`, for every `1 ≤ p ≤ ∞`, into
mathlib's actual `TemperedDistribution ℝ ℂ`. Its action on a Schwartz test is
`Σ_n a_n (𝓕g)(-n/2)`, with absolute convergence. The map is complex-linear and
continuous for mathlib's pointwise distribution topology. A smooth frequency
bump of radius `1/4` isolates each half-integer lattice point; its inverse
Fourier transform tests the corresponding original coefficient exactly. Thus
the synthesis map is injective. The normalization is verified by actual
real-line integrals: a single coefficient at `n` acts as its amplitude times
integration against `exp(iπnx)`. Finite Fourier truncations converge in the
distribution topology, including at `p=∞`, where norm convergence of coefficient
truncations is not asserted.

`DistributionPeriodicity` proves the physical translation law on Schwartz tests.
All synthesized distributions have period two. Period one holds if and only if
the coefficients have even support, extending the earlier period-doubling map to
actual distributions. For absolutely summable coefficients, exchanging the
Fourier sum with the integral proves agreement with the existing continuous
period-two synthesis and period-one synthesis on every Schwartz test.

This completes the forward realization and exact recovery for Banach coefficient
data. The following milestone identifies actual distributional differentiation.
Potential multiplication and the intrinsic converse for unweighted Banach classes
are proved below. No function representative is assumed for general coefficient
data. The weighted extension for every real Sobolev exponent is also proved below.

## Exact distributional derivative and free operator graphs

`DistributionDerivative` proves the Fourier transform formula for differentiated
Schwartz tests at the signed half-integer lattice. The actual tempered-distribution
derivative of synthesis has multiplier `iπn`. Localized tests recover those
derivative coefficients even when they no longer lie in the original `lp` class.
For `a,b : Coeff p`, the equation `D(Ta)=Tb` is equivalent both to the coefficient
identity `b_n=iπn a_n` and to the existence of `f : ScalarDomain p` with
`scalarInclusion f=a` and `derivative f=b`. Thus the existing one-derivative domain
is exactly the distributional derivative domain in the same Fourier class,
including at infinity. The weighted-membership estimate used for the converse
is now shared with the existing classical Hilbert Sobolev identification.

Synthesis is independent of the Banach exponent used to package identical raw
coefficients. Consequently, for every finite exponent the domain's synthesized
distribution agrees with integration against its continuous Sobolev representative.
Its derivative acts as minus the integral against the actual derivative of a
Schwartz test. This is a real-line weak integration-by-parts identity, without
an unproved classical derivative assumption at non-Hilbert exponents.

`DistributionFreeOperator` constructs the actual signed differential operator
`diag(i,-i)D` on pairs of tempered distributions. The injective continuous pair
synthesis intertwines it with `freeOperator`, both pointwise and as a continuous
linear-map identity. The distributional free equation is equivalent to the
signed coefficient equations and to the exact existing pair-domain graph.
Pulling back the closed distributional equality proves that the scalar and
pair free graphs are closed for every Banach exponent. At infinity this also
gives stability under limits in the two base coefficient norms, without assuming
convergence in the stronger domain norm.

The following milestone identifies distributional potential multiplication.
The separate source infinity pair norm is implemented below.

## Actual distribution multiplication and the full operator

`DistributionModulation` proves smoothness and exact iterated derivatives for
every period-two wave, and hence temperate growth. Mathlib's multiplication of
actual tempered distributions by a wave is exactly the coefficient shift.
Finite Fourier polynomials therefore give precisely the existing truncated
convolution product under the genuine smooth-multiplier API. No totalized
smooth-multiplier operation is used on a nonsmooth function.

`DistributionProduct` proves that synthesis of convolution is the unique
continuous extension of that smooth operation from Fourier polynomials to
`ℓ¹` multiplier coefficients. It is jointly continuous in the two coefficient
norms, has a quantitative bound on every Schwartz test, and is independent of
arbitrary converging coefficient approximations. It depends only on the actual
potential distribution, independently of the coefficient exponent used to
represent it. The potential may lie in any
Banach `lp`, including infinity. The multiplier remains in `l1`.

`TestConvolution` transposes convolution onto reflected test coefficients using
absolute convergence on the product lattice. `ProductTestSamples` identifies
that test sequence with actual real-line Fourier integrals of the continuous
multiplier times the Schwartz test, with an `l1` norm bound. Thus the extended
product's action is an absolutely convergent integral series even when the
multiplied test is not Schwartz. For temperate smooth multipliers this proves
agreement with Mathlib's actual distribution multiplication. For `l1` potential
data as well, it proves agreement with ordinary multiplication of the two
continuous synthesized functions under integration.

`DistributionPotential` applies this extension to the existing finite-exponent
one-derivative domain. The test-integral formula uses its actual continuous
Sobolev representative, and the bound retains the existing scalar domain
constant. Both the canonical Fourier truncations and arbitrary finite Fourier
approximations converging in the domain norm give the same product, even with
simultaneously varying potentials. The signed actual distribution derivative
plus the off-diagonal extended products agrees exactly with `operator hp φ`.
Injectivity of synthesis identifies both general operator equations and
distributional eigenvalue equations with the coefficient equations already
used in the spectral theory.

This is the full operator identification on the realized Fourier domain.
The intrinsic characterization of arbitrary periodic tempered distributions in
these Fourier classes, including the full real Sobolev scale, is proved below.
The separate source infinity pair norm is implemented below.

## Schwartz periodization and the converse bridge

`SchwartzPeriodization` constructs a continuous complex-linear map from genuine
Schwartz tests on the real line to continuous functions on the period-two circle.
Poisson summation proves that its value is exactly `Σ_k g(x+2k)`, with absolute
convergence proved separately. Its normalized coefficient at `n` is
`(1/2)(𝓕g)(n/2)`, and integration over one period recovers the real-line integral.
The frequency reflection and period factor are explicit throughout.

The coefficient-extracting test at `n` periodizes to `(1/2) fourier(-n)`.
In particular, the zero-mode test is a Schwartz window whose translates sum to
one half. Finite sums of these tests explicitly lift every Fourier polynomial;
testing the lift against a synthesized distribution gives the reflected finite
coefficient pairing, with factor two and no complex conjugation. The Fourier
polynomial density theorem implies uniform density of Schwartz periodizations
in continuous circle functions.

Periodization is invariant under test translation by two. Its kernel consists
exactly of tests whose Fourier transform vanishes at every half-integer, and
also exactly of tests annihilated by every synthesized distribution at any fixed
Banach exponent, including infinity. Synthesized distributions therefore assign
the same value to tests with equal periodization.

Uniform density alone does not suffice for arbitrary distributions. The subsequent
smooth approximation, Schwartz reconstruction, and kernel arguments below
complete the converse for unweighted Banach coefficient classes.

## Smooth periodization and all derivative orders

`SchwartzPeriodizationSmooth` proves a general classical differentiation theorem
for absolutely summable Fourier data whose differentiated coefficients are also
absolutely summable. Applying the Schwartz Fourier derivative identity proves
that periodization commutes with the actual real-line derivative at every point.
Induction gives all finite smooth orders and genuine `C∞` regularity.

`periodizationDerivCLM k` is a continuous complex-linear map from Schwartz space
to continuous circle functions. Its physical pullback is exactly the `k`th
classical derivative of periodization. Its uniform norm bounds that derivative
on the whole real line. Consequently, periodizations satisfy Mathlib's actual
`HasTemperateGrowth` condition and can multiply Schwartz tests through the
genuine smooth-multiplier API.

The Fourier coefficients of the `k`th derivative multiply the original ones by
`(iπn)^k` and remain absolutely summable. The same finite Fourier polynomials
converge uniformly to periodization together with each fixed derivative order,
using arbitrary finite lattice cutoffs. Every derivative also equals the
absolutely convergent physical translate sum of the corresponding Schwartz
derivative. Thus approximation now controls all smooth orders, beyond the earlier
uniform density statement.

The subsequent windowed reconstruction in Schwartz topology and the periodic-
distribution kernel argument below complete the unweighted Banach converse.

## Windowed Fourier reconstruction in Schwartz topology

`SchwartzMultiplierConvergence` proves a weighted Leibniz estimate for smooth
multiplier products with a fixed Schwartz window. At polynomial weight `k` and
derivative order `n`, a common uniform bound on multiplier derivatives through
order `n` controls the product seminorm by the finite sum of window seminorms
with exact binomial coefficients. The polynomial weight remains `k` throughout.

For arbitrary index types and filters, uniform convergence of every derivative
of temperate smooth multipliers now implies convergence of the products in the
actual Schwartz topology. Each weighted seminorm uses only finitely many
uniform derivative estimates; the proof does not replace Schwartz topology by
pointwise or distributional convergence.

Applied to the established Fourier truncations of a periodized test, this gives
Schwartz convergence after multiplication by any fixed Schwartz window. The
finite products equal finite sums of modulated windows, so the resulting infinite
wave expansion has a genuine `HasSum` in Schwartz space. Every Mathlib tempered
distribution, with no periodicity or Fourier-class hypothesis, evaluates this
series term by term. Its scalar series converges absolutely.

The following milestone identifies the action on an arbitrary test with the
action on its normalized windowed periodization, proving the kernel criterion
and the intrinsic unweighted Banach coefficient characterization.

## Intrinsic identification of periodic tempered distributions

`SchwartzSeries` constructs a genuine Schwartz sum when every standard seminorm
is summable over the terms. Smooth-series differentiation and weighted derivative
bounds prove the sum is Schwartz. Its seminorm is bounded by the corresponding
scalar series; every finite truncation error is bounded by that series' tail.
This proves convergence in Schwartz topology directly, without assuming an
unavailable Schwartz completeness instance.

`SchwartzTranslateProduct` uses rapid decay of both Schwartz factors to bound
every weighted product seminorm by `C/(1+|m|)^2` when one factor is translated
by `2m`. The bilateral sum therefore converges in Schwartz topology, and its
pointwise values identify it with the fixed window times actual periodization.

`PeriodicDistributionKernel` defines period two by actual translation invariance
on all Schwartz tests and proves invariance for every signed integer multiple.
Translating each product term interchanges its two Schwartz factors and reverses
the lattice index. The two convergent series give periodization exchange under
any periodic tempered distribution. The zero-mode window's periodization one
half then gives `T(g)=2 T((Pg) coefficientTest(0))`. Thus arbitrary periodic
distributions act only on periodization, and period-two invariance is equivalent
to annihilating its full kernel.

`PeriodicDistributionIdentification` identifies modulated zero-mode windows with
the existing coefficient-extracting tests under every periodic distribution.
Windowed Fourier reconstruction consequently gives
`T(g)=Σ_n T(coefficientTest n) (𝓕g)(-n/2)`, with absolute convergence for every
Schwartz test and no coefficient regularity assumption. These coefficients
determine every periodic tempered distribution uniquely.

The main characterization is now an equivalence: actual period-two invariance
and `Memℓp` of the coefficient-test values hold if and only if there is a unique
`Coeff p` whose distributional synthesis equals the given tempered distribution.
It applies to every Banach exponent, including infinity without a vanishing-tail
assumption. This completes the intrinsic unweighted Banach Fourier-class
identification. The following milestone extends it to the full real Sobolev
scale; the distinct source infinity pair norm is implemented subsequently below.

## Weighted distributions and the full real Sobolev scale

`TemperedWeight` gives the precise hypothesis used for general positive weights:
the reciprocal weight must be bounded by a polynomial on the lattice. It proves
this for the unit weight and for `(1+|n|)^s` at every real `s`, by bounding `-s`
above by a natural exponent. No smooth extension of the lattice weight is assumed.

`WeightedSchwartzSampling` proves that `f(-n/2)/w(n)` is absolutely summable for
every Schwartz test. A sufficiently high finite family of standard Schwartz
seminorms absorbs the reciprocal-weight polynomial and leaves a summable inverse-
square envelope. This constructs an actual continuous complex-linear sampling
map from Schwartz space into `ℓ¹`.

`WeightedDistributionSynthesis` tests the weighted `lp` sequence against these
samples. The weight cancels exactly, leaving the absolutely convergent raw
Fourier action `Σ_n a(n) (𝓕g)(-n/2)`. The weighted norm controls each test action,
and synthesis is a continuous complex-linear map into genuine tempered
distributions. The existing coefficient tests recover every raw coefficient,
proving injectivity. The resulting distributions have actual period two.
Finite Fourier truncations converge in distribution topology even at infinity,
without any requirement that the raw coefficients be bounded. Equal raw data
has identical action across admissible weights and Banach exponents; compatibility
with the earlier unweighted synthesis is explicit.

`WeightedDistributionIdentification` applies periodic coefficient uniqueness to
prove the full intrinsic converse: actual period-two invariance and weighted
`Memℓp` hold exactly when there is a unique weighted synthesis representative.
The public Sobolev synthesis map and characterization cover every real exponent,
including negative and fractional exponents, and every Banach `p`, including
infinity.

`WeightedMultiplier` builds continuous linear maps from the pointwise inequality
`v(n) |m(n)| ≤ C w(n)`, retaining the same norm bound at all Banach exponents.
Monotone weights give contractive injective inclusions preserving raw values.
`SobolevDerivative` specializes these maps to all real Sobolev regularities.
The inclusions compose, and the period-two derivative has norm at most `π`
from regularity `s+1` to `s`. Applying the one-derivative domain criterion to
weighted data recovers exactly one regularity unit from a sequence and its
derivative in regularity `s`.

`SobolevDistributionDerivative` proves that regularity inclusions preserve the
actual distribution, and identifies differentiation with Mathlib's tempered-
distribution derivative, retaining the `iπn` multiplier. The derivative graph
in each Sobolev coefficient norm is exactly the included `s+1` space and is
closed, including infinity. An intrinsic criterion for arbitrary periodic
inputs characterizes regularity `s+1` by simultaneous regularity `s` of the
distribution and its derivative. All statements include negative fractional
regularity.

## Exact infinity pair norm and signed distributional realization

`CoeffPairInfty` is the actual `lp` space at infinity of pairs carrying their
local sum norm. Thus its norm is `sup_n (|a(n)| + |b(n)|)`, exactly the source's
endpoint convention following (1.2), printed page 22. It is a complete complex
normed space. Continuous linear equivalences identify the topology with the
existing maximum product; the forward bound is one and the reverse bound is
two, attained by equal signed sequences including nondecaying data.

The source's pair basis uses scalar frequency `-n` in its first component.
Consequently, `toMax` preserves signed coordinates, while `toScalarMax`
reflects the first sequence to enter the existing scalar-coordinate spaces.
In scalar coefficients the source supremum pairs the first component at `-n`
with the second at `n`. This matters at infinity: reflecting only one component
can change the frequencywise sum norm even though it preserves both scalar norms.

`WeightedCoeffPairInfty` retains raw signed weighted sequences and transports
its norm through weighting into `CoeffPairInfty`. This gives completeness and
exact `sup_n w(n)(|a(n)|+|b(n)|)` for every positive weight. The same sharp
comparisons hold. Every real Sobolev weight has an explicit scalar-coordinate
conversion using its reflection isometry, including negative fractional weights.

`PairDistributionInfty` synthesizes these weighted endpoint pairs continuously
and injectively into two genuine period-two tempered distributions. Coefficient
tests recover the first signed sequence at the reflected frequency and the
second directly. The exact source norm is recovered from these actual
coefficients. Every pair of periodic distributions with endpoint Sobolev
regularity has a unique representative in this source-norm space.

## Exponent embeddings and the Sobolev Hölder threshold

`ExponentEmbedding` proves that the identity from `ℓᵖ` to `ℓᑫ` is contractive
for every pair of Banach exponents `p≤q`, including infinity. A unit-ball
power comparison gives the exact constant one, then homogeneity removes the
normalization. The maps are continuous linear injections and compose. Weighted
transport keeps raw coefficients unchanged, and combining with the earlier
regularity inclusion gives a contractive map whenever `t≤s` and `p≤q`.

`HolderEmbedding` constructs continuous pointwise products for arbitrary Banach
Hölder triples with `1/q = 1/p + 1/r`. A target/source weight ratio in `ℓʳ`
therefore gives a continuous injective map of weighted coefficient spaces.
The norm is bounded by the explicit `ℓʳ` ratio norm times the input norm.
For finite positive `r`, the reciprocal Sobolev weight is in `ℓʳ` exactly when
its regularity times `r` exceeds one; restricting the series to nonnegative
frequencies proves necessity as well as sufficiency. At `r=∞`, nonnegative
regularity suffices. Thus the embedding from `FL^{s,p}` to `FL^{t,q}` follows
for every finite multiplier exponent with `(s-t)r>1`, retaining its explicit
constant. This is the coefficient estimate in Appendix A.9. The forward
physical interval bridge and resulting membership conclusions are described below.

`DistributionEmbeddings` proves that every exponent or Hölder embedding above
preserves the actual tempered distribution, across both weights and exponents.
An arbitrary periodic input satisfying the source Sobolev coefficient condition
has a unique target representative under the Hölder condition.

## Full discrete Young inequality: Appendix B.2

`YoungRelation` encodes exactly `1 + 1/r = 1/p + 1/q`, interpreting the
reciprocal of infinity as zero. Both input exponents are at most the output
exponent, and the second input embeds into the Hölder conjugate of the first.
This supplies absolute convergence of the scalar convolution sum at every
frequency for all admissible inputs, including the infinity endpoints.

`YoungTrilinear` uses weighted arithmetic-geometric mean with inverse
exponents summing to two. It bounds each product of three coefficient
magnitudes by a weighted sum of three products of energies. Finite translated
energy sums give a trilinear unit-ball bound one; homogeneity gives the product
of all three norms. `YoungFinite` expands the existing convolution into its
finite single-frequency sums. Finite conjugate norming tests then give the
full Young norm estimate uniformly over input supports.

`YoungInequality` includes the `l1` output and infinity output endpoints in
that finite bound. Simultaneous finite input cutoffs converge at every output
frequency by a summable Hölder majorant. The `lp` Fatou property proves that
the raw convolution belongs to the exact output exponent and retains the
constant-one bound. This proves Appendix B.2 without an `l1`-factor hypothesis.

`YoungConvolution` packages the result as a continuous complex bilinear map.
Its norm equals one, as unit single modes attain the bound. The construction
is commutative with exchanged input exponents and agrees with the previous
Banach-series convolution when the right factor is in `l1`. Single inputs
shift the other sequence after its contractive exponent inclusion. Arbitrary
norm-convergent input approximations converge in output norm. In particular,
both finite input cutoffs converge in the output norm whenever the inputs
have finite exponents, even for conjugate inputs with infinity output.
The distribution-product extension in Appendix A.7 and the mixed
three-sequence inequality in Appendix B.3 are now proved below.

## General periodic distribution products: Appendix A.7

`YoungDistributionProduct` synthesizes the full Young convolution into an actual
period-two tempered distribution for every Banach Young triple. Its recovered
coefficients are the absolutely convergent convolution series, and its unique
output coefficient representative has norm at most the product of the input
norms. It is intrinsically periodic and is characterized among all periodic
tempered distributions by these coefficients. This proves the product statement
and exact estimate of Appendix A.7 in the project's period-two convention.

The product is jointly continuous, commutative, and independent of both inputs'
coefficient-space representations, including changes of the output exponent.
Every finite multiplier agrees with Mathlib's actual smooth distribution
multiplication. Arbitrary norm-convergent inputs give the same distributional
limit. A finite right exponent gives convergence of right polynomial
multipliers; a finite left exponent gives the symmetric result. Every admissible
triple has at least one finite input exponent, which proves uniqueness of the
continuous extension at all endpoints without asserting finite-support norm
density in `l∞`. Shared Wiener representatives recover the prior product, its
smooth-multiplier compatibility, and ordinary real-line function-product integrals.

## Mixed three-sequence Young inequality: Appendix B.3

`PowerCoefficients` constructs the magnitude power `|a(n)|^t` in exponent `p/t`
with norm exactly `‖a‖^t` for positive finite real `p,t`. Original exponents may
be below one; no Banach-space instance is assumed for those inputs. Only the
powered exponents in each application of Young must be at least one.
`PowerYoung` proves absolute convergence of the powered convolution and constructs
its positive-root representative with norm at most the product of the input norms.

`MixedYoungRelation` records the source conditions `γ ≥ p₁ ≥ β > 0`,
`p₂,p₃ ≥ α > 0`, and `1/α + 1/β + 1/γ = 1/p₁ + 1/p₂ + 1/p₃` for finite
real exponents. These conditions construct a positive intermediate exponent
`q` with `1/q = 1/β + 1/γ - 1/p₁`, satisfying both powered Young relations.
The first application estimates the `α`-root convolution of `b,c`; the second
estimates the `β`-root convolution of `a` with that intermediate sequence.

`mixedYoung_le` states the source's full three-level sum explicitly, with powers
`α`, `β/α`, `γ/β`, and final root `1/γ`, bounded by `‖a‖‖b‖‖c‖`.
`mixedYoung_summable_and_le` additionally proves convergence of every inner sum,
every middle sum, and the outer sum. Unit modes attain one in the mixed norm,
so the constant is sharp. This establishes the displayed finite-positive-exponent
statement in Appendix B.3, including exponent values below one.

## Physical fractional translation energy: toward Appendix A.9

`CircleTranslation` is a linear isometry of actual normalized circle `L²`,
constructed from measure-preserving physical translation. Its representative
is `f(t+x)` almost everywhere and its Fourier coefficients are multiplied by
`exp(iπnt)`. Translations compose, have inverse displacement `-t`, and are
strongly continuous on every `L²` class. The continuity proof uses dominated
convergence of the Fourier coefficients and does not require smooth input.

Parseval gives the exact normalized squared increment energy as the sum of
`|exp(iπnt)-1|² |f̂(n)|²`. It also equals half the ordinary integral of
`|f(t+x)-f(x)|²` on `[0,2]`. Every such physical increment is square integrable.
For any measurable nonnegative displacement kernel and any displacement measure,
Tonelli exchanges the Fourier sum and the kernel integral, retaining infinite
values. A second formula identifies this energy with a genuine nonnegative
physical double integral, with the same normalization factor `1/2`.

The fractional specialization uses displacement `t∈[-1,1]` and kernel
`|t|^(-1-2s)`. Its regularity predicate is defined by finiteness of physical
increment energy. Exact Fourier diagonalization gives a spectral finiteness
criterion; it does not define the physical space through its coefficients.
Translations preserve this energy, positive and negative frequencies have the
same spectral weight, each single mode has its exact diagonal energy, and
constants have zero seminorm despite the kernel singularity.

This is a prerequisite for Appendix A.9, not its completion. The spectral
comparison is now proved below. The interval-to-periodic boundary estimate for
`0≤s<1/2` and the separate `H^(1/2)` conclusion remain to be connected to the
physical interval space.

## Fractional spectral comparison and homogeneous regularity

`FractionalKernel` proves two bounds for the real unit-frequency kernel
`|exp(iπx)-1|² |x|^(-1-2s)`: it is at most `π² |x|^(1-2s)` near zero and at
most `4 |x|^(-1-2s)` at infinity. The resulting powers prove global integrability
for `0<s<1`, including the singular but integrable range `s>1/2`. The kernel is
even and strictly positive on `(0,2)`, giving positive mass on `[0,1]`.

`FractionalKernelScaling` identifies the real kernel with the extended-nonnegative
physical kernel, including the zero-phase point. For every positive integer `n`,
an exact change of variables expresses its spectral weight as `n^(2s)` times
the model-kernel integral on `[-n,n]`. Integrability is established before any
conversion from nonnegative energy to an ordinary integral.

`FractionalSpectralBounds` uses the positive core mass as a lower constant and
the finite total model mass as an upper constant. The constants are actual
integrals and do not depend on frequency. The corresponding two-sided bounds
hold for every integer frequency, including the zero mode and negative indices.
All weights are finite, and precisely the nonzero modes have positive weight.
Summing the bounds compares physical fractional energy with
`Σ |n|^(2s)|f̂(n)|²`, retaining infinite values. For `0<s<1`, finite physical
fractional energy is equivalent to ordinary summability of this conventional
homogeneous Fourier square sum. Every Fourier mode consequently has finite
physical fractional energy.

## Periodic fractional Sobolev identification

`SobolevHomogeneous` identifies weighted Hilbert membership with homogeneous
moment summability on `ℓ²`. It proves the exact weighted square energy and
the comparisons `H ≤ W ≤ 2^(2s)(L+H)`, where `W` is the weighted norm squared,
`L` is the raw `ℓ²` norm squared, and `H` is the homogeneous square sum.
The inclusion into unweighted coefficients is a contractive linear map.

`FractionalSobolevIdentification` composes this inclusion with Hilbert Fourier
synthesis. For `0<s<1`, finite physical fractional energy is equivalent to
weighted square summability of the actual Fourier coefficients and to a unique
weighted synthesis representation. Both inverse identities hold in the genuine
periodic `L²` space. Writing `E` for the physical fractional energy and `c,C`
for the positive model-kernel constants, the bounds are
`E ≤ C W` and `c W ≤ 2^(2s)(c L+E)`. They are stated in extended nonnegative
reals, preserving the earlier physical definition without a totalized integral.
The `L²` term controls constant functions whose fractional seminorm vanishes.

This completes the periodic identification throughout `0<s<1`, including
`1/2`. The nonperiodic interval boundary estimate required by Appendix A.9
and its separate endpoint consequence remain open.

## Interval exterior kernel and sharp boundary threshold

`FractionalBoundaryKernel` evaluates both exterior tails for arbitrary interval
length `L>0` and `s>0`. Their sum at `0<x<L` is exactly
`[x^(-2s)+(L-x)^(-2s)]/(2s)`. Thus the one-direction exterior interaction
is `1/(2s)` times the endpoint-weighted square integral. Both sides are
nonnegative integrals and may be infinite. The exterior interaction is proved
to equal the mixed difference energy of the actual indicator zero extension.
The intrinsic interval Gagliardo energy is defined separately and is invariant
under almost-everywhere changes to interval data.

`FractionalBoundaryWeight` proves that this weight is integrable exactly when
`s<1/2`; its mass is `2 L^(1-2s)/(1-2s)`. For constant complex amplitude `z`,
the exterior interaction below one half is
`L^(1-2s)|z|²/[s(1-2s)]`. Constant amplitude one has infinite exterior
interaction at and above one half, despite zero intrinsic interval energy.
An almost-everywhere bound `|f|≤M` yields the same upper estimate with `M²`.
These are zero-extension statements; they do not assert a boundary obstruction
for periodically extended constant functions.

The general fractional Hardy inequality is now proved below. The remaining
extension/periodization comparison must connect it to the completed periodic
identification before claiming Appendix A.9.

## Fractional Hardy inequality for arbitrary interval data

`FractionalHardyKernel` computes the averaging coefficient
`c_s=(2^(2s)-1)/(2s)=∫₁² t^(2s-1)dt`. It is positive and strictly below one
when `0<s<1/2`. The explicit parameter `ε_s=(1-c_s)/(2c_s)` satisfies
`(1+ε_s)c_s=(1+c_s)/2<1`. The adjustable complex square inequality and the
annular integral are proved directly.

`FractionalHardyAveraging` represents the triangle `x<y<2x` by a jointly
measurable kernel. Exact Tonelli interchange recovers its weighted column
mass, including infinite nonnegative inputs. The row mass recovers the left
boundary weight, and the intrinsic difference kernel dominates the averaging
kernel. These statements give a uniform truncated operator bound.

`FractionalHardyPreestimate` integrates the actual squared function inequality.
Writing `J_δ` for left-boundary energy over `(δ,L)`, `E` for intrinsic interval
energy, and `a_s=(1+c_s)/2`, its result is
`J_(δ,L/2) ≤ a_s J_δ + (1+1/ε_s)E`.
Positive-distance truncation is finite for every interval `L²` function.
`FractionalHardyLeft` first proves this finiteness, then legitimately absorbs
the `a_s J_δ` term. The rest of the interval contributes only
`(L/2)^(-2s)N`, where `N=∫₀ᴸ |f|²`. Cutoffs `1/(n+1)` exhaust `(0,L)`;
nonnegative monotone convergence gives the coercive bound
`(1-a_s)J_0 ≤ (1+1/ε_s)E+(L/2)^(-2s)N`.

`FractionalHardy` proves that interval reflection preserves restricted measure,
the intrinsic energy, and the square energy. Adding the reflected estimate
controls the full endpoint-weighted square integral by twice the displayed
right side. Therefore finite intrinsic interval energy and `L²` imply finite
zero-extension exterior energy for `0<s<1/2`. No boundedness assumption is
used. The finiteness theorem applies to arbitrary interval representatives:
almost-everywhere replacement supplies a measurable representative and both
energies respect that replacement.

The fractional Hardy dependency and the forward zero-extension/periodization
comparison below are complete, as are the A.9 Fourier-Lebesgue membership
range and endpoint conclusions described after them.

## Zero extension and forward periodization

`FractionalZeroExtension` defines the actual indicator extension and full line
Gagliardo energy. Square integrability and square energy agree exactly with
the interval quantities. Partitioning the product measure and exchanging the
two mixed terms by Tonelli gives
`E_line(zeroExtension f)=E_interval(f)+2 E_exterior(f)`.
The identity retains infinite energies and holds for arbitrary interval `L²`
representatives by almost-everywhere replacement. With Hardy, zero extension
has finite line energy if and only if the original interval energy is finite
for `0<s<1/2` and every positive interval length.

`FractionalLineTranslation` changes the inner variable by actual translation
and then uses Tonelli to identify line difference energy with the nonnegative
double integral of physical translation increments. Both this identity and the
exact zero-extension decomposition apply to arbitrary `L²` representatives.

`PeriodizationIncrement` proves the periodic increment formula from three
adjacent zero-extension translates when `|t|≤1`. The exceptional endpoint
crossings form a null set. A three-term square estimate and translation
invariance bound its interval square integral by nine times the line increment
integral. No finite-energy assumption is needed for this comparison.

`FractionalPeriodization` reconciles the real-distance kernel with the circle
kernel, handling zero displacement explicitly. Circle normalization gives the
bound `E_periodic ≤ (9/2) E_line_translation(zeroExtension f)`; this constant is
not claimed sharp. Combining it with interval Fourier reconstruction proves
that arbitrary period-two interval `L²` data with finite intrinsic energy has
physical periodic regularity and actual `(1+|n|)^s` weighted Fourier square
summability for `0<s<1/2`. Matching endpoint values are not assumed. The
quantitative bound can be stated entirely in the original interval energies:
`E_periodic ≤ (9/2)(E_interval+2 E_exterior)`.

This proves the forward physical regularity passage needed for A.9 in the
period-two model. Its Fourier-Lebesgue membership conclusions are assembled below.

## Appendix A.9 exponent and endpoint conclusions

`HilbertSobolevEmbedding` constructs the injective continuous identity map
from weighted Hilbert coefficients of regularity `s≥0` to finite real Banach
targets `q≥1` satisfying `1/q<s+1/2`. For `q≥2` this is the contractive
exponent inclusion after removal of the weight. Below two, the explicit
auxiliary exponent `r=(1/q-1/2)⁻¹` satisfies the exact extended-real Hölder
relation and `sr>1`. Both branches preserve every raw coefficient.

`FractionalIntervalEmbedding` proves
`E_t(f) ≤ L^(2(s-t)) E_s(f)` for `0≤t≤s` and positive interval length `L`.
The proof includes the diagonal of the kernel and permits infinite energies;
no measurability hypothesis on the representative is needed for the comparison.
In particular, finite intrinsic half-regularity energy gives all smaller
positive regularities.

`IntervalFourierLebesgue` composes the actual interval Fourier reconstruction
with the coefficient inclusion. For `0<s<1/2`, `L²` and finite intrinsic energy
give `periodTwoCoefficient f ∈ ℓ^q` whenever `q>1/(s+1/2)`. The zero case
requires only `L²`, permits equality `q=2`, and also gives bounded coefficients.
The unified nonnegative-regularity theorem makes its difference-energy
hypothesis conditional on `s>0`, so it imposes no extra energy assumption at
zero. At half regularity, a positive `t<1/2` with `1/q<t+1/2` exists for every
finite `q>1`; lowering intrinsic regularity before periodization proves the
separate conclusion without assuming matching endpoints or finite critical
zero-extension energy.

These are the actual coefficient membership conclusions for the period-two
model, with a continuous linear embedding between the coefficient spaces.
The combined bounds in the original intrinsic interval size are proved below.
The arbitrary-period coefficient and energy scaling are now proved below.

## Appendix A.9 quantitative intrinsic bounds

`IntrinsicIntervalEnergy` retains `I_s(f)=N(f)+E_s(f)`, where `N` is the
unnormalized physical square integral. For positive regularity its finite
square root is the intrinsic Gagliardo size. Almost-everywhere invariance and
finiteness are proved before converting the nonnegative energy to real values
in the norm estimates. At zero regularity, the final theorem uses `N` alone.
Lowering regularity on an interval of length `L` gives
`I_t ≤ (1+L^(2(s-t))) I_s` and the corresponding square-root bound.

`FractionalHardyBound` explicitly inverts the positive Hardy gap
`g_s=1-(1+c_s)/2`. Its finite constant is
`C_ext=(1/(2s)) g_s^(-1) 2 (1+1/ε_s+(L/2)^(-2s))`.
The resulting bound `E_ext ≤ C_ext I_s` holds for arbitrary interval `L²`
representatives, even if the fractional energy is infinite. The constant is
not claimed optimal. Almost-everywhere replacement removes the global
measurability assumption from the quantitative result.

`IntervalSobolevBound` proves the nonnegative Parseval identity with its exact
factor `1/2`, then combines periodization and the lower spectral bound:
`C_per=(9/2)(1+2 C_ext)` and
`C_Sob=c_low^(-1) 2^(2s)(c_low/2+C_per)`.
Both constants are proved finite below half. The actual weighted Fourier
sequence satisfies `‖a‖² ≤ C_Sob I_s(f)` and the corresponding square-root
bound. Synthesis returns the original interval Fourier `L²` reconstruction.

`IntervalFourierLebesgueBound` composes this with the continuous coefficient
inclusion. The finite constant is its operator norm times `sqrt(C_Sob)`,
independent of the interval function. Thus the actual `ℓ^q` norm is bounded
by that constant times the original intrinsic size throughout the positive
subcritical A.9 range. For half regularity the explicit choice
`t(q)=(max(0,1/q-1/2)+1/2)/2` lies strictly between zero and half and satisfies
the needed reciprocal inequality. The quantitative lowering estimate gives
a uniform bound in `I_(1/2)`, without periodizing at the critical index.
At zero regularity, every extended target `q≥2`, including infinity, satisfies
`‖a‖_q ≤ sqrt(1/2) sqrt(N(f))`; an imaginary constant attains equality.

These are uniform inequalities in the actual intrinsic interval size. The
normed quotient API is described below. The period-two results are extended
to arbitrary positive periods by the scaling identification below.

## Appendix A.9 on arbitrary positive periods

`IntervalDilation` transports the restricted Lebesgue measure under `x ↦ cx`
for `c>0`, retaining the exact inverse Jacobian. The resulting nonnegative
integral identity works without measurability of the integrand, and `MemLp`
transports on both open and half-open intervals. Physical square energy scales
by `c⁻¹`.

`FractionalDilation` proves exact distance-kernel homogeneity, including its
diagonal for every real regularity. Changing both variables gives
`E_s,[0,A](f(c·))=c^(2s-1) E_s,[0,cA](f)`.
The identity allows infinite energies. The full inhomogeneous energy has two
distinct factors, `c⁻¹` for the square integral and `c^(2s-1)` for differences.
Their sum gives a finite uniform factor and a real intrinsic size bound when
the original data has finite energy. Half-regularity energy is dilation invariant.

`IntervalCoefficientScaling` defines the actual normalized integral on `[0,L]`
with frequency `2πn/L`, proves equality with mathlib's `fourierCoeffOn`, and
identifies it exactly with the period-two coefficient of `f((L/2)·)`. This is
an identity of the physical Fourier integrals.

`ArbitraryPeriodFourierLebesgue` transfers the weighted square summability and
A.9's full exponent conclusions to every `L>0`. For `0<s<1/2`, actual coefficients
belong to `ℓ^q` whenever `q>1/(s+1/2)`. The zero branch uses only interval `L²`
and permits every extended `q≥2`. Intrinsic half regularity gives every finite
`q>1`. Uniform positive and half-regularity bounds use the original length-`L`
intrinsic size and the explicit dilation factor, with constants independent of
the function. The zero-regularity normalization is exactly
`‖a‖_q ≤ sqrt(1/L) sqrt(N_L(f))`, including the infinity target.

This completes the arbitrary-period coefficient and quantitative embedding
statements in the intrinsic interval formulation. The reverse Sobolev comparison
and resulting regularity identification are proved below. A separate normed
intrinsic function-space API and the main nonlinear Fourier/Birkhoff results
remain separate work.

## Reverse restriction and Sobolev identification

`FractionalRestriction` first enlarges the inner spatial integral to the real
line, changes to displacement variables, and applies Tonelli. This gives
`E_interval ≤ 2 E_full_translation` with the exact circle normalization.
The real-distance kernel is measurable and agrees with the singular extended
kernel in the central energy: at zero displacement the actual increment
vanishes. Translating the already evaluated exterior kernel gives tail mass
`∫_(|t|>1) |t|^(-1-2s) dt = 1/s` for every `s>0`.
The `L²` increment bound then yields
`E_interval ≤ 2(E_periodic+(4/s)‖f‖²)`.
No energy finiteness is assumed for this comparison. Periodic fractional
regularity therefore implies finite intrinsic interval energy for every
positive index, including indices above half.

`IntervalSobolevIdentification` combines the reverse estimate with the
subcritical periodization theorem. For `0<s<1/2`, physical periodic regularity
is equivalent to finite intrinsic energy on a period. Almost-everywhere
Fourier reconstruction gives the exact weighted square-summability criterion
for arbitrary interval representatives. Positive dilation preserves fractional
energy finiteness in both directions, so the criterion holds on every interval
`[0,L]` with `L>0`. Finite intrinsic energy is also equivalent to a unique
weighted sequence whose raw entries are the actual normalized Fourier integrals.

`IntervalSobolevNormEquivalence` retains the square term and the tail in the
finite reverse constant
`R_s=2+2(C_upper(s)+4/s)`.
For `0<s<1`, the periodic synthesis of weighted coefficients `a` satisfies
`I_s ≤ R_s ‖a‖²` and `size_s ≤ sqrt(R_s) ‖a‖`.
Below half, reconstruction transfers the reverse bound to arbitrary original
period-two interval data. Together with the forward periodization bound this
proves explicit inequalities in both directions between intrinsic interval
size and the actual weighted Fourier norm. The result preserves constant
functions and does not require endpoint matching.

`FractionalDifferenceQuotient` identifies the physical energy with the square
norm of `(f(x)-f(y))/|x-y|^(1/2+s)` on the interval product. This holds on the
diagonal as well. The quotient is measurable for measurable representatives,
linear, and invariant under almost-everywhere changes of interval data.

`PhysicalIntervalL2` represents an interval `L²` class in normalized coordinates
and proves exact square-energy factor `L`, actual Fourier coefficient agreement,
and both reconstruction identities. Arbitrary square-integrable input is
accepted, without global measurability or an endpoint condition. Equality of
classes is precisely almost-everywhere equality on the physical interval.

`IntrinsicIntervalSobolev` is the finite-energy submodule of these actual `L²`
classes. The graph into two `L²` spaces, with first component multiplied by
`sqrt(L)`, induces a normed complex vector space. Its squared norm is exactly
`N+E_s`, and its norm equals the previous intrinsic size. Both the underlying
`L²` map and the physical difference-quotient operator are continuous. The
former has norm bound `1/sqrt(L)` and the latter bound one. Construction from
arbitrary original interval data preserves its intrinsic size and reconstructs
it almost everywhere. Equality of constructed elements is exactly equality
almost everywhere of the input data.

`IntrinsicFourierEmbedding` packages the actual A.9 maps as continuous
complex-linear injections from this normed space. The finite targets are
`q>1/(s+1/2)` for `0<s<1/2` and every `q>1` at `s=1/2`. The existing uniform
bounds now use the actual norm; coefficient extraction is exactly the original
normalized interval integral, including for unequal endpoint values.

At zero, ordinary `L²` remains the source of the earlier A.9 API; the graph
norm at zero includes the extra difference term.

`IntrinsicGraphClosed` transfers arbitrary almost-everywhere properties from
the normalized circle to physical interval coordinates. Two successive
almost-everywhere convergent subsequences of `L²` limits identify the graph
limit with the actual fractional difference quotient of the limiting input.
Product-measure projections transfer convergence at both physical arguments.
This proof covers every real graph index, including half regularity, and
requires no endpoint condition or periodization at the critical index.

`IntrinsicSobolevComplete` proves that the isometric graph image is closed in
the product of complete `L²` spaces. Thus the intrinsic normed quotient is now
complete on every positive interval. The induced complex inner product is
exactly `L * inner(f,g) + inner(Q_s f,Q_s g)` in normalized circle coordinates.
This makes the intrinsic quotient a complex Hilbert space with its existing
physical norm. Intrinsic convergence is equivalent to simultaneous `L²`
convergence of its two graph components; every intrinsic Cauchy sequence has
a limit in the same space.

`IntrinsicSobolevSynthesis` gives an injective continuous map from weighted
Hilbert coefficients to actual intrinsic interval classes for every `0<s<1`.
Its actual Fourier coefficients are exactly the original entries. The inverse
coordinate dilation preserves fractional energy finiteness, and the intrinsic
norm bound accounts for both the square and difference energies.

`IntrinsicSobolevEquivalence` proves that below half regularity this synthesis
is inverse to actual Fourier analysis, giving a continuous complex-linear
equivalence with the normalized-frequency weight `(1+|n|)^s`. The forward
constant is `sqrt(C_Sob(s)) sqrt(D_s(L/2))`; the inverse constant is
`sqrt(D_s(2/L)) sqrt(R_s)`, where `D_s(c)=c⁻¹+c^(2s-1)` and the period-two
constants were proved earlier. Both estimates use the existing exact intrinsic
norm. Passing arbitrary interval representatives to their quotient preserves
every original Fourier integral. The earlier A.9 map equals the composition
of this equivalence with the weighted Hilbert coefficient inclusion.

`IntrinsicSobolevApproximation` transports finite coefficient truncations back
to the intrinsic space. These retain exactly the selected physical Fourier
coefficients and satisfy a uniform bound independent of the finite set. They
converge in the full intrinsic norm as the finite sets exhaust the integers,
so classes with finite Fourier support are dense below half regularity.
No matching-endpoint assumption is needed. Surjectivity and this Fourier
truncation convergence are not asserted at or above half regularity.

## Section 6 weight class and shifted weighted norms

`SpectralWeight` implements the displayed class `M`: `w(n)≥1`, symmetry,
submultiplicativity, and monotonicity on nonnegative integer frequencies.
Monotonicity is also proved for arbitrary signed magnitudes. The displayed
normalization permits `w(0)>1`, so constant weights greater than one are
included. Scaled Sobolev weights `(1+c|n|)^s`, `c,s≥0`, include the exact
source convention `(1+|nπ|)^s`. All source weights have tempered inverses.

`ShiftedWeight` proves the two translation comparisons with factor `w(i)`.
The identity on raw coefficients gives a continuous linear equivalence between
the original and translated-weight spaces. Reindexing gives an isometric
identification of the latter with the original weight; its output coefficients
are exactly `a(n-i)`. Thus the shifted norm equals the norm after Fourier
modulation. The finite-`p` scalar energy is exactly
`Σ_n w(n+i)^p |a(n)|^p`; the scalar construction and norm comparisons also
hold at infinity. Changing the shift by `j` costs at most `w(j)`, independently
of the original shift. There is also a contractive unweighted inclusion.

`ShiftedPairNorm` uses the existing source sum norm for finite Banach exponents.
The first physical component is modulated by `-i` and the second by `i`.
Frequency reflection in the first component gives the exact source energy
`Σ_n w(n+i)^p (|f_minus(-n)|^p+|f_plus(n)|^p)`.
Both comparisons with the unshifted pair norm have factor `w(i)`, without an
extra factor from passing through a maximum norm. Pair shifts satisfy the
additive law and zero shift is the identity. These pair formulas are stated
for finite `p`; the source's separate infinity pair norm is not substituted.

`SpectralWeightModulation` identifies the weighted realization with the
unweighted tempered distribution obtained through the contractive inclusion.
It then proves that weighted coefficient modulation is exactly Mathlib's
physical multiplication by `exp(iπix)`.
The complementary free inverse is now implemented as follows.

## Section 6 resonant splitting and complementary inverse

`WeightedResonance` selects exactly the first physical frequency `-n` and the
second frequency `n`. Its two continuous projections sum to the identity,
are idempotent, and annihilate each other. A vector is fixed by the complement
exactly when its two resonant coefficients vanish. Both projections contract
the source's finite-exponent pair norm for any positive weight.

`ComplementaryStrip` uses the entire closed strip `|Re λ-nπ|≤π/2`, without
removing a disk. For every `m≠n`, `|λ-mπ|≥|m-n|≥1`. The reciprocal symbol is
explicitly zero at `m=n`, so its construction also applies at `λ=nπ`.
Its base bound is one and its one-derivative bound is `1+(1+|λ|)/π`.

`WeightedFreePencil` uses the domain weight `w(k)(1+|k|)` and physical symbols
`λ+πk` and `λ-πk`. Domain inclusion is injective and preserves coefficients.
For every source spectral weight, forgetting the weight identifies the pencil
exactly with `λ*domainInclusion-freeOperator` on the existing differential
domain. Thus this construction uses the previously identified free derivative.

`ComplementaryFreeInverse` provides continuous linear base and domain-valued
inverses, with the same coefficients. Composing the domain inverse with the
pencil in either order gives precisely the complementary projection, in the
appropriate space. Its image is complementary and it is the unique
complementary solution of the projected free equation. The base norm is at
most one; the domain norm has the explicit bound above.

`ComplementaryShiftedNorm` proves that coefficient norm domination survives
every signed shift. Both projections and the base inverse are contractions
in every such norm, independently of the shift, weight, strip index, and
spectral parameter within the strip. Pair norm estimates concern finite Banach
exponents; the algebraic identities and scalar bounds also cover infinity.
The potential-composed operator and Lemma 6.4 are now implemented below.

## Section 6, Lemma 6.4: uniform weighted potential estimate

`SpectralConvolution` constructs weighted convolution as an absolutely
convergent series in the weighted Banach space. Submultiplicativity controls
each translated summand, giving the exact Young bound
`‖a*b‖_{w,p}≤‖a‖_{w,p}‖b‖_{w,1}`, including `p=∞`. Forgetting the weight gives
the existing convolution of the raw coefficients. The map is continuous and
complex bilinear. Product modulation can be assigned to the second factor,
so the corresponding scalar shifted bound has no extra weight factor.

`PuncturedLattice` bundles the sequence `k⁻¹` off the origin and zero at the
origin. It belongs to every `ℓᑫ` with `q>1`, including infinity. The bilateral
integral estimate gives its `ℓ²` norm at most two. For finite Banach `p`, the
chosen constant is `c_p=max(‖puncturedLattice‖_{p′},2)`; it depends only on `p`
and is proved to equal two when `p=2`.

`ComplementaryL1` bounds the actual reciprocal by a translated, signed copy
of that lattice. Weighted Hölder multiplication then maps the complementary
inverse from `ℓᵖ_w` into `ℓ¹_w` with constant `c_p`. The arbitrary positive
weight cancels exactly. Translated weights give the same estimate in every
scalar shifted norm, independently of the shift, strip center, and parameter.
The argument includes `p=1`, where the conjugate exponent is infinity.

`WeightedPotentialInverse` constructs `T_n=Φ A_λ⁻¹ Q_n` as a continuous linear
operator on the source's weighted finite-`p` pair space. The two off-diagonal
products exchange physical components. Combining their estimates in the exact
pair norm proves `‖T_n f‖_{w,p;i}≤c_p‖φ‖_{w,p}‖f‖_{w,p;-i}`. At `p=2`, the
constant is exactly two. Forgetting the weight identifies this map with the
original potential operator applied to the previously constructed domain-valued
complementary inverse. There is also a bound for its ordinary operator norm.

Two applications restore the initial shift and have bound `(c_p‖φ‖)²`.
The stronger Lemma 6.5 estimate is now proved below.

## Section 6, Lemma 6.5: refined weighted square estimate

`WeightedFourierTail` defines the scalar and pair remainder with the exact
source cutoff `|k|≥N`, including equality. It is a continuous projection,
contracts the relevant norms, and tends to zero in norm for finite exponents.
Weighting commutes with this cutoff. Symmetry makes it compatible with both
physical signs.

`WeightedHolderMultiplier` and `WeightedSandwich` construct the actual weighted
`ℓᵖ→ℓ¹` double-inverse product for arbitrary conjugate-space symbols. Their
bounds hold in every scalar shifted norm. Splitting the two symbols gives
far-output, far-input, and near-near terms; separated near windows replace
the potential exactly by its high-frequency remainder.

`ResonantWindowGeometry` uses the closed radius-`|n|/2` integer windows around
`n` and `-n`. Opposite near frequencies satisfy `|j-k|≥|n|`, including the
boundary, and the sharper weight comparison
`w(j-n)w(n)≤w(j-k)w(k-n)`. Positive coefficient majorants preserve all input
sequence norms. `WeightedSandwichGain` transfers this pointwise comparison
to the full shifted output norm using the existing Hölder–Young sandwich.
Thus the near-near contribution is bounded by the potential tail divided
by `w(n)`, rather than merely by the tail alone.

`ComplementaryReciprocalTail` proves a normalized inverse-bracket envelope
for the zeroed reciprocal and the uniform bound
`16p |n|^(-1/p)` outside either physical near window, for `n≠0`. This includes
`p=1` with conjugate exponent infinity and every parameter of the unpunctured
closed strip. Combining this with the full reciprocal bound `c_p` gives the
scalar two-term estimate. The inhomogeneous bracket handles the zero strip.
The explicit double-inverse constant is `C_p=64p c_p+c_p²`; for `p=2` it is 260.
No optimality of this Lemma 6.5 constant is asserted.

`WeightedSquareEstimate` identifies both components of the actual `T_n²` with
the appropriate outer potential times the opposite scalar double inverse.
It proves, for every finite Banach exponent and every `λ∈U_n`,
`‖T_n² f‖_{w,p;n}≤C_p‖φ‖(‖φ‖/(1+|n|)^(1/p)+‖R_n φ‖/w(n))‖f‖_{w,p;n}`.
Conjugating the square by the source shift gives the same displayed bound
for its induced operator norm. All factors use the source's exact finite-`p`
pair norm, and the weighted remainder retains its boundary.

### Locally uniform contraction after Lemma 6.5

`UnweightedComplementary` forgets a spectral weight without changing Fourier
coefficients. This inclusion contracts the exact finite-exponent pair norm,
commutes with Fourier tails and the actual `T_n`, and preserves the physical
component signs. Unit-weight signed shifts preserve the source pair norm.
Thus Lemma 6.5 also gives an ordinary unshifted operator bound on the full
unweighted space, with the same potential after inclusion.

`WeightedContraction` proves that weighted tail norms decrease with the
cutoff. A common upper bound controls both the weighted shifted square and
the unweighted square: the weighted full norm dominates the unweighted one,
and likewise for every Fourier remainder. Given any potential and any
positive tolerance `ε`, it constructs `N≥1` and an open convex neighborhood
containing both that potential and zero. Every potential in the neighborhood
has norm less than the original norm plus one. Both operator norms are at
most `ε` for all `|n|≥N` and every point of the full closed strip `U_n`.

The special case `ε=1/2` is exactly the simultaneous contraction assertion
on printed page 39. It holds for every finite Banach exponent, including
`p=1`, without removing the central lattice point or the strip boundary.
### Squared Neumann inverse and the Q-equation

`ConjugatedSquaredNeumann` transports the geometric series through a continuous
linear equivalence. The even series converges in the original operator algebra
and inverts `Id-K²` on both sides. Its product with `Id+K` inverts `Id-K` on
both sides and commutes with `K`. Smallness is tested on the conjugated square.
`WeightedCorrection` applies this construction using the signed pair modulation.
It proves the displayed factorization for `T̂_n`, both inverse identities,
uniqueness, and commutation with `T_n`. Forgetting the weight carries this
inverse to the unit-weight inverse on every common input.

`WeightedDomainPotential` embeds the weighted one-derivative scalar domain
into weighted `ℓ¹` with the same exponent-only constant as the ordinary
Sobolev embedding. Composing with weighted convolution gives the actual
continuous domain-to-base potential. Its physical coefficients agree with the
original operator, and applying it after the complementary domain inverse
gives exactly the previously estimated `T_n`.

`WeightedQEquation` constructs the continuous domain-valued map
`u ↦ v=A_λ⁻¹ Q_n T̂_n Φu`. Its values have zero resonant coordinates and
satisfy `A_λ v=Q_n Φ(u+v)`. The source formula `Φv=T̂_n T_n Φu` and the
identity `Φ(u+v)=T̂_n Φu` are proved. The solution is unique among actual
complementary weighted derivative-domain vectors. A single open convex
neighborhood and frequency cutoff give existence and uniqueness for every
input `u` on every sufficiently distant full closed strip. These results
include `p=1` and require no eigenvalue or determinant assumptions.

### Lemma 6.6: the resonant determinant criterion

`ResonantCoordinates` extracts the physical first-component frequency `-n`
and second-component frequency `n`. Synthesis recovers the actual resonant
projection and has a coefficient-preserving derivative-domain lift. Its two
amplitudes remain independent at `n=0`. The free pencil acts on this space
by the scalar `λ-nπ`, and the complementary projection commutes with the
pencil between the domain and base.

`WeightedResonantReduction` defines the source map
`S_n=(λ-nπ)Id - coordinates ∘ T̂_n Φ ∘ synthesis` and its `2×2` matrix.
Each entry is the free diagonal minus the corresponding corrected potential
coefficient. Reconstruction adds the unique Q-solution to the synthesized
resonant vector. Its resonant coordinates are exactly the prescribed input,
and its full differential residual equals the synthesis of `S_n c`.
Every actual domain eigenvector is reconstructed from its coordinates.
Consequently, the existence of a nonzero weighted domain eigenvector is
equivalent to a nonzero matrix-kernel vector and to `det S_n=0`.

`UnitWeightedRealization` gives continuous coefficient-preserving equivalences
between the unit-weight and original base and derivative-domain spaces.
It identifies the full eigenvector equations and preserves nonzero vectors
in both directions. `PeriodicResonantReduction` therefore proves Lemma 6.6
for the existing original periodic spectrum, for every finite Banach exponent.
A single open convex neighborhood and cutoff `N≥1` make the criterion valid
on all full closed strips with `|n|≥N`.

### Lemma 6.7(i) and the reality hypothesis in 6.7(ii)

`ReflectedTestSymmetry` proves the transposition identity for absolutely
convergent convolution tests. `BilinearGreen` pairs base coefficients with
opposite reflected derivative-domain components, without conjugation.
The actual free pencil and arbitrary complex off-diagonal potential are
symmetric for this pairing. The proof works at every finite Banach exponent,
including `p=1`, using the derivative-domain embedding into `ℓ¹`.

`ResonantDiagonalSymmetry` applies Green's identity to the reconstructed
vectors and uses their exact residuals. The resulting cross-coordinate
identity forces equality of the two diagonal entries, and hence of the
correction diagonals `a_n⁺=a_n⁻`. It defines the common coefficient `a_n`
and both `b_n` coefficients and proves the common-diagonal matrix form.
This establishes Lemma 6.7(i), on source pages 40–41.

The reality assertion for `a_n` in the printed Lemma 6.7(ii) lacks the
hypothesis used in its proof. The proof starts by assuming `φ*=±φ` and uses
it for both the diagonal and off-diagonal conjugation identities.
`ConstantResonantCoefficient` computes the actual correction for constant
components `(a,b)` through the uniqueness of the already constructed inverse:
`a_n(λ)=ab/(λ+nπ)` for `n≠0`. At the central parameter this is `ab/(2πn)`.

`ResonantRealityCounterexample` takes `(a,b)=(1,i)` and proves that the
imaginary part is strictly positive at every positive central resonance
where the inverse is defined. For every cutoff, it constructs a positive
index beyond that cutoff satisfying the actual shifted square bound `≤1/2`
and having a nonreal diagonal. Thus a large-frequency restriction cannot
repair the unconditional assertion for general complex potentials. The
conditional conjugation identities under `φ*=±φ` are now proved below.
The printed unconditional assertion remains false for general complex potentials.

### Lemma 6.7(ii): conditional conjugation identities

`ConjugateReflection` constructs physical conjugation on every symmetric
weighted coefficient space: the coefficient at `k` becomes the complex
conjugate of the original coefficient at `-k`. It preserves the scalar norm,
including the infinity endpoint, and is involutive. Conjugation reverses
both factors in the actual convolution sum.

`WeightedReality` defines the source potential star by exchanging the two
conjugate-reflected components. Its equality to `εφ` is characterized by
both raw coefficient identities. For `ε²=1`, the signed map on vectors is
`J_ε(f)=(conj(f₂(-k)), ε conj(f₁(-k)))`. Symmetry of the derivative weight
makes it available on the actual domain as well as the base.

`ConjugateComplementary` proves that the full closed strip is invariant
under conjugation, and that the zeroed reciprocal symbol conjugates at the
same integer index. Under `φ*=εφ`, signed conjugation commutes with the
actual domain potential and intertwines the complementary domain inverse,
and hence `T_n(λ)`, with the operators at `conj λ`.

`ConjugateCorrection` uses uniqueness of `(Id-T_n)⁻¹` to obtain the identity
for the already constructed correction. Extraction and synthesis agree with
the signed action on the two resonant coordinates. `ResonantConjugation`
then proves `a_n(conj λ)=conj(a_n(λ))` and
`b_n⁺(conj λ)=ε conj(b_n⁻(λ))`, together with the reverse off-diagonal
identity. The reality hypothesis applies to every conclusion. The common
diagonal has zero imaginary part on the real axis for either reality type.

These identities hold at every finite Banach exponent with the two inverse
hypotheses. The final uniform theorem supplies both hypotheses on every
sufficiently distant full closed strip, using one open convex neighborhood
and one cutoff. Thus the corrected Lemma 6.7(ii), with the hypothesis from
its source proof on pages 40–41, is established for both signs.

### Equations (1.14)–(1.15): parity and the source basis order

The implementation's resonant coordinates use the physical order
`(e_n⁻,e_n⁺)`, whereas the displayed matrix on source page 40 uses
`(e_n⁺,e_n⁻)`. The `weightedResonantBPlus` and `weightedResonantBMinus`
names now follow the source definitions: they are respectively the lower
and upper correction entries in physical order. This corrects the earlier
label assignment. The conjugation theorems have been updated accordingly.
`SourceResonantMatrix` explicitly reverses both indices, proves the exact
printed matrix form, and proves equality of its determinant with the
physical-order determinant and the resulting eigenvalue criterion.

`ResonantPotentialModes` applies the actual potential to the two resonant
derivative-domain basis vectors. Column zero has only a second component,
with coefficient `φ_+(k+n)`; column one has only a first component, with
coefficient `φ_-(k-n)`. Consequently the source leading term `φ^+_{2n}` is
the raw second coefficient at `2n`, while `φ^-_{2n}` is the raw first
coefficient at `-2n`. The signs follow equation (1.2) on source page 22.

`SquaredNeumannInvariant` proves that continuous testing commutes with the
sum of a convergent even operator series, and that any kernel preserved by
its square is preserved by the sum. `WeightedComponentParity` proves that
`T_n` exchanges the physical components and its even powers preserve them.
The convergent even Neumann inverse therefore preserves each component
subspace as well. This is component parity, not parity of Fourier indices.

Writing `u_i=(Id-T_n²)⁻¹ Φe_i` in physical order, `ResonantParityExpansion`
proves (1.14) as `a_n=coordinates(T_n u_1)_1`. The off-diagonal coefficients
are `b_n⁺=coordinates(u_0)_1` and `b_n⁻=coordinates(u_1)_0`. Subtracting the
actual leading Fourier coefficients gives precisely `coordinates(T_n²u_i)`
in the same output component, proving both parts of (1.15).

`ResonantCoefficientSeries` proves the individual parity cancellations and
the actual scalar `HasSum` statements: `a_n` is the sum of the odd terms
`T_n(T_n²)^j Φe_n⁺`; each off-diagonal Fourier remainder is the sum of the
strictly positive even terms `T_n²(T_n²)^j Φe_n∓`. All results hold for
arbitrary complex potentials and every finite Banach exponent under the
existing shifted-square hypothesis. The even-vector bounds and analytic
dependence and both summability estimates are proved below, with the
source-display qualification recorded for Lemma 6.8(ii).

### Lemma 6.8: uniform even-vector bounds and approximation

`ConjugatedNeumannBounds` measures the even inverse in the exact norm obtained
by the chosen continuous change of coordinates. If the conjugated square has
norm `q<1`, the inverse bound is `(1-q)⁻¹`. The remainder after the first `m`
even terms is exactly `(T²)^m (Id-T²)⁻¹`, with bound `q^m/(1-q)`.
These results also cover trivial Banach spaces. At `q≤1/2`, the inverse
bound is two and the approximation error is at most `2·2⁻ᵐ` times the input norm.

`ResonantSourceNorm` proves that the signed modulation removes each resonant
wave exactly. The source at physical index zero has shifted norm `‖φ.snd‖`,
and the source at index one has shifted norm `‖φ.fst‖`. No normalization
`w(0)=1` or comparison with the maximum pair norm is needed.
`WeightedEvenApproximation` transfers the inverse and remainder bounds to
the actual complementary operator in this shifted norm.

`ResonantEvenBounds` therefore bounds each actual even vector by twice its
opposite potential component norm. Forgetting the weight commutes with signed
modulation; the unweighted finite-exponent pair norm is bounded by every
shifted spectral-weight norm with constant one. The same factor-two bounds
thus hold in the source's unweighted norm.

One open convex neighborhood containing the potential and zero, and one
cutoff `N≥1`, give these bounds throughout every full closed strip with
`|n|≥N`. Both vector errors are bounded by `2·2⁻ᵐ (‖φ‖+1)` on that entire
parameter set. An epsilon-form theorem proves that one truncation length
works for both vectors, every potential in this neighborhood, and all those
strips. Analytic dependence and the proof-consistent off-diagonal
summability estimate are proved below.

### Lemma 6.8: analytic dependence of the actual resonant coefficients

`ComplementaryResolventIdentity` proves the scalar, base-space, and
derivative-domain resolvent identities for two parameters in a closed strip.
They include the removed resonant frequency, which is exactly zero.
`ComplementaryAnalytic` normalizes at `c=nπ` by the entire bounded pencil
`A(z)=Id+(z-c)R_c`. On the full closed strip its two-sided inverse is
`Id-(z-c)R_z`. The domain-valued total extension `R_c^domain A(z)⁻¹`
is proved equal to the actual complementary inverse throughout that strip.
Banach-algebra inversion proves operator-norm analyticity on a neighborhood
of every strip point, including the central lattice point and both edges.
This free-inverse construction also covers the infinity endpoint in the
existing `WithLp ∞` maximum pair norm.

`WeightedPotentialAnalytic` bundles the actual derivative-domain potential
as a continuous complex-linear operator-valued map of the potential. Its
bilinear bound retains the exponent-only Sobolev embedding constant in the
exact finite-exponent pair norm. Composition with the complementary extension
gives a jointly analytic extension of `T_n=Φ A_λ⁻¹Q_n`, with exact agreement
on the closed strip.

`WeightedCorrectionAnalytic` defines total even and full corrections by
Banach-algebra inversion and the squared factorization. Their joint domain
requires the free normalization and the even denominator to be invertible;
this domain is proved open. The shifted small-square hypothesis implies both
requirements. Two-sided inverse uniqueness proves that these extensions are
the actual existing Neumann inverses at every such parameter.

`ResonantAnalytic` applies continuous resonant extraction to the actual
corrected potential-source vectors. Every correction matrix entry and all
three source coefficients `a_n`, `b_n⁺`, and `b_n⁻` are jointly analytic on
this open domain. The source basis labels are preserved. One open convex
potential neighborhood containing the given potential and zero, and one
cutoff `N≥1`, give joint analyticity over its product with each closed strip
`|n|≥N`. The same theorem explicitly supplies the smallness witness and
agreement with all three original source coefficients on that entire set.
Restricting the joint result to a fixed potential gives the analytic assertion
of Lemma 6.8. The argument works for every finite Banach exponent, including
`p=1`; both summability estimates for `p>1` are proved below, with the
source-display qualification for (ii).

### Lemma 6.8(i): diagonal row and full-strip supremum estimates

`UnweightedEvenCorrection` proves uniqueness for the even equation and
compatibility of its inverse with forgetting the spectral weight. The same
holds for each potential-source vector and actual resonant even vector.
Unit-weight signed modulation preserves the square's operator norm, so the
existing simultaneous contraction theorem supplies both inverse hypotheses.
Consequently the positive-mode even vector has unweighted norm at most
`2‖φ_-‖_p`, retaining the unweighted component norm instead of replacing it
by its larger weighted norm. Ordinary coefficient realization has exactly
the same norm as forgetting to unit weight.

`ComplementaryRowEstimate` constructs the actual physical-frequency row
`a(n-k) complementarySymbol(n,z,-k)` in a reciprocal exponent `q>1`,
and a parameter-independent punctured-lattice envelope. Pointwise domination
throughout the closed strip gives domination of its `ℓ^q` norm. The actual
row is absolutely summable against an `ℓ^p` input when `p,q` are conjugate,
and Hölder bounds its sum by the input norm times the envelope norm. The
`p=1,q=∞` endpoint is included. For finite `q`, reflection identifies that
norm with the exact source expression
`(Σ_m (‖a(n+m)‖ / |m-n|)^q)^(1/q)`; the resonant term is zero.

`ResonantDiagonalEstimate` proves the actual diagonal's Fourier expansion,
its absolute convergence, and the pointwise bound
`‖a_n(z)‖ ≤ 2‖φ_-‖_p (Σ_m (‖φ_+(n+m)‖ / |m-n|)^{p'})^{1/p'}`.
The conjugate norm formulation also covers `p=1`. One potential neighborhood
and cutoff make this bound valid on every distant full closed strip for both
the original proof-dependent coefficient and its analytic extension.

`ResonantDiagonalSup` defines the source quantity `|a_n|_{U_n}` as the
supremum of the actual coefficient norm over the entire unbounded closed
strip. The uniform pointwise estimate proves that image bounded, that the
supremum dominates every actual coefficient value, and that it is nonnegative
and bounded by the same reciprocal expression. All these conclusions share
one open convex potential neighborhood and one cutoff. The diagonal sum and
quantitative tail decay, and the proof-consistent off-diagonal estimates
in (ii), are proved below.

### Lemma 6.8(i): quantitative diagonal summability

`ConvolutionRows` applies powered Young to construct an actual `ℓ^p` sequence
of inner row norms. Contractive exponent inclusion permits the common inner
exponent `r=min(p,p')`, and extraction at `2n` does not increase the outer norm.
`ConvolutionRowTails` proves the exact support split: when `|n|≥N`, either the
kernel index has magnitude at least `N`, or the potential index does. Thus
the majorant norm is at most `‖a‖‖R_N L_r‖ + ‖R_N a‖‖L_r‖`.

`ReciprocalRowSummation` identifies the physical reciprocal row norms with
these convolution rows. The signed reindexing preserves norms; it does not
assert equality of complex coefficients with opposite reciprocal signs.
`PuncturedLatticeTail` uses Appendix B.1 to prove
`‖R_N L_r‖ ≤ 4s N^(-1/s)` and `‖L_r‖ ≤ 4s`, where `s` is conjugate to `r`.
`DiagonalSummationExponent` shows `p/s=min(1,p-1)` and `s≤max(p,p')`.

`DiagonalSupSummability` constructs the actual diagonal supremum tail in
`ℓ^p` by domination, with bound
`8s ‖φ_-‖_p (‖φ_+‖_p N^(-1/s) + ‖R_N φ_+‖_p)`.
`DiagonalTailPower` raises this estimate to `p` and proves the quantitative
sum bound with explicit constant `c_p=(8 max(p,p'))^p 2^(p-1)`.
`DiagonalSummability` separately proves convergence of the power series,
then bounds component norms by the exact unweighted pair norm and enlarges
the tail from `N` to `N/2`. Its theorem `exists_uniform_diagonalSummability`
is Lemma 6.8(i): one cutoff and open convex potential neighborhood containing
both the given potential and zero work for every larger cutoff. The bound is
`c_p ‖φ‖_p^p (‖φ‖_p^p/N^min(1,p-1) + ‖R_(N/2) φ‖_p^p)`.
The source range `1<p<∞` is retained; no endpoint summability is asserted.

### Lemma 6.8(ii): the double reciprocal region sums

`IteratedConvolutionRows` constructs the outer row obtained by taking an
inner convolution-row norm and multiplying by the other kernel. Its norm
is at most `‖a‖‖b‖‖c‖`. Two powered Young estimates give an actual outer
`ℓ^p` sequence of these norms, including sampling at `2n`. Increasing both
inner exponents contracts the nested norm.

`IteratedRowSums` proves that the associated double power sum is jointly
summable, gives the exact norm-power identity, and justifies interchanging
the kernels. `IteratedRowTails` proves the three-region bound: the first
kernel tail, the second kernel tail, and the near-near contribution. Both
near kernels are truncated strictly inside `N/2`; at a distant output `2n`,
the remaining potential coefficient lies in `R_N a`.

`DoubleReciprocalRows` specializes to the punctured reciprocal lattice.
The two far-region norms agree exactly. Each far region has an `ℓ^p`
majorant with norm at most `‖a‖‖R_M L_r‖‖L_r‖`; the near-region majorant
has norm at most `‖R_N a‖‖L_r‖²`. The cutoff `M=N/2` uses integer division.
`DoubleReciprocalSums` proves the source's signed double sum
`Σ_l Σ_k (‖a(l+k)‖ / |n-l| / |n-k|)^q` as the full row norm to power `q`,
with the resonant terms zero. The regional norm bounds become
`16s² ‖a‖ M^(-1/s)` and `16s² ‖R_N a‖` for the conjugate `s` of `r`.

`DoubleReciprocalSummability` chooses `r=min(p,p')` and proves convergence
of the actual source-conjugate regional power sums. With
`C_p=(16 max(p,p')²)^p`, each far sum is bounded by
`C_p ‖a‖_p^p/M^min(1,p-1)` and the near sum by `C_p ‖R_N a‖_p^p`.
All sums range over signed integer frequencies, so they also control distant
subsets. This establishes the reciprocal estimates following (1.16) in both
exponent ranges. The full-index Hölder test and application to the actual
coefficients, the near-region extra potential tail, and the final weighted
supremum power sum are proved below.

### Lemma 6.8(ii): actual weighted off-diagonal Hölder bounds

`IteratedRowTesting` proves the two-index Hölder estimate with constant one,
retaining the nested row norm and both testing-sequence norms. The complete
absolute double series is jointly summable before any change of order.
`SpectralReflection` constructs the exact physical reflection isometry for
all source spectral weights; scalar modulation commutes with reflection
with its sign reversed. Thus `‖reflection f‖_(w,p;n)=‖f‖_(w,p;-n)`.

`OffDiagonalSeries` expands both components of the actual `T_n²` operator,
then proves both off-diagonal remainder identities. The negative remainder
uses `φ_-(−(n+l)) φ_+(l+k) u_1^-(-k)`, and the positive remainder uses
`φ_+(n+l) φ_-(−(l+k)) u_0^+(k)`, each with denominators at `l` and `k`.
The leading terms remain `φ_-(-2n)` and `φ_+(2n)` respectively.

`WeightedDoubleRow` normalizes the reciprocal indices to `j=n-l`, `k=n-m`.
Submultiplicativity gives the exact transfer
`w(2n) ≤ w(2n-j) w(2n-j-k) w(2n-k)`.
The outer weighted potential has its original norm, and the weighted input
has exactly its source shifted norm. The reciprocal strip bound and the
two-index Hölder test give joint absolute convergence and a bound with the
full double reciprocal row retained.

`OffDiagonalHolder` identifies the physical series with this test and proves
its joint absolute convergence. The even-vector half-contraction estimate
gives the actual negative bound `2‖φ_-‖²` times the double row of the weighted
positive potential. The positive bound uses `2‖φ_+‖²` and the weighted
reflected first potential. Both include the factor `w(2n)` on the actual
remainder norm and require no reality condition on the potential.

`OffDiagonalUniformBound` defines the two parameter-independent majorants.
One open convex potential neighborhood containing the given potential and
zero, and one cutoff, make both bounds valid on every distant full closed
strip. The theorem includes equality of the analytic extensions with the
original coefficients. All finite Banach exponents are covered, including
`p=1` with its conjugate infinity row. This is the full-index form of (1.16);
the regional refinement and weighted supremum power sum are proved next.

### Lemma 6.8(ii): weighted supremum power sums

`DoubleSeriesRegions` partitions the product lattice into disjoint first-far,
second-far-with-first-near, and near-near regions. Joint absolute convergence
justifies the exact sum decomposition. `DominatedDoubleTesting` transfers
pointwise majorization to both absolute convergence and the two-index Hölder
bound. `OffDiagonalRegions` applies this to the actual weighted series.
At `|n|≥N`, both near potential indices have absolute value at least `N`.
The near estimate therefore retains `‖R_N d‖` and the row of `R_N a`;
the two far estimates use full potential norms and one reciprocal tail each.

`OffDiagonalTailBound` combines these estimates with the actual even-vector
bound. Its nonnegative majorant controls both analytic remainder extensions
throughout distant full strips, on one open convex potential neighborhood
containing the given potential and zero, for every larger cutoff.
`OffDiagonalPower` proves the majorant's entire signed `p`-power series
converges and sums it using the previously established reciprocal bounds.

`SpectralReflectionTail` preserves the exact weighted tail and its norm under
reflection. `HalfCutoffPower` proves that replacing `floor(N/2)` by `N` costs
at most three for decay exponents in `[0,1]`, including odd cutoffs.
`OffDiagonalPairPower` then gives the source pair-norm bound with
`C_p = 3 · 4^p · 2^(p-1) · (16 max(p,p')²)^p`.
The intermediate estimate retains the product of the two component norms
and the product of their actual tails at `N`.

`OffDiagonalSup` defines the actual weighted supremum over the entire
unbounded closed strip. It is nonnegative, bounds each actual value, and
is bounded by the regional majorant at every valid cutoff. A separate identity
proves it equals `w(2n)` times the ordinary supremum of the remainder norm.
`OffDiagonalSummability` proves the actual conditional power series converges
and satisfies

`Σ_{|n|≥N} (w(2n) |b_n^± - leading_n^±|_{U_n})^p`
`≤ C_p ‖φ_±‖_(w,p)^p (‖φ‖_(w,p)^(2p)/N^min(1,p-1) + ‖R_(N/2)φ‖_(w,p)^(2p))`.

The leading modes retain the physical signs `φ_-(-2n)` and `φ_+(2n)`.
The range is every finite `p>1`; no reality assumption or normalization
`w(0)=1` is used. Both signs and all larger cutoffs share one neighborhood
and threshold. Together with the earlier diagonal and analytic results,
this completes the proof-consistent version of Lemma 6.8.

**Source-display qualification.** Visual inspection confirms that the
statement of (ii) on source page 41 omits the `p`-powers on its left side
and writes `‖φ_+‖^(2p)` in its first numerator. The concluding estimate in
the proof on page 43 has the `p`-power sum and the full pair norm `‖φ‖^(2p)`.
The Lean theorem follows that proof formulation, with the stated half-cutoff
tail. It does not establish the literal page-41 display. This discrepancy
is distinct from the earlier, explicitly disproved unconditional reality
claim in Lemma 6.7.

### Lemma 6.9: uniform localization, boundary comparison, and root gaps

`UniformPowerTail` makes the scalar budgets in Lemma 6.8 uniformly small.
A bound on the full weighted norm and one weighted Fourier tail defines an
open convex neighborhood containing the potential and zero. The construction
works for every positive norm exponent and decay exponent, including the
fractional powers used below `p=2`, and controls every larger integer cutoff.

`ResonantSupSmallness` uses convergence of the actual power sums to bound each
individual supremum by an arbitrarily prescribed positive tolerance. Both
coefficient estimates retain locally uniform neighborhoods and thresholds.
`ResonantCoefficientSmallness` proves weighted decay of the signed leading
Fourier modes, including cutoff boundaries. Adding those modes to the actual
remainders gives smallness of the full `b_n⁻` and `b_n⁺`. In particular,
`|a_n|≤π/32` and `|b_n^±|≤π/16` hold over all sufficiently distant full closed
strips on one open convex neighborhood. This proves the opening estimates
of Lemma 6.9 for every finite `p>1`, with arbitrary source spectral weights.

`ResonantDeterminantAnalytic` defines
`F_n(z)=(z-nπ-a_n(z))²-b_n⁺(z)b_n⁻(z)` from the actual analytic extensions.
It equals the determinant of the reduced matrix wherever the complementary
square is small, and is jointly analytic on the existing correction domain.
For unit weight, its zeros are exactly the original periodic spectral points
under the established reduction hypothesis. At zero potential it is exactly
`(z-nπ)²`, including at the strip center and at nonreal parameters.

`ResonantDeterminantBounds` gives the scalar perturbation estimate
`|F-q²|≤2|q||a|+|a|²+|b⁺||b⁻|`. The numerical coefficient bounds imply that
every zero has `|z-nπ|≤3π/32`, strictly inside the source disc of radius `π/4`.
On that disc's boundary, `|F_n(z)-(z-nπ)²|<|(z-nπ)²|` holds.
`ResonantDeterminantLocalization` establishes these conclusions for the
actual determinant, with analyticity and original matrix agreement sharing
one neighborhood and threshold. There are no zeros in the remainder of the
full strip. This supplies the strict boundary comparison needed for Rouché.

`ResonantCauchyGap` proves that the closed disc of radius `π/4` around each
point of the refined disc stays in the full strip. Cauchy's estimate gives
`|a_n′|≤1/8`, and the complex mean-value theorem yields the corresponding
Lipschitz bound. Two squared residual estimates then give the factor six
without selecting square-root branches.
`ResonantRootGap` defines the actual full-strip supremum `|b_n⁺b_n⁻|_{U_n}`,
proves it nonnegative, finite, and at most `(π/16)²`, and establishes
`|ξ-η|²≤6|b_n⁺b_n⁻|_{U_n}` for any two actual strip zeros. All these bounds
are locally uniform; no distinctness or reality assumption on the roots is
needed, and the spectral weight need not satisfy `w(0)=1`.

### Lemma 6.9: scalar analytic multiplicity two and the two roots

`LogDerivativeLocal` factors each finite-order analytic germ and proves that
its logarithmic derivative is its natural analytic order divided by the
centered coordinate, plus an analytic remainder. `FinitePoleRemoval` subtracts
all finitely many such terms and uses meromorphic normal form to fill their
removable values. The filled function is analytic on the whole domain and
agrees with the original remainder away from the listed poles.

`AnalyticZeroCount` sums natural analytic orders. For a function analytic on
a neighborhood of a compact connected set and nonzero at one point, all
orders are finite and the zero set is finite. `ArgumentPrinciple` applies
Cauchy's theorem to the filled remainder and integrates each principal part.
For every positive-radius closed disc with nonzero boundary values, it proves
`∮ f'/f = 2πi · analyticZeroCount f (closedBall c R)`.

`Rouche` proves that a strict relative boundary perturbation has its ratio
in the open disc centered at one with radius one. The principal logarithm of
that ratio has derivative `g'/g-f'/f` along the circle; its contour integral
vanishes. The argument principle then gives equal natural zero counts.
`ZeroCountComparison` computes every centered monomial's count, transports
counts between sets containing the same zeros, and equates open and closed
disc counts when the boundary is nonvanishing.

`ResonantZeroCount` applies these results to the actual determinant and its
centered square. Its scalar analytic multiplicity is exactly two on the
closed radius-`π/4` disc, the open refined disc, and the full source strip.
The boundary is nonvanishing, the strip zero set is finite, and every analytic
order in the strip is finite. One open convex neighborhood containing the
potential and zero and one cutoff work for all distant signed resonances,
all finite `p>1`, and every source spectral weight.

`ZeroMultiset` represents the actual natural orders as root multiplicities.
`ResonantRoots` produces two roots allowing coincidence, proves that they
exhaust the whole strip's determinant zeros, and identifies every strip
point's analytic order with its occurrence count in this pair. Both roots
lie in the refined disc, satisfy the `3π/32` localization bound, and obey
`|ξ-η|²≤6|b_n⁺b_n⁻|_{U_n}` on a common potential neighborhood and cutoff.
No reality, distinctness, or normalization `w(0)=1` is required.

### Lemma 6.9: displacement source audit and valid per-root powers

Visual inspection of printed page 43 confirms that its displacement budget
is `C_p (B^p/N^min(1,p-1) + T^p) (1+B^p) B^p`, where `B=‖φ‖_p`
and `T=‖R_(N/2)φ‖_p`. The displayed left-hand side repeats the positive root
label; the discussion concerns both roots. The norm-factor issue below also
persists with that repeated label.

`SingleResonantPotential` puts amplitudes `a,b` at physical frequencies
`-2n,2n`. The actual complementary free inverse annihilates both resonant
potential sources, so the full correction fixes them and the determinant
is exactly `(z-nπ)²-ba` wherever the proved small-square condition holds.
Unit-weight Fourier modes have precisely their amplitude norm; at `p=2`,
the squared pair norm is `|a|²+|b|²`.

`RootDisplacementSourceAudit` specializes to `a=b=t>0`. Its roots are `nπ±t`
and the pair norm squared is `2t²`. Using the actual Fourier-tail contraction,
the printed Hilbert budget is at most `24 C t⁴` for `t≤1` and cutoffs at least
one. The formal theorem `exists_resonantRoot_exceeding_printed_budget` proves:
for every nonnegative proposed constant, every open potential neighborhood
of zero, and every prescribed cutoff, there is a positive resonance beyond
that cutoff and a potential in the neighborhood with an actual refined-disc
root whose squared displacement exceeds the printed budget. The witness
satisfies the actual small-square condition. The companion negation theorem
rules out even the locally uniform single-root consequence of the display.

This disproves the claimed local uniformity at zero. It does not assert
failure of an eventual bound for each fixed potential with an unrestricted
potential-dependent cutoff: a fixed finitely supported potential could have
its exceptional resonance excluded. The counterexample instead allows the
single resonant frequency to lie beyond any shared cutoff.

`RootDisplacementPower` supplies the valid starting estimate. For
`(q-a)²=bc`, it proves `|q-a|≤(|b|+|c|)/2` and, for every real `P≥1`,
`|q|^P≤2^(P-1)(|a|^P+(|b|^P+|c|^P)/2)`. The actual determinant corollary
splits each full off-diagonal coefficient into its signed leading Fourier
coefficient and remainder, retaining all four power terms. It uses no
square-root branch, root distinctness, or reality assumption.

### Lemma 6.9: corrected quantitative displacement power sum

`SampledPowerTail` proves that injective sampling of high Fourier modes has
a convergent power sum bounded by the exact source remainder norm.
`ResonantLeadingPowerTail` applies this to both signed frequencies `-2n,2n`
and preserves the spectral weight. The sum of their weighted `p`-powers for
`|n|≥N` is bounded by `‖R_M φ‖_(w,p)^p` for every `M≤2N`, including the
cutoff boundary. In particular, the half-cutoff tail gives the required
additive term without a potential-norm prefactor.

`ResonantDisplacementMajorant` combines the actual diagonal supremum, both
actual weighted remainder suprema, and the two leading powers. This same
nonnegative sequence bounds `|ξ-nπ|^p+|η-nπ|^p` for every pair of actual
strip zeros. `DisplacementMajorantSum` proves convergence and the exact
linear combination of these four convergent series.

`RootDisplacementBudget` combines the estimates into
`C_p [T^p + (B^p/N^δ+T^p)(1+B^p)B^p]`, where
`B=‖φ‖_(w,p)`, `T=‖R_(N/2)φ‖_(w,p)`, and `δ=min(1,p-1)`.
The explicit constant is `(2K+K²)(1+C_diagonal+C_offDiagonal)`, with
`K=2^(p-1)` and the previously proved diagonal/remainder constants. Its
Hilbert value is `3149832`. The additive `T^p` is retained separately from
the nonlinear expression whose literal printed form failed near zero.

`UniformDisplacementMajorant` supplies one open convex neighborhood containing
the potential and zero and one cutoff for all larger convergent majorant
tails. Forgetting a spectral weight contracts both the potential and its
Fourier tail, so the diagonal estimate fits the same weighted pair budget.
The two off-diagonal component prefactors combine into the exact pair norm.

`exists_uniform_resonantRoots_with_displacement_sum` selects the two actual
scalar roots for each distant signed mode. Their occurrence counts equal
all actual analytic zero orders in the strip, they exhaust its zeros, both
lie in the refined disc and within `3π/32` of its center, and they satisfy
the factor-six gap bound. On the same neighborhood and cutoff, every larger
two-sided displacement power tail is genuinely summable and satisfies the
corrected budget. This holds for every finite `p>1` and every source spectral
weight, including `w(0)>1`. No continuous root labeling is claimed.

The original periodic spectral identification and individual algebraic
multiplicities are now proved below. The literal printed displacement bound
remains excluded by the source audit.

## Corrected weighted gap power sums

`resonantRoots_gap_le_majorant` transfers the weight to the actual full-strip
product supremum and bounds the weighted gap power by leading and remainder
powers. The explicit constant `G_p=2^p (2^(p-1))²` is valid for every finite
`p≥1`, including above two; it equals `16` in the Hilbert case. No square-root
branch or reality assumption is used.

For finite `p>1`, `exists_uniform_resonantGapMajorant` supplies a common open
convex potential neighborhood and signed cutoff. Every larger majorant tail
converges and is at most
`G_p [T^p + E_p B^p (B^(2p)/N^min(1,p-1) + T^(2p))]`,
where `B=‖φ‖_(w,p)`, `T=‖R_(N/2)φ‖_(w,p)`, and `E_p` is the proved
`offDiagonalSummationConstant p`. Only the off-diagonal remainder estimates
enter; the leading Fourier tail remains additive.

`exists_uniform_resonantRoots_with_power_sums` gives the same two roots with
both displacement and weighted gap power sums for every larger cutoff. It
retains full-strip zero detection, exact scalar analytic multiplicities,
localization, and the factor-six squared gap bound. The gap tail is unchanged
by exchanging the roots and agrees with the source product `w_(2n)^p |γ_n|^p`.
The signed tail includes its boundary and allows nonnormalized weights.

This is a corrected scalar-root estimate toward Proposition 6.3. Propositions
6.1 and 6.3 repeat the source's nonlinear-only budget with locally uniform
cutoffs; those literal displays are not claimed. The bridge to the original
periodic spectrum and its algebraic multiplicities is now proved below.

## Original periodic eigenvalue identification and intrinsic gap sums

`UnweightedResonantDeterminant` proves that the actual correction entries,
and therefore the full scalar determinant, survive forgetting the spectral
weight. Both complementary inverses must be in their contraction domains;
the uniform square estimate supplies these hypotheses simultaneously on all
distant strips. The resulting zero criterion detects the original periodic
spectrum of the physical coefficient pair for every source weight.

`SpectralRootPair` identifies the enclosed spectral set with the scalar root
pair. The previously proved spectral algebraic count two and positivity force
multiplicity one at each distinct value, or multiplicity two when they
coincide. Therefore each scalar analytic order equals the original spectral
algebraic multiplicity throughout that distant strip, including zero away
from the two roots. This is a local high-frequency identification, not a
claim about arbitrary operator-valued analytic determinants.

`PeriodicResonantPair` packages the exact original strip spectrum, both
multiplicity descriptions, root localization, and the intrinsic contour
midpoint and squared gap. The latter are exactly `(ξ+η)/2` and `(ξ-η)²`.
`exists_uniform_periodicRoots_with_power_sums` gives these pairs together
with both corrected quantitative power tails on one open convex potential
neighborhood and cutoff. Any two counted pairs agree up to exchange;
`periodicRoot_powerTails_eq` allows that exchange independently at every mode.
No continuous labeling or distinct-root assumption is used.

`periodicGapPowerTail` uses the original contour-defined squared gap directly:
its nonzero terms are `w_(2n)^p |periodicSquaredGap_n|^(p/2)`.
`exists_uniform_periodicGapSummability` proves convergence and the corrected
`rootGapBudget` for every larger cutoff, independently of all root choices.
Thus the corrected versions of Propositions 6.1 and 6.3 now concern original
periodic eigenvalues and the intrinsic spectral gap, with the additive
leading-tail contributions retained.

## Midpoint and ordinary boundary displacement sequences

`SpectralDisplacementTail` bounds a single displacement power series by any
summable majorant. A finite signed low-frequency interval contains every
omitted term, so summability of one power tail implies global `Memℓp`
membership for the actual displacement sequence. Low modes can be arbitrary.

`norm_midpoint_displacement_rpow_le` proves the precise factor one half for
every real exponent at least one. Applied to the original contour midpoint,
`exists_uniform_periodicMidpointSummability` gives its global `ℓp`
displacement sequence and every larger power tail, bounded by
`rootDisplacementBudget / 2`. A common open convex neighborhood and cutoff
work for every source weight and every finite `p>1`.

`exists_uniform_boundaryDisplacementSummability` uses the existing simple
boundary eigenvalue in each distant disc. Each is an original periodic root
in the same strip, so its displacement power is bounded by the two-root sum.
Both ordinary Dirichlet and Neumann branches share the potential neighborhood
and cutoff; each has a full `ℓp` displacement sequence and every larger tail
bounded by the corrected displacement budget of the reflected potential.

`periodOneBoundaryPotential` composes the completed Dirichlet interval
extension with the source pair-norm realization. Both ordinary boundary
problems use this same potential extension. Pulling back the neighborhood
proves `exists_uniform_periodOneBoundaryAsymptotics` for original period-one
coefficient inputs at all finite `p>1`. The output Fourier tail is that of
the actual reflected potential; no unproved estimate replaces it with an
input tail. Both free branches retain the signed value `nπ`.

`exists_uniform_classicalBoundaryAsymptotics` transfers the estimate to
arbitrary original physical interval `L²` potentials. Both classical
Dirichlet and Neumann branches have square-summable displacements, and their
high-disc singleton characterization as actual original eigenvalues holds
on the same open convex neighborhood and cutoff as the quantitative tails.

The ordinary coefficient/physical realizations and midpoint consequence are
proved above. The auxiliary coefficient realization and starred displacement
conclusions, coefficient multiplicities, and physical auxiliary endpoint and
eigenvalue-set identifications are proved below, together with the independent
physical operator and resolvent, generalized multiplicities, and uniform
starred asymptotics.

## Auxiliary spectra, physical endpoint realization, and starred asymptotics

`AuxiliaryPhase` gives the exact linear isometry
`G(f₋,f₊)=(f₋,if₊)` in the base and one-derivative norms. Its potential phase
map is `(φ₋,φ₊)↦(iφ₋,-iφ₊)`, also an isometry. The actual operator identity
is `L(φ) G = G L(iφ₋,-iφ₊)`, with corresponding identities for `z-L` and the
eigenvalue equation. A potential is Neumann-reflected exactly when its
phase transform is Dirichlet-reflected.

`AuxiliarySpaces` defines the auxiliary base spaces and all real Sobolev
spaces as phase images of the ordinary ones. Their raw Fourier conditions
are `f₋(n)=-i f₊(-n)` for auxiliary D and `f₋(n)=i f₊(-n)` for auxiliary N.
They are closed and complementary; phase transport is an isometry on the
actual base and domain spaces, and the domain inclusion preserves the same
condition. No physical endpoint equivalence is inferred solely from these
coefficient formulas.

`AuxiliarySpectrum` restricts the actual `z-L(φ)` pencil to those auxiliary
spaces for Neumann-reflected potentials. The auxiliary resolvent set is
defined by bijectivity of that pencil. A proved conjugation identifies its
resolvent set and spectrum with the ordinary restricted problem at the
transformed potential. Both auxiliary spectra are closed, discrete, and
finite in bounded sets. Spectral membership is equivalent to a nonzero
eigenvector satisfying the actual operator equation in the auxiliary domain.
This proves the coefficient discreteness assertion of Proposition 5.2;
its generalized multiplicity counts are transported below.

`auxiliaryPeriodOnePotential` uses the source's completed Neumann potential
extension, for both starred problems. The auxiliary high-index trace branch
is the unique actual auxiliary spectral value in its disc.
`exists_uniform_auxiliaryPeriodOneAsymptotics` gives one open convex source
potential neighborhood and cutoff for both branches: global displacement
`Memℓp`, unique high-disc spectral identification, and every larger convergent
power tail bounded by the corrected budget of the phase-conjugated reflected
potential. Both free auxiliary branches retain every signed index.
Together with the ordinary result, all four coefficient displacement
conclusions of Corollary 6.2 hold for every finite `p>1`.

`AuxiliaryRootSpaces` defines generalized eigenspaces recursively using the
actual auxiliary pencil and domain inclusion at every step. Phase conjugation
identifies each level with the ordinary boundary root space of the transformed
potential. The full root space has finite dimension, is closed, and stabilizes.
Auxiliary algebraic multiplicity is defined as its actual dimension; the root
space equivalence proves equality with ordinary boundary multiplicity. It is
positive exactly on the actual auxiliary spectrum and zero on the resolvent set.

`AuxiliaryCounting` defines finite clusters directly from the actual auxiliary
spectrum. Both auxiliary restrictions have central algebraic count `2N+1`
and one simple eigenvalue in each high disc, with no spectrum outside the
proved localization regions. One open convex neighborhood containing the
potential and zero supports these conclusions for every larger cutoff. The
source Neumann extension transfers the same counts to period-one coefficient
pairs for every finite `p>1`. These use the proved safe central box, retaining
the separate qualification on the printed general-p height.

`ClassicalAuxiliaryPhase` defines the original H¹ auxiliary domains using
exactly `f₋+if₊=0` for D* and `f₋-if₊=0` for N* at both endpoints.
Pointwise physical phase conjugation identifies these conditions with the
ordinary domains and intertwines the actual differential expressions. Physical
auxiliary eigenvalues are defined directly by nonzero original eigenfunctions;
these sets are closed, discrete, and finite in bounded regions for L² potentials.

`ClassicalAuxiliaryExtension` constructs the source reflected function with
`(-if₊,if₋)` on the second half, with the D*/N* sign. Its Sobolev extension
reconstructs the source function on `[0,2]` and the original function including
both endpoints of `[0,1]`. Every auxiliary coefficient-domain vector comes
from an original endpoint function, and that weighted representative is unique.
This establishes the set-theoretic domain identification; the physical norm
and topological isomorphism are constructed below.

`ClassicalAuxiliarySpectrum` defines the Neumann potential extension by actual
normalized physical Fourier integrals. Its phase equals the Dirichlet extension
of the physically transformed potential. This gives equality of the original
auxiliary eigenvalue sets with the actual coefficient spectra and proves both
directions of the eigenvalue equation transfer, using the actual Sobolev
extension in Lemma 5.1. The independent physical L² resolvent is constructed
below, followed by multiplicity from actual physical generalized root spaces.

`ClassicalAuxiliarySpace` stores actual functions on the original closed
interval. Its membership criterion is exactly the auxiliary H¹ endpoint
condition. The norm equals the physical component-sum H¹ norm, and phase
rotation is an isometry from the complete ordinary endpoint domain. Actual
Fourier extension and physical restriction give a continuous linear equivalence
with the auxiliary weighted domain, with explicit bounds `1` and `√2 π`.

`AuxiliaryPhysicalL2` supplies isometries for the function and potential phases
on the original physical L² space. `ClassicalAuxiliaryOperator` uses them to
construct actual domain inclusion and the auxiliary operator; its realization
theorems identify the outputs with the original physical functions and their
differential expression for arbitrary representatives. Inclusion is injective
and has dense range.

`ClassicalAuxiliaryResolvent` defines its resolvent set by actual physical-pencil
bijectivity. It equals the ordinary physical resolvent set at the transformed
potential. The constructed bounded inverse satisfies both inverse identities
between original L² and auxiliary H¹, and the base-space resolvent is compact.
The physical spectrum equals both the original auxiliary eigenvalue set and
the actual auxiliary coefficient spectrum of the Neumann potential extension.

`ClassicalAuxiliaryClosed` constructs the unbounded operator inside physical
L². Its potential-independent domain is exactly the L² classes of original
auxiliary H¹ functions. Its values are the actual differential expression,
its domain is dense, and the physical resolvent proves its graph is closed.

`ClassicalAuxiliaryRootSpaces` defines the actual physical Jordan-chain
recursion using the auxiliary pencil and physical inclusion. Every intermediate
vector requires the original auxiliary H¹ domain. Phase conjugation identifies
all finite levels and full root spaces with ordinary physical root spaces. The
full space stabilizes, has finite dimension, is closed, and is contained in
the original unbounded auxiliary domain.

`ClassicalAuxiliaryMultiplicity` defines multiplicity as this actual physical
full-root-space dimension. It agrees with ordinary physical multiplicity at
the transformed potential and with actual auxiliary coefficient multiplicity
at the Neumann extension. It is positive exactly on the physical spectrum
and zero on the resolvent set; every signed free mode has multiplicity one.

`ClassicalAuxiliaryCounting` defines central clusters from the original
physical spectrum. Both conditions have central algebraic count `2N+1`,
one simple eigenvalue per high disc, and no spectrum outside the proved
localization regions. One open convex physical L² neighborhood containing
the given potential and zero supports every larger cutoff, with analytic
high-index branches that equal the auxiliary coefficient trace branches.

`ClassicalAuxiliaryAsymptotics` combines those physical counts and analytic
branches with the physical starred displacement estimates. On one common
neighborhood both branches have full `Memℓp` membership at `p=2`, unique
algebraically simple high-disc values, and every larger convergent displacement
power tail bounded by the corrected budget of the transformed reflected
potential. This proves the original physical L² starred part of Corollary 6.2.

`HalfIntervalReality` proves that the completed half-interval map commutes
with conjugation and index reversal for every `1<p<∞`. Even coefficients use
the exact half-normalization; odd coefficients use the full shifted-Hilbert
series and its reflected reciprocal kernel.

`AuxiliaryReality` then proves that both signed source interval extensions
preserve real type. In particular, the Neumann potential extension used for
both auxiliary problems preserves it in the source period-one pair topology.
For real-type potentials, every actual auxiliary spectral value is real, and
every nonreal parameter belongs to the actual auxiliary resolvent set. The reflected coefficient
result also includes `p=1`. This proves Proposition 5.2(iv) for the source
coefficient problems without an extra assumption on the extended potential.

`ClassicalAuxiliaryReality` defines physical real type a.e. on the original
interval and proves its invariance under changes of representative. Conjugation
of the actual half-interval integrals and the folded coefficient formula prove
real type of the actual Neumann potential coefficients for arbitrary original
L² data. Both original endpoint eigenvalue sets and both closed physical
auxiliary operator spectra are real; nonreal parameters lie in their physical
resolvent sets. These results include potentials changed on null sets.

**Remaining scope.** Verify the bounded source period-one auxiliary
eigenfunction extensions.
The printed general-`p` central-height issue and the global nonlinear
coordinate construction remain open.

## Verification

Run `./scripts/check.sh` to build, check public-API examples, and audit transitive
axioms. The current audit covers 6459 declarations under `NLS`, including generated
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

Full-range interval checks cover norm-preserving insertion at `p=1` and `p=∞`,
negative odd indices and opposite-parity zeros, the half-map normalization and
injectivity, and reflected nonreal input modes that distinguish Dirichlet and
Neumann signs. The one-sided constant displays the normalized odd reciprocal
tail. Other checks cover arbitrary-input boundary membership, bounds into the
boundary subtype, analyticity, physical finite integral agreement, uniqueness,
and preservation of the exact Parseval energy identity at `p=2`.

Continuous-synthesis checks recover a negative odd mode with imaginary amplitude,
verify actual normalized integrals, and rule out an accidental period-one
restriction. They cover uniform convergence at `p=3`, the uniform bound at `p=1`,
reflection without complex conjugation, both zero endpoint traces of a sine-type
combination, uniqueness of continuous representatives, and agreement with the
`L²` Fourier inverse.

Derivative checks cover the imaginary constant's zero derivative, a negative odd
mode's signed half-period increment, vanishing full-period derivative mean, and
the positive real derivative coefficient from a negative frequency with imaginary
amplitude. They instantiate absolute continuity, almost-everywhere classical
differentiation, physical square integrability, the factor-two integral bound,
and vector-valued primitives on reversed intervals.

Converse-Sobolev checks construct classical hypotheses directly from smooth
physical waves, recover a negative odd mode and its coefficient support, and
retain the odd mode's endpoint sign. They check reconstruction from arbitrary
classical AC/`L²` hypotheses, the other inverse, the nonzero endpoint correction
for an imaginary ramp at frequency zero, complex integration by parts on a
reversed interval, and negative-frequency derivative coefficients with matching
endpoints.

Classical interval checks fold a nonperiodic ramp into a triangle with a corner
at the join and verify its reflected derivative sign almost everywhere. They
cover both actual weighted boundary spaces, the Neumann signed swap on the
second half, exact endpoint restriction, general `L²` folding without matching
joins, and signed negative-frequency coefficient reflection.

Restriction checks retain positive and negative odd modes, prove that a valid
Dirichlet mode has different values at the two interval endpoints, and verify
the Neumann endpoint signs. They also exercise the right inverse on a negative
odd mode, full-interval injectivity, and unique representation of arbitrary
classical Neumann data.

Energy checks retain the length-two factor for arbitrary complex constants, the
component-sum pair norm, and the exact derivative energy `2(1+9π²)` of the odd
mode `exp(3iπx)`. A reflected ramp has energy `8/3` despite its corner. Further
checks cover both norm bounds for a negative odd Neumann mode and vanishing of
both endpoint values when the physical norm is zero.

Bundled-domain checks verify complex Banach-space instances, pointwise vector
operations, complex linearity, continuity, and Neumann endpoint signs. A constant
Neumann pair has norm `√2`, detecting the physical component-sum convention.
Further checks recover actual Fourier integrals at an odd negative index,
exercise inverse identities on an odd Neumann mode and original classical data,
and instantiate both operator-norm bounds.

Physical-product checks cover negative odd modulation of arbitrary `L²` data,
norm preservation, complex mode amplitudes, and the exact zero-frequency
physical integral. Distinct constant matrix entries detect off-diagonal swaps;
a nonzero wave verifies both derivative signs and the factor `π`. Further
checks establish square-integrable physical outputs and exercise the reverse
physical-to-coefficient eigen-equation and nonzero preservation.

Interval-transfer checks reconstruct a square-integrable potential with a
midpoint jump. The constant Neumann eigenfunction `(1,-1)` for potential `(2,2)`
retains eigenvalue `-2`; the potential's zero coefficient stays `+2` and the
reflected-half equation has the correct sign. This example enters both the
already-constructed boundary and periodic spectra. The checks also exercise
transport of a.e. equalities for either signed extension.

Eigenvalue-set checks retain negative odd free modes for both boundary conditions,
produce an original nonzero Neumann eigenfunction from a coefficient eigenvalue,
and exclude the nonreal value `i` for the free potential. A potential supported
at one interior point has exactly the free lattice. Further checks cover finite
intersection with any closed disk and original eigenfunction existence for every
periodic spectral point of a Dirichlet-reflected potential.

Physical-potential checks verify completeness and complex scalars. The constant
pair `(3,4i)` has physical norm `5`, reflected coefficient squared norm `25/2`,
and zero coefficient `(3+4i)/2`. Further checks cover a.e. equality of the classes,
complex linearity, injectivity, negative odd free branches, and original nonzero
`H¹` eigenfunctions and analytic branches on a common physical neighborhood.

Base-space isomorphism checks cover full surjectivity and both-sided inversion,
Neumann zero-mode differences, and the negative swap on the reflected half.
Negative odd modes survive base/domain transport and have physical norm `√2`
without the frequency weight. A discontinuous original step function also
round-trips through Neumann extension, and arbitrary Neumann inverse classes
agree with actual physical restriction almost everywhere.

Original-operator checks verify physical inclusion and the matrix action
`(1,-1) ↦ (-2,2)` for the Neumann domain and potential `(2,2)`, for both the
bounded domain map and the unbounded partial map. Original classical data alone
proves domain membership. The free physical spectrum is exactly `πℤ`; at `i`
both inverse identities hold on arbitrary physical inputs. Further checks cover
compactness for arbitrary potentials, closedness, and base-space graph recognition.

Physical-root checks distinguish length-two Jordan chains from ordinary
eigenvectors and preserve that distinction under Fourier transport. Negative
odd free eigenvalues have full physical root-space dimension one. Generalized
vectors admit original classical domain representatives. Further checks combine
central physical multiplicity sums, unique algebraically simple high-disk
spectral points, and analytic branches on one common neighborhood, and verify
the periodic multiplicity split.

Rectangle-contour checks compute both coordinate-function integrals around the
unit square and reverse one orientation, detecting the signs of both edge pairs.
They retain corners and exclude the central interior, check polynomial Cauchy
vanishing on a nonsquare rectangle, and exercise both subdivisions. At `p=3`,
a free rectangle above the real axis contributes zero. Further checks exercise
edge deformation without a resolvent-interior assumption on the retained box,
uniform compactness, and evaluation of the domain factorization.

Residue checks use an off-center pole in a nonsquare rectangle, an exterior
pole, every higher pole order, and a vector-valued normalized residue. The
existing explicit coupled `p=3` potential supplies a genuine length-two Jordan
chain at `π`; an admissible central rectangle fixes its generalized vector,
which remains outside the ordinary eigenspace. A further check exercises the
inclusion of the whole central algebraic range in the rectangular integral range.

Whole-space contour checks interchange an integrand with poles inside both
contours and evaluate its mixed integral as `(2πi)²`. At `p=1` the rectangular
and algebraic operators agree on arbitrary inputs. At `p=3` every complementary
component `x-Px` is annihilated. Further checks instantiate one neighborhood
with operator-norm analytic actual rectangular projections and exact rank
`4N+2` for every larger cutoff.

Explicit-height checks exercise both printed Hilbert boundary signs at norm
one, the whole `p=3` unit norm ball at height `15625`, and signed free spectral
endpoints in the height-one box. A numerical-criterion failure is paired with
a proof of actual resolvent membership, keeping those concepts distinct.
Further checks instantiate uniform full algebraic counting in each potential's
own Hilbert height box.

Moving-contour checks identify the whole free projection in a rectangle with
asymmetric vertical endpoints and compute its rank two. A discontinuous choice
of sufficient height still yields analytic projections. The explicit non-Hilbert
norm-height contour also retains the existing genuine length-two Jordan chain,
whose generalized vector remains outside the ordinary eigenspace.

Pair-norm checks use components of amplitudes `3` and `4i` at frequencies
`-3` and `5`: the `p=1` norm is seven, the Hilbert norm is five while the
maximum norm is four, and the cubic energy is 91. Equal negative-frequency
components attain the comparison constant. A one-derivative pair has exact
energy 720; a negative fractional Sobolev exponent retains the product `sp`.
Both printed Hilbert edges at height 1681 are admissible in the source norm.
Further checks exercise coefficient preservation and uniform analytic rank
on the actual component-sum parameter space.

Period-one checks retain negative-frequency signs, sample arbitrary even
sequences, and preserve the scalar supremum norm. A convolution shifts input
index `-2` by `3` before doubling to output index `2`. The actual wave and
unit-period coefficient of a negative odd input are recovered. A discontinuous
sawtooth has vanishing negative odd coefficients and mean exactly `1/2`,
checking the period normalization independently of continuous synthesis.
Further checks preserve the component-sum pair norm and the odd resolvent sector.

Distribution checks test complex linearity at negative frequencies, the constant
mode's integral normalization, and coefficient recovery for arbitrary cubic
inputs. The constant-one sequence at infinity is proved not to lie in `l1`;
its coefficients are nevertheless recovered, and its finite Fourier truncations
converge distributionally. An explicit odd-frequency test distinguishes its
period two from period one, while doubling makes it period one. Arbitrary
Schwartz tests also check agreement with both continuous synthesis conventions.

Derivative checks recover the physical negative-frequency sign, the zero-mode
derivative, and the full cubic derivative domain. They verify weak integration
by parts on continuous non-Hilbert representatives and exponent-independent
synthesis. The constant-one sequence at infinity has a genuine distributional
derivative whose coefficients are proved unbounded, so it is outside the
one-derivative domain. Both free-component signs and endpoint graph limits
are checked through the public API.

Product checks exercise Mathlib's actual wave multiplication with two negative
frequencies, complex amplitudes, and a nondecaying infinity-exponent potential.
They check ordinary integral products, absolute convergence on the cubic domain,
arbitrary simultaneous smooth approximations, and uniqueness of the continuous
extension. A unit off-diagonal potential has a nonzero constant-pair eigenstate
for the full actual distributional equation at eigenvalue one.

Periodization checks verify the opposite sign for a negative-frequency test,
the window's real-line integral one versus its periodization one half, absolute
convergence at a negative nonintegral argument, and an explicit two-mode lift
with imaginary amplitudes. Testing against an infinity-exponent imaginary mode
produces `-2`, checking bilinearity and the period factor. Further checks exercise
uniform approximation, translation differences, and the cubic annihilator criterion.

Smooth-periodization checks identify the derivative at every real argument with
the sum of translated Schwartz derivatives, retain an odd mode's negative
second-derivative sign, and annihilate the constant window at every positive
order. They exercise fifth-derivative uniform approximation, absolute sixth-
derivative translate sums, continuity in the fourth-derivative uniform norm,
and genuine pointwise Schwartz multiplication by periodized tests.

Windowed-reconstruction checks retain the exact `1,2,1` Leibniz coefficients
in the polynomial-weight-three, derivative-order-two estimate. They verify the
constant-window factor one half in Schwartz convergence and imaginary amplitudes
on a polynomial with negative and positive modes. Genuine nonperiodic point
masses and their derivatives act term by term on the series; the derivative
check retains the dual minus sign and includes absolute convergence.

Intrinsic-identification checks cover Schwartz convergence of translated products
with unrestricted windows, polynomial weight three and derivative order four,
and invariance under translation by `-6`. Imaginary amplitudes on a negative
wave test the reflected coefficient and complex linearity. Abstract periodic
inputs exercise kernel annihilation, absolute reconstruction, cubic regularity,
and the full infinity endpoint. Constant-one coefficients identify the
nondecaying infinity synthesis. A single real-line Dirac mass is proved not
periodic, testing the necessity of that hypothesis. A geometric Schwartz series
sums to exactly twice its window in Schwartz topology.

Weighted-distribution checks instantiate the intrinsic converse at regularity
`-3/2` and exponent three. The raw sequence `a(n)=n` is constructed at regularity
`-1`, exponent infinity, and proved unbounded in the unweighted infinity class.
Its negative coefficient is recovered without a weight factor, its truncations
converge as distributions, and multiplying its synthesis by `iπ` gives the genuine
derivative of the constant-one coefficient distribution. Other checks compare
raw data across weights and exponents and recover the earlier unweighted
realization at zero regularity.

Sobolev-derivative checks cross zero regularity at exponent three and compose
successive inclusions at infinity. An imaginary negative-frequency mode has
the positive real derivative coefficient `3π`; a constant mode differentiates
to zero. Fractional inputs satisfy genuine integration by parts. Endpoint
graph recovery and the intrinsic criterion recover the next regularity, and
zero regularity agrees with the existing Zakharov–Shabat domain derivative.

Endpoint-pair checks use nondecaying equal components to attain factor two
against the maximum norm. Disjoint signed single modes have norm one while the
sum of the separate scalar suprema is two. Their scalar coordinates coincide
at frequency `-1`, checking the essential first-component reflection. Weighted
diagonal modes exercise negative fractional regularity and the exact numerical
norm `1/2` at regularity `-1`. Actual pair synthesis recovers imaginary first
coefficients at the opposite frequency and annihilates the wrong frequency.
Arbitrary periodic inputs exercise the unique endpoint pair representation.

Exponent-embedding checks retain imaginary negative modes, attain the unit
norm bound on a singleton, and compose exponent changes at negative fractional
regularity. They exercise `FL^{3/8,2} → FL^{0,4/3}` with multiplier exponent four
and its exact reciprocal-weight norm constant, as well as an infinity-to-`l1`
embedding with two regularity units. The critical fractional reciprocal fails
at equality. The harmonic raw sequence is an actual element of `FL^{1,∞}` but
is not in `l1`, and coefficient uniqueness proves that its synthesized periodic
distribution has no alternative `l1` representation. Abstract periodic data
exercises the unique target-representation theorem.

Young checks cover `l^(4/3) × l^(4/3) → l2` and its exact bilinear operator
norm one. Negative and positive single modes test frequency addition and
imaginary amplitudes. Both `l∞ × l1` and `l1 × l∞` agree with the existing
convolution, and the `l1` output endpoint is checked. The harmonic coefficient
sequence is constructed in `l2` and proved not in `l1`; its self-convolution
still has absolute convergence at a negative output frequency. Cutoff convergence
is checked in the full infinity output norm, and a two-mode Hilbert example
has the expected coefficient two from two distinct summands. Arbitrary finite
supports exercise the non-Hilbert bound; an invalid output exponent is rejected.

Young-distribution checks realize the non-Hilbert constant-one estimate as an
actual distribution and recover the signed single-mode coefficients `-1` and
zero. Hilbert-input polynomial products converge with infinity output. The
infinity-input endpoint uses approximation in its finite opposite factor, and
both endpoint orders agree with the old Wiener product. Joint uniqueness,
arbitrary simultaneous approximations, changes of both input and output
exponents, and characterization among arbitrary periodic distributions are
checked explicitly.

Mixed-Young checks instantiate `α=1, β=2, γ=p₁=4, p₂=p₃=4/3`, exercise
convergence at all three levels, and construct the required intermediate
exponent. All six exponents equal to `1/2` test the full inequality below the
Banach range. Power transport from exponent `1/2` by power `1/4` has the exact
norm identity, and single-mode quasi-norms equal one. Unit modes attain the
mixed bound with distinct nesting exponents. A two-mode calculation gives the
middle sum five at output frequency one, distinguishing the mixed nesting
from the square of the ordinary convolution coefficient three.

Translation-energy checks recover the positive physical phase sign from an
imaginary negative-frequency mode translated by half a unit. They check
inverse translations and strong continuity for arbitrary `L²` classes, as well
as the almost-everywhere physical increment formula. A negative mode has
normalized squared increment energy four and physical interval energy eight.
Fractional examples check exact diagonalization without finiteness assumptions,
translation invariance, frequency reflection, zero energy for imaginary
constants, the amplitude factor four for a nonzero mode, and the physical
double-integral normalization.

Fractional spectral checks evaluate the model kernel at zero and both unit
displacements, prove integrability at regularities `1/4` and `3/4`, and check the
negative near-zero power at `3/4`. They verify positivity and order of the actual
integral constants, the exact `n=3, s=1/4` scaling and interval endpoints,
negative-frequency two-sided bounds, and positivity and finiteness of nonzero
weights. Arbitrary physical `L²` data exercises both energy bounds and the
`|n|^(2/3)` summability criterion. Imaginary negative modes exercise actual
fractional regularity at `s=3/4`.

Fractional identification checks exercise actual reconstruction at `s=3/4`,
unique representation at `s=1/2`, the exact weighted exponent `3/2`, both
physical norm bounds, and imaginary negative-frequency coefficient recovery.
An imaginary constant has weighted norm one although its physical seminorm
vanishes. The actual `L²` synthesis with coefficients `(1+|n|)^(-1)` fails
physical regularity at `s=1/2`, using the exact reciprocal summability threshold.

Boundary checks evaluate the exterior kernel at the midpoint of `[0,2]`,
its positive tail at distance four, and the boundary-weight mass at `s=1/4`.
They test nonintegrability at `s=1/2`, zero intrinsic energy alongside infinite
exterior interaction for constant data at that threshold, and exterior energy
eight for imaginary unit amplitude on `[0,1]`. Doubling the amplitude and
using length four gives energy 64. Further checks cover almost-everywhere
bounded data, almost-everywhere invariance, and the physical zero-extension
difference formula.

Hardy checks exercise positivity and contraction at `s=1/3`, exact loss of
contraction at `s=1/2`, the square-root coefficient at `s=1/4`, the adjustable
square bound for imaginary values, the numerical annular mass, exact row
normalization, triangle support and nonpositive columns. They check truncated
averaging and the contracting physical preestimate for arbitrary data, cutoff
finiteness even above half regularity, and exhaustion of the open interval.
Reflection is tested without any finiteness assumption. The final check derives
finite exterior interaction from interval `L²` and intrinsic fractional energy
alone, with no global measurability or boundedness hypothesis.

Zero-extension checks retain the factor two between exterior and full line
energy, recover energy 16 for imaginary unit interval data at `s=1/4`, and
verify infinite line energy for a constant zero extension at `s=1/2`. Line
translation energy has the same exact value. At a wrap crossing the nonzero
zero-extension pieces cancel for a periodic constant. The periodic comparison
and actual interval Fourier membership are exercised for arbitrary data.
A concrete ramp `f(x)=x` has unequal endpoint values, interval square
integrability, and proved fractional energy at most eight at `s=1/4`; the new
bridge yields its weighted Fourier square summability without periodicity.

A.9 checks evaluate the auxiliary exponent at `q=3/2`, recover an imaginary
negative-frequency coefficient through the continuous inclusion, and cover
targets above two and the Banach endpoint at higher regularity. The reciprocal
weight fails summability at equality in its threshold. Lowering half regularity
to a quarter on length four has constant two. Zero-regularity examples require
only `L²`, including target two and infinity. The actual nonperiodic ramp has
`ℓ^(3/2)` Fourier coefficients from quarter regularity; its independently
proved intrinsic half energy is at most four, giving `ℓ^(6/5)` coefficients
despite unequal endpoint values.

Intrinsic-bound checks preserve the nonzero size of an imaginary constant,
verify finite exterior and spectral constants below half, and evaluate the
vanishing Hardy gap at half. Arbitrary interval representatives exercise the
uniform exterior bound without global measurability. Nonnegative Parseval
retains the factor `1/2`. The explicit lower indices are `5/12` at `q=6/5`
and `1/4` at `q=3`. The actual nonperiodic ramp exercises both the subcritical
and half-regularity Fourier norm bounds in its own intrinsic size. The zero
case uses only `L²`, and an imaginary constant attains its infinity norm bound.

Dilation checks distinguish the inverse square-energy Jacobian from the
fractional exponent: at quarter regularity, dilation by four has factor one
half, while half energy is invariant under dilation by three. The kernel's
diagonal at regularity `-1/2` is checked separately. Period-one coefficient
scaling and period-four agreement with mathlib are checked, and an imaginary
negative-frequency wave on length four recovers its coefficient exactly.
A genuinely nonperiodic length-four ramp has proved half energy at most 16,
giving the subcritical target `3/2` and half target `6/5`. Additional checks
cover the vacuous zero-energy hypothesis, both arbitrary-length intrinsic norm
bounds, and the infinity normalization factor `1/2` at length four.

Restriction checks distinguish the real and extended kernels at zero while
verifying equality of their actual central energies. The two tails have exact
mass four at `s=1/4`; an imaginary constant has zero full displacement energy.
Periodic input at `s=3/4` exercises restriction and the reverse norm bound above
half. A nonzero imaginary negative mode verifies the square normalization.
The nonperiodic ramp exercises the two-sided bound below half. Further checks
cover bidirectional dilation finiteness, the arbitrary-length weighted criterion,
and unique weighted representation of the length-four ramp.

Intrinsic-space checks evaluate the exceptional diagonal, the length-four
square energy of an imaginary negative mode, both quotient reconstruction
directions, and the exact norm two of an imaginary constant on length four.
The constant has zero difference-quotient class. A nonperiodic ramp with proved
half energy defines an actual intrinsic class and maps continuously into
`ℓ^(6/5)`. Checks cover complex linearity, injectivity, full sequence norm
bounds, the `1/2` normalized `L²` inclusion factor, the quarter-to-`3/2` map,
negative-frequency coefficient signs, and exact almost-everywhere class equality.

Completeness checks infer the complete-space structure at half and above half
regularity on different interval lengths. The imaginary constant's self inner
product is exactly four on length four, while multiplication by `i` in the
first argument gives `-4i`. Checks exercise arbitrary simultaneous graph limits,
the full intrinsic convergence criterion, and Cauchy limits. A norm-summable
series of nonperiodic half-regularity ramps exists by completeness, and both
its Fourier coefficients and physical difference quotients commute with the sum.

Equivalence checks verify both inverse identities on different interval lengths,
explicit forward and inverse norm bounds, and original Fourier coefficients of
the nonperiodic length-four ramp. Its finite Fourier truncations converge in
the full quarter-regularity norm and in the difference-quotient `L²` norm.
Negative selected frequencies are retained, excluded positive frequencies are
zero, and finite support is dense. Additional checks cover continuous synthesis
above half, its exact raw coefficients, and the A.9 factorization through the
weighted equivalence.

Spectral-weight checks allow a constant weight with value two at zero, retain
the physical `π` scale at a negative frequency, and evaluate a fractional
scaled weight. They exercise signed monotonicity and tempered compatibility.
An imaginary negative scalar mode is shifted with the correct sign, including
at infinity. An asymmetric pair gives shifted energies 16 at `p=1`, 136 at
`p=2`, and 1216 at `p=3`, distinguishing the opposite component signs and the
source sum norm. Unit weights give an isometry; general weights retain both
comparison bounds. The actual tempered-distribution modulation identity is
also checked at a negative frequency.

The complementary-inverse examples check resonant modes at `p=1,3`, opposite
physical signs at the same frequency, the closed strip boundary with a nonzero
imaginary part, algebraic inversion at infinity, and negative resonant indices.
They also check shifted bounds, the explicit derivative bound, the original
free differential equation, and uniqueness from vanishing resonant coordinates.

The Lemma 6.4 examples check weighted Fourier-mode multiplication, Young's
infinity endpoint, shifted scalar bounds at `p=1,2`, the exact `c₂=2` constant,
and the physical signs and component exchange in `T_n`. They instantiate the
pair estimate at `p=1,2,3`, verify the same-shift squared estimate, and check
agreement with the original potential and derivative-domain inverse.

The Lemma 6.5 examples check both signed tail boundaries, deletion strictly
inside the cutoff, finite-exponent pair-tail convergence, closed and odd-radius
windows, and the weight gain for positive and negative centers. They cover the
conjugate-infinity reciprocal tail at resonance, the improved near-near norm,
the explicit Hilbert constant 260, the pair estimate at `p=1,3`, zero-strip
operator bounds, and the actual two-potential factorization.

The contraction checks cover unit-weight shift isometries at `p=1,3`, an
imaginary negative Fourier mode under a constant weight with `w(0)=2`,
nested tail norms, and compatibility of the actual operator square at a
negative resonance. They instantiate the simultaneous open-neighborhood
half bound at `p=1` and a quarter bound along negative resonances at `p=3`.
The zero-potential frequency bound also vanishes at the zero strip.

The Q-equation checks invert a nilpotent operator whose norm is at least four
through an arbitrary coordinate equivalence, and verify its transported
geometric series. They check the weighted derivative embedding at `p=1`,
the original domain potential at `p=3`, the source Q-solution formula at a
negative resonance, locally uniform existence and uniqueness at `p=3`,
and weighted/unweighted inverse compatibility. With zero potential, the
solution is exactly zero even at the central zero strip.

The Lemma 6.6 checks cover negative-frequency synthesis at `p=1`, two
independent amplitudes at the zero strip with `p=3`, and the exact domain
lift. The free matrix determinant is exactly `(λ-nπ)²` for arbitrary spectral
weights and finite Banach exponents. Checks recover its double root at a
negative resonance and exclude a nonreal free parameter from the original
periodic spectrum at `p=1`. They also instantiate nonzero eigenfunction
reconstruction and the locally uniform criterion on original potential space.

The Lemma 6.7 checks distinguish the bilinear pairing from a Hermitian one
using opposite imaginary Fourier modes at `p=3`. They check the vanishing
constant-potential diagonal at the zero strip, the signed denominator at a
negative resonance, the determinant's off-diagonal product sign at `p=1`,
and positive imaginary diagonals beyond every cutoff at `p=3` with the
actual half-size contraction.

Conjugation checks cover the infinity endpoint under a constant weight with
`w(0)=2`, negative imaginary Fourier modes, and nonconstant real/imaginary
type potentials with opposite frequencies and complex amplitudes at `p=1,3`.
They check real-axis diagonal reality for complex real-type components,
the minus sign in the imaginary-type off-diagonal identity, and conjugation
of a nonreal parameter on the closed strip boundary.

Parity checks recover distinct leading coefficients from asymmetric Fourier
modes at a negative resonance. For constant components `(a,b)` at the zero
resonance, the actual inverse fixes the potential-source vectors; thus
`b_n⁺=b` and `b_n⁻=a`. The asymmetric example `(2,i)` verifies the exact
source matrix `[[λ,-i],[-2,λ]]` at `p=1`, catching swapped names and basis
indices. Additional checks cover arbitrary unwanted even terms at `p=1`
and the convergent positive remainder series at a negative resonance with
`p=3`. The determinant comparison uses the same source coefficient labels.

Even-vector checks use a nonzero operator with square exactly half the identity
and an arbitrary continuous change of coordinates, obtaining the three-term
error constant `1/4`. They cover the empty partial sum on a trivial Banach
space, distinct exact source norms under `w(0)=2` at a negative resonance
with `p=3`, the unweighted positive-mode bound at `p=1`, and the four-term
error constant `1/8` at a negative resonance with `p=3`.

Analytic-coefficient checks cover removal of the two exact resonant modes at
`p=∞`, center normalization at `p=3`, and ambient analyticity at a nonreal
point on a negative strip boundary. They check operator-norm linearity of
the actual potential at `p=1`, spectral restriction of both off-diagonal joint
analyticity results at `p=3`, and an actual nonreal analytic diagonal at
arbitrarily large real centers. A final `p=1` check extracts one cutoff for
all signed distant strips together with exact source-coefficient agreement.

Diagonal-estimate checks locate a single reciprocal row at the signed index
`-6` with denominator `8`, and verify removal of the resonant contribution
at the conjugate infinity endpoint. Under a constant weight with `w(0)=2`,
the actual even-vector bound retains the smaller unweighted component norm.
Checks instantiate the row bounds at `p=1` and the exact reciprocal-sum
formula at `p=3/2`. The full-strip supremum is proved strictly positive for
an actual complex potential at arbitrarily distant positive real centers.

Diagonal-summability checks retain negative cutoff-boundary kernel modes and
complex phases, and exercise the low-kernel potential-tail contribution at a
negative resonance. They recover the decay powers `1/2` and `1` at `p=3/2`
and `p=3`, evaluate the Hilbert constant as `512`, and check an odd half-cutoff
under `w(0)=2`. The full locally uniform source inequality is instantiated
below two; a separate cubic-tail check establishes summability of the actual
supremum sequence above two.

Double-reciprocal checks use a complex inner mode and distinct signed kernel
frequencies, interchange asymmetric kernels below two, and test the near
identity at an odd negative cutoff. They instantiate the physical sum at a
negative resonance, the far decay powers `1/2` and `1`, and vanishing of a
near region for a potential mode below its cutoff. The explicit Hilbert
region constant is checked to be `4096`.

Off-diagonal Hölder checks use `w(0)=2`, a reflected negative shift, and a
nonzero complex weighted series term. Two nonconstant potential modes produce
an actual resonant second-iterate coefficient `6i/π²`, testing the physical
frequency signs and both reciprocal denominators. The absolute Hölder test
is instantiated at `p=1,q=∞`, and joint physical convergence is checked at a
nonreal spectral parameter. Actual negative and positive remainder bounds
are checked at `p=1` and `p=3`, together with a common cutoff for both
analytic remainder bounds on all signed full strips.

Off-diagonal summability checks exercise the shared far-region boundary without
double counting, a nonzero complex near-region term with both potential tails,
and vanishing of the entire near sum when only the outer potential has low
support. They preserve a reflected cutoff-boundary coefficient under `w(0)=2`,
check the odd cutoff `N=3`, and compute the actual supremum of a constant phase
over an unbounded strip. The explicit Hilbert constant is `393216`. The locally
uniform negative estimate is instantiated at `p=3/2` with decay `N^(-1/2)`;
at `p=3`, both actual power tails converge and the positive estimate has decay
`N^(-1)`, for every larger cutoff.

Refined-root checks evaluate the actual free determinant at a nonreal parameter
near a negative resonance, attain the scalar localization radius with purely
imaginary coefficients, and test the strict boundary comparison with nonreal
phases. A nonreal point tests the shifted Cauchy-disc inclusion. Two imaginary
roots and a nonzero diagonal slope exercise the squared-residual gap argument.
The full weighted coefficient bound is instantiated at `p=3/2` and `w(0)=2`;
the actual determinant circle comparison is tested below two and its root-gap
bound at `p=3`. A negative-resonance example checks the scalar zero criterion
against the original periodic spectrum.

Scalar counting checks compute a nonreal triple root and the zero-degree
monomial, then count a cubic with a double root at `i` and a simple root at
`-i`. Its contour integral is checked against total multiplicity three.
A complex perturbation of a square centered at `i` exercises Rouché's theorem.
The actual full-strip determinant count is instantiated at `p=3/2` with
`w(0)=2`; the actual free determinant has count two at a negative resonance.
At `p=3`, the two-root theorem is checked with complete strip zero detection,
exact analytic multiplicities, and the factor-six gap bound.

Displacement checks compute the exact Hilbert norm of unequal complex
amplitudes at a negative resonance, and an actual nonreal determinant root
at `p=3`. A concrete small-amplitude budget is strictly below one squared
root displacement for every larger cutoff. The counterexample is instantiated
with a large proposed constant, a tiny open ball, and an arbitrary lower
frequency threshold. Aligned imaginary coefficients test the power estimate
at `P=3` and its endpoint `P=1`.

Corrected summation checks compute a weighted leading sum of `52` from unequal
complex amplitudes at the negative cutoff-boundary resonance, preserving
`w(0)=2`. Injective sampling is checked with the exact doubled cutoff. Two
nonreal test roots contribute `5` to a two-sided displacement sum at a negative
boundary. The explicit Hilbert constant and the vanishing zero-potential budget
are checked. At `p=3/2`, actual root tails use the decay `N^(-1/2)` with every
larger cutoff and a nonnormalized weight; at `p=3`, the summable sequences
retain the exact analytic zero multiplicities.

Weighted gap checks compute the exact sum `36` from unequal imaginary roots
at a negative cutoff-boundary mode with `w(0)=2`, then remove it by raising
the cutoff. Coincident roots give zero gap; exchanging root order preserves
the tail below exponent two. The explicit Hilbert constant, zero-potential
budget, and a four-term estimate above exponent two are checked. Actual
`p=3/2` gap tails retain `N^(-1/2)` and the leading Fourier tail, while the
`p=3` test retains exact analytic orders and both simultaneous quantitative
power tails for all larger cutoffs.

Periodic bridge checks detect the original spectrum through the actual
complex single-mode determinant at a negative resonance with `w(0)=2` and
`p=3`. Repeated and distinct pairs have spectral algebraic multiplicities two
and one respectively. A nonreal gap checks the squared-modulus power identity,
and the free intrinsic gap vanishes at a negative cutoff boundary below
exponent two. At `p=3/2`, one neighborhood identifies analytic and spectral
multiplicities and the intrinsic gap budget retains `N^(-1/2)`; at `p=3`, the
actual periodic pair retains both simultaneous quantitative tails.

Midpoint/boundary checks evaluate an imaginary displacement at a negative
cutoff boundary and recover global `ℓp` membership for arbitrary finitely
many low modes. Complex midpoint inequalities cover `P=1` and `P=3`; the
actual midpoint half-budget is instantiated at `p=3/2` with `w(0)=2`.
The period-one potential map preserves the normalized even-frequency
reflection formula. Both ordinary source branches have full displacement
membership and quantitative tails below two, while the free branches retain
negative indices. The original physical test retains both square summability
and the unique high-disc classical eigenvalue characterization.

Auxiliary checks compute the exact phase of both signed free boundary modes
at a negative resonance, and verify complementarity at negative fractional
Sobolev regularity below exponent two. A nonzero constant Neumann-reflected
potential `(1,-1)` has an actual auxiliary D eigenvector with eigenvalue `i`.
The unrestricted operator conjugation is checked below two; both spectra
are discrete above two. The starred source branches retain global `ℓp`
displacements, actual unique high-disc spectral values, and every quantitative
tail at `p=3/2`. Both free branches retain a negative index.

Auxiliary root-space checks cover level-three conjugation, finite dimension,
stabilization, and actual multiplicity one at a negative free index. The source
period-one API retains one open convex neighborhood for both conditions and
every larger cutoff, with central count `2N+1` and simple high-disc values at
`p=3`. A nonzero constant potential `(π,-π)` gives a genuine auxiliary
Dirichlet Jordan chain at zero: its initial vector lies in level two but not
level one. The check verifies both actual pencil equations and domain conditions.

Physical auxiliary checks verify both reflected phase signs at `x=3/2`, exact
retention of both original endpoints, the literal source D*/N* endpoint
equations, and unique weighted representatives for arbitrary original H¹ input.
For the nonzero physical potential `(1,-1)`, constant auxiliary eigenfunctions
have eigenvalues `i` and `-i` for D* and N*, respectively. The same `i` belongs
to the actual auxiliary coefficient spectrum. The potential's zeroth Fourier
coefficients are checked directly from the Neumann extension integrals, and
the original differential equation transfers through the actual Sobolev extension.

Physical auxiliary operator checks verify the exact norm `√2` of the constant
function `(1,i)`, completeness, both physical L² phase isometries, and the two
explicit domain-isomorphism bounds. At the nonzero potential `(1,-1)`, the
actual L² operator has eigenvalue `i`, and the original pencil is proved
noninjective there. Both inverse identities hold for arbitrary physical data
and potentials. The checks also cover nonempty resolvent sets, compactness,
closedness, density, and exact original-function membership in the unbounded
domain.

Physical auxiliary multiplicity checks cover finite-chain conjugation, the
recognition of a nontrivial two-step chain from actual domain-pencil equations,
full-root-space stabilization and finite dimension, and containment in the
original unbounded domain. Physical and actual coefficient multiplicities agree,
and negative free indices are simple. The public physical asymptotic API retains
one open convex neighborhood for both conditions, actual central counts at
every larger cutoff, analytic simple branches, full square-summability, and
all quantitative displacement tails.

Auxiliary reality checks cover negative odd half coefficients, nonconstant
complex-amplitude real-type inputs at `p=3`, both signed source extensions,
and actual spectral reality at `p=1`. The source period-one theorem uses its
actual pair topology and Neumann potential extension. Physical checks allow
a non-real exceptional value at an interior singleton and place `i` in the
actual closed physical operator's resolvent for arbitrary real-type L² data.

## Next milestones

1. Resolve the printed general-`p` central height beyond the proved Hilbert case.
2. Verify bounded source period-one auxiliary eigenfunction extension maps.
   Source-extension real-type compatibility and Proposition 5.2(iv) are now
   proved for source coefficient and original physical L² potentials. The
   physical endpoint domains, normed isomorphisms, closed densely defined L² operators, compact resolvents,
   actual generalized multiplicities, counts, and uniform starred asymptotics
   are now proved. All four coefficient and physical L² Corollary 6.2
   displacement conclusions hold, together with the midpoint consequence.
   Corrected Propositions 6.1/6.3 now hold for the original periodic eigenvalue
   pairs and intrinsic squared gaps, with exact spectral algebraic multiplicities.
   Lemma 6.7 is proved with `φ*=±φ` retained for
   both conjugation conclusions. Lemma 6.6 is proved
   for the original periodic spectrum, including locally uniform thresholds. Lemmas 6.4 and 6.5 are proved for all
   finite Banach exponents, including the source's `c₂=2` in Lemma 6.4.
   A.9's intrinsic Hilbert space and continuous
   subcritical weighted identification are implemented on every positive interval,
   as are the finite Fourier approximation and the zero/half coefficient bounds.
   Appendix B.2, its periodic product in A.7, and the displayed B.3 inequality
   are proved.
3. Continue to the Chapter 2 discriminant, product, and action-coordinate
   prerequisites, then the remaining nonlinear Fourier/Birkhoff main results.
   Both finite and infinity source pair norms and their sharp comparisons are
   complete.

Classical Birkhoff prerequisites and the main dissertation theorems remain
unimplemented. The printed general-`p` spectral height remains open, and
the remaining bounded auxiliary eigenfunction extension and Chapter 2 nonlinear
coordinate construction remain incomplete.
