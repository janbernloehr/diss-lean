import NLS.Articles.KdVConvexity.CanonicalMomentPreparation
import NLS.KdV.HillHminusOneFinitePeriodExtensions
import NLS.KdV.HillHminusOneJointGapSquares
import NLS.KdV.HillHminusOneJointGapPeriodGerms
import NLS.ComplexAnalysis.CompactCoordinateUniqueness
import NLS.KdV.HillHminusOneAllGapSquares
import NLS.KdV.HillHminusOneAllRealPeriods
import NLS.KdV.HillHminusOneRealGapContours
import NLS.KdV.HillHminusOneGlobalRealLabels
import NLS.KdV.HillHminusOneCubicSign
import NLS.KdV.HillHminusOnePhysicalHighCuts
import NLS.ComplexAnalysis.PhysicalCutCubicSign
import NLS.KdV.HillHminusOneMomentReality
import NLS.Articles.KdVConvexity.CoordinateActionExtension
import NLS.KdV.HillHminusOneArnoldActionComparison
import NLS.KdV.HillHminusOneMomentRadius
import NLS.KdV.HillHminusOneFreeSquareComparison
import NLS.KdV.HillHminusOneSourcePrimitive
import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.SequenceSpaces.PeriodOneMiuraCharts
import NLS.SequenceSpaces.PeriodOneMiuraRegularity
import NLS.KdV.ClassicalTraceAsymptotics
import NLS.KdV.ClassicalBranchPrimitive
import NLS.KdV.ClassicalContourMoments
import NLS.KdV.ClassicalHighGapFamilies
import NLS.KdV.ClassicalHillMomentReality
import NLS.KdV.ClassicalHillHighEndpointNormalization
import NLS.KdV.ClassicalHillSquaredPrimitiveMatching
import NLS.KdV.ClassicalHillWholeGapSquares
import NLS.KdV.ClassicalHillGapCutRoots
import NLS.KdV.ClassicalHillCubicGapBounds
import NLS.KdV.ClassicalL2PrimitiveAgreement
import NLS.KdV.ClassicalL2ContourAgreement
import NLS.KdV.HillL2DiscAsymptotics
import NLS.KdV.HillL2GapSquareFamilies
import NLS.KdV.HillL2HighMomentFamilies
import NLS.KdV.HillL2ArnoldActionComparison
import NLS.KdV.ClassicalHillGapQuotientAsymptotics
import NLS.KdV.ClassicalHillArnoldActionComparison
import NLS.KdV.ActionHamiltonianFiniteGap
import NLS.Articles.KdVConvexity.LocalConsequences
import NLS.Articles.KdVConvexity.BaseContourSeries
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let namespaces := #[`NLS.Articles.KdVConvexity, `NLS.KdV]
  let additional := #[``NLS.ZakharovShabat.norm_continuousPotentialL2Class_le_two_norm,
    ``NLS.ZakharovShabat.continuousPotentialL2CLM,
    ``NLS.ZakharovShabat.continuousPotentialL2CLM_apply,
    ``NLS.ZakharovShabat.classicalSolution_injective_initial,
    ``NLS.ZakharovShabat.classicalSolution_eq_zero_imp_initial_eq_zero,
    ``NLS.ComplexAnalysis.twoZeroQuotient,
    ``NLS.ComplexAnalysis.dslope_zero_at_second_zero,
    ``NLS.ComplexAnalysis.twoZeroQuotient_factor,
    ``NLS.ComplexAnalysis.analyticOnNhd_twoZeroQuotient,
    ``NLS.ComplexAnalysis.twoZeroQuotient_ne_zero,
    ``NLS.ComplexAnalysis.norm_twoZeroQuotient_le,
    ``NLS.ComplexAnalysis.norm_two_root_quotient_sub_le_on_disc,
    ``NLS.ComplexAnalysis.analyticOnNhd_continuous_squareRoot,
    ``NLS.ComplexAnalysis.exists_analytic_squareRoot_on_ball,
    ``NLS.ComplexAnalysis.endpointRoot,
    ``NLS.ComplexAnalysis.midpoint_mem_complex_segment,
    ``NLS.ComplexAnalysis.endpointRoot_sq,
    ``NLS.ComplexAnalysis.analyticOnNhd_endpointRoot,
    ``NLS.ComplexAnalysis.exists_analytic_squareRoot_on_two_zero_cut,
    ``NLS.ComplexAnalysis.norm_sq_sub_sq_of_small_sphere,
    ``NLS.ComplexAnalysis.square_circleMap_sub_linear,
    ``NLS.ComplexAnalysis.squaredCirclePath_contDiffOn,
    ``NLS.ComplexAnalysis.squaredCircleHomotopy_annulus,
    ``NLS.ComplexAnalysis.circleIntegral_square_pullback_eq_energy_circle,
    ``NLS.ComplexAnalysis.circleIntegral_eq_of_analytic_cut_nestedCircles]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let additionalModules := #[
    `NLS.ComplexAnalysis.RealCutWeightedPowerIntegral,
    `NLS.ComplexAnalysis.ScalarCoordinateUniqueness,
    `NLS.ComplexAnalysis.NearbyCircleHomotopy,

    `NLS.ComplexAnalysis.ContinuousMapAnalytic,
    `NLS.ComplexAnalysis.ContinuousMapSuperposition,
    `NLS.ComplexAnalysis.ContinuousMapAnalyticInverse,
    `NLS.ComplexAnalysis.ParametricCircleIntegralHigher,
    `NLS.ComplexAnalysis.CompactCoordinateExtension,
    `NLS.ComplexAnalysis.CompactCoordinateJointExtension,
    `NLS.ComplexAnalysis.CompactCoordinateContinuation,
    `NLS.ComplexAnalysis.CoshSquareRegularity,
    `NLS.ComplexAnalysis.CompactCoordinateUniqueness,

    `NLS.ComplexAnalysis.UpperLogarithmBoundary,
    `NLS.ComplexAnalysis.ParametricUpperLogarithmBoundary,
    `NLS.ComplexAnalysis.RealSimpleZeroSigns,
    `NLS.ComplexAnalysis.ClosedUpperExtension,
    `NLS.ComplexAnalysis.BoundaryAnalyticCoordinate,
    `NLS.ComplexAnalysis.CoshSquareLocalCoordinate,

    `NLS.ComplexAnalysis.TraceRootPrimitive,
    `NLS.ComplexAnalysis.UpperTracePrimitiveExtension,
    `NLS.ComplexAnalysis.CoshSquareCoordinate,
    `NLS.ComplexAnalysis.RealCoshTrace,

    `NLS.ComplexAnalysis.RealGapDiscIsolation,
    `NLS.ComplexAnalysis.NearImaginarySquare,
    `NLS.ComplexAnalysis.PhysicalCutCubicGeometry,

    `NLS.ComplexAnalysis.RealDiameterDisc,
    `NLS.SequenceSpaces.OrderedOneSidedEnumeration,
    `NLS.SequenceSpaces.OrderedFiniteContinuity,
    `NLS.ComplexAnalysis.PositiveRealPart,
    `NLS.ComplexAnalysis.RealCutConjugation,
    `NLS.ComplexAnalysis.RealGapEllipse,
    `NLS.ComplexAnalysis.RealGapEllipseHomotopy,
    `NLS.ComplexAnalysis.RealGapEllipseIntegral,
    `NLS.ComplexAnalysis.RealGapEllipseLimit,
    `NLS.ComplexAnalysis.RealCutCircleIntegral,
    `NLS.ComplexAnalysis.BoundedPuncturedCircleIntegral,
    `NLS.ComplexAnalysis.SignedSquareBoundary,
    `NLS.ComplexAnalysis.PhysicalCutCubicSign,
`NLS.ComplexAnalysis.ClosedZeroPersistence,`NLS.SequenceSpaces.PeriodOneHminusOneRealDensity,`NLS.Fourier.ContinuousConjugation,`NLS.ComplexAnalysis.TracePrimitiveReflection,
    `NLS.ComplexAnalysis.HolomorphicCircleIntegral,`NLS.ComplexAnalysis.FDerivCauchyFormula,`NLS.ComplexAnalysis.AnalyticLineLimit,`NLS.ComplexAnalysis.AnalyticLineDerivative,`NLS.ComplexAnalysis.AnalyticLineDerivativeLinear,`NLS.ComplexAnalysis.AnalyticLineDerivativeBounds,`NLS.ComplexAnalysis.AnalyticLineRemainder,`NLS.ComplexAnalysis.AnalyticLineFrechet,`NLS.ComplexAnalysis.FDerivAnalyticLine,`NLS.ComplexAnalysis.BanachHolomorphicAnalytic,`NLS.SequenceSpaces.SignChange,`NLS.SequenceSpaces.FiniteCenterBall,`NLS.SequenceSpaces.MixedSquare,`NLS.ComplexAnalysis.QuadraticLineRoot,`NLS.SequenceSpaces.FiniteMixedSquareLineLift,`NLS.SequenceSpaces.AnalyticSequenceSlice,`NLS.SequenceSpaces.ComplexSignInvariance,`NLS.ComplexAnalysis.OpenMapDescent,`NLS.SequenceSpaces.TailSquareDescent,`NLS.SequenceSpaces.TailSquareDescentHeadAnalytic,`NLS.SequenceSpaces.TailSquareDescentCoordinateAnalytic,`NLS.SequenceSpaces.TailSquareDescentAnalyticSlice,`NLS.SequenceSpaces.TailSquareDescentFiniteLine,`NLS.SequenceSpaces.TailSquareDescentAnalyticLine,`NLS.SequenceSpaces.TailSquareDescentFrechet,`NLS.SequenceSpaces.TailSquareDescentAnalytic,`NLS.SequenceSpaces.ScalarTailSquareDescent,`NLS.SequenceSpaces.RealActionRotation,`NLS.SequenceSpaces.ComplexActionStationarity,`NLS.SequenceSpaces.ActionSplitDirection,`NLS.SequenceSpaces.PairCoordinateDensity,`NLS.SequenceSpaces.TailActionStationarity,`NLS.SequenceSpaces.TailActionInvariance,`NLS.SequenceSpaces.TailSumCoordinates,`NLS.SequenceSpaces.HeadActionSection,`NLS.SequenceSpaces.LocalTailSumDescent,`NLS.SequenceSpaces.HeadRotationStationarity,`NLS.SequenceSpaces.HeadRotationDescent,`NLS.SequenceSpaces.HeadActionPath,`NLS.SequenceSpaces.HeadActionPathAnalytic,`NLS.SequenceSpaces.HeadActionPathNeighborhood,`NLS.SequenceSpaces.HeadActionTangent,`NLS.SequenceSpaces.HeadActionCurveInvariance,`NLS.SequenceSpaces.LocalHeadActionDescent,`NLS.SequenceSpaces.LocalScalarActionDescent,`NLS.SequenceSpaces.NonzeroFiniteCenter,`NLS.SequenceSpaces.NonnegativeActionIdentity,`NLS.SequenceSpaces.NonnegativeActionOverlap,`NLS.SequenceSpaces.NonnegativeActionGluing,`NLS.SequenceSpaces.RealActionPairLifting,`NLS.SequenceSpaces.RealActionLifting,`NLS.SequenceSpaces.LocalScalarActionFamilyDescent,`NLS.SequenceSpaces.RealScalarActionFamilyDescent,`NLS.SequenceSpaces.ScalarActionFamilyGluing,`NLS.SequenceSpaces.GlobalScalarActionFamilyDescent,`NLS.SequenceSpaces.WeightedScalarActionFamilyDescent,
    `NLS.ComplexAnalysis.QuadraticClusterCount,
    `NLS.ComplexAnalysis.ShiftedSquareRootBounds,
    `NLS.MKdV.MiuraClassicalSolution,
    `NLS.MKdV.SobolevMiuraPotential,
    `NLS.FunctionalAnalysis.LinearVolterraFlow,
    `NLS.MKdV.QuasiHillDiscriminant,
    `NLS.MKdV.MiuraBoundaryTransfer,
    `NLS.ZakharovShabat.ClassicalVolterraTrace,
    `NLS.MKdV.QuasiHillZSComparison,
    `NLS.MKdV.QuasiHillJointAnalytic,
    `NLS.ComplexAnalysis.SourceDiscriminantPrimitive,
    `NLS.ZakharovShabat.ContinuousPotentialSource,
    `NLS.MKdV.QuasiHillSourcePrimitive,
    `NLS.DifferentialPolynomial.UngradedIntegrationByParts,
    `NLS.DifferentialPolynomial.PowerSeriesDerivation,
    `NLS.DifferentialPolynomial.DifferentialRiccati,
    `NLS.DifferentialPolynomial.RiccatiResolvent,
    `NLS.DifferentialPolynomial.LogarithmicDerivative,
    `NLS.DifferentialPolynomial.MiuraRiccati,
    `NLS.DifferentialPolynomial.ConstructedRiccatiResolvent,
    `NLS.DifferentialPolynomial.RiccatiResolventNaturality,
    `NLS.FunctionalAnalysis.PeriodicIntegrationByParts,
    `NLS.ZakharovShabat.ClassicalNLSHamiltonians,
    `NLS.DifferentialPolynomial.PeriodicEvaluation,
    `NLS.DifferentialPolynomial.MultiJet,
    `NLS.ZakharovShabat.SobolevHierarchySymmetries,
    `NLS.MKdV.HierarchyRestriction,
    `NLS.DifferentialPolynomial.RiccatiResolventParity,
    `NLS.ZakharovShabat.NLSRiccatiResolvent,
    `NLS.MKdV.MiuraHierarchyHamiltonians,
    `NLS.DifferentialPolynomial.PolynomialVariation,
    `NLS.DifferentialPolynomial.AlgebraicPolynomialVariation,
    `NLS.DifferentialPolynomial.EulerLagrange,
    `NLS.DifferentialPolynomial.IndependentJetVariation,
    `NLS.DifferentialPolynomial.RiccatiResolventVariation,
    `NLS.ZakharovShabat.NLSRiccatiResolventVariation,
    `NLS.FunctionalAnalysis.UnitIntervalMean,
    `NLS.DifferentialPolynomial.SmoothVariation,
    `NLS.ZakharovShabat.ClassicalNLSHierarchyVariation,
    `NLS.DifferentialPolynomial.EulerScalar,
    `NLS.Fourier.PeriodicVariationalUniqueness,
    `NLS.ZakharovShabat.NLSRiccatiResolventGradient,
    `NLS.MKdV.HierarchyGradientRecurrence,
    `NLS.MKdV.MiuraHierarchyFlowRestriction,
    `NLS.DifferentialPolynomial.EulerOrderBounds,
    `NLS.ZakharovShabat.SobolevPolynomialL2,
    `NLS.Fourier.CircleUnitCoefficients,
    `NLS.ZakharovShabat.SobolevPolynomialVariation,
    `NLS.ZakharovShabat.SobolevSourceCotangent,
    `NLS.ZakharovShabat.SobolevSmoothFirstVariation,
    `NLS.MKdV.SobolevMiuraHillHamiltonian,
    `NLS.MKdV.MiuraHillRiccatiRemainder,
    `NLS.Fourier.CircleBilinearMean,
    `NLS.ZakharovShabat.SobolevPolynomialEndpointMean,
    `NLS.ZakharovShabat.SobolevScalarSmoothDensity,
    `NLS.MKdV.NativeMiuraHillHamiltonian,
    `NLS.MKdV.QuasiHillPhysicalEquation,
    `NLS.MKdV.QuasiHillPhysicalUniqueness,
    `NLS.MKdV.PhysicalHillDiscriminant,
    `NLS.MKdV.MiuraHillHamiltonianTrace,
    `NLS.MKdV.MiuraHillSpectralBridge,
    `NLS.KdV.HillNLSPrimitivePathComparison,
    `NLS.MKdV.MiuraHillPrimitiveComparison,
    `NLS.MKdV.QuasiHillPrimitiveComparison,
    `NLS.MKdV.SobolevQuasiHill,
    `NLS.MKdV.SobolevMiuraPrimitive,
    `NLS.MKdV.MiuraL2HillDiscriminant,
    `NLS.SequenceSpaces.PeriodOneHminusOneDensity,`NLS.ComplexAnalysis.AnalyticUnitDerivativeInverse,
    `NLS.ComplexAnalysis.AnalyticOpenInverse,
    `NLS.ComplexAnalysis.SmallQuadraticInverse,
    `NLS.SequenceSpaces.PeriodOneMassResolvent,
    `NLS.SequenceSpaces.PeriodOneMiuraQuadratic,
    `NLS.SequenceSpaces.PeriodOneMiuraCharts,
    `NLS.SequenceSpaces.PeriodOneMiuraRegularity,
    `NLS.SequenceSpaces.PeriodOneMiuraShift,
    `NLS.ComplexAnalysis.EntireEvenSquareDescent,
    `NLS.ComplexAnalysis.AnalyticLocalLipschitz,
    `NLS.ComplexAnalysis.NormalizedSquareRootBounds,
    `NLS.ComplexAnalysis.LogarithmStripNormalization,
    `NLS.ComplexAnalysis.QuadraticRootContourPeriod,
    `NLS.ComplexAnalysis.TracePrimitiveContinuation,
    `NLS.ComplexAnalysis.TracePrimitiveMoments,
    `NLS.ComplexAnalysis.TracePrimitiveFunctoriality,
    `NLS.ComplexAnalysis.TwoZeroOrderComparison,
    `NLS.ComplexAnalysis.ZeroCountHomotopy,
    `NLS.FunctionalAnalysis.AbsoluteContinuityTranslation,
    `NLS.FunctionalAnalysis.LinearVolterraLinearity,
    `NLS.FunctionalAnalysis.TwoDimensionalDeterminant,
    `NLS.SequenceSpaces.WeightedInsertion]
  let mut checked : Nat := 0
  let env ← getEnv
  for mod in additionalModules do
    unless env.header.moduleNames.contains mod do
      throwError "Required audit module is not imported: {mod}"
  for (name, _) in env.constants do
    let fromSharedModule := (env.getModuleIdxFor? name).any
      (fun idx => additionalModules.contains env.header.moduleNames[idx.toNat]!)
    if namespaces.any (fun ns => ns.isPrefixOf name) || additional.contains name || fromSharedModule then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      logInfo m!"{name}: {axioms}"
      checked := checked + 1
  if checked == 0 then
    throwError "No article or shared KdV declarations found"
  logInfo m!"Transitive axiom audit passed for {checked} article/shared KdV declarations."
