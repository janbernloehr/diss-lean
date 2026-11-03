import NLS.FunctionalAnalysis.UnitCurveIntegral
import NLS.ComplexAnalysis.ScalarStateMass
import NLS.ZakharovShabat.L2SolutionNonvanishing
import NLS.KdV.HillL2StateCurve
import NLS.KdV.HillL2GreenIdentity
import NLS.KdV.HillDirichletReality
import NLS.KdV.HillStateMonodromy
import NLS.KdV.HillDirichletBands
import NLS.SequenceSpaces.SpectralWeightProduct
import NLS.SequenceSpaces.SpectralWeightCeilingCutoff
import NLS.SequenceSpaces.QuadraticCutoffRounding
import NLS.KdV.HillWeightedActionHead
import NLS.KdV.HillWeightedActionEstimate
import NLS.Articles.KdVEstimates.WeightedActionEstimate
import NLS.KdV.HillL2DirichletCharacteristic
import NLS.KdV.HillUniformActionGapBound
import NLS.SequenceSpaces.NonnegativeSeriesCauchySchwarz
import NLS.SequenceSpaces.WeightedSquareSums
import NLS.SequenceSpaces.QuadraticSeparationTail
import NLS.ComplexAnalysis.ProductExponentialBound
import NLS.SequenceSpaces.WeightedCutoffPowers
import NLS.SequenceSpaces.SpectralWeightFixedShift
import NLS.KdV.HillCriticalProductBounds
import NLS.KdV.HillWeightedCriticalTail
import NLS.ComplexAnalysis.RealCriticalProducts
import NLS.SequenceSpaces.PositiveQuotientProducts
import NLS.ComplexAnalysis.RealGapArcsineIntegral
import NLS.KdV.HillEnergyChiPositivity
import NLS.KdV.HillLowCriticalProductBound
import NLS.KdV.HillChiActionFormula
import NLS.ComplexAnalysis.EndpointCriticalRatioBounds
import NLS.SequenceSpaces.NaturalSquareSeparation
import NLS.KdV.HillEnergyLogarithmicProduct
import NLS.KdV.HillOmittedEnergyCriticalProduct
import NLS.KdV.HillHighCriticalFactorBounds
import NLS.KdV.HillCriticalCentralCensus
import NLS.KdV.HillSignedCriticalFrequencies
import NLS.KdV.HillEnergyCriticalProduct
import NLS.KdV.HillCriticalEnergyZeros
import NLS.ComplexAnalysis.DerivativeSquarePullbackOrder
import NLS.KdV.HillEnergyPolynomialLimits
import NLS.KdV.HillGapCriticalPoints
import NLS.KdV.HillCriticalFrequencyBridge
import NLS.Articles.KdVEstimates.ArnoldIntegerEstimates
import NLS.ComplexAnalysis.RealCutConnected
import NLS.ComplexAnalysis.RealEndpointRootSigns
import NLS.KdV.HillEnergyRootIdentification
import NLS.ZakharovShabat.PeriodicEndpointCandidates
import NLS.KdV.HillEnergyEndpointLabeling
import NLS.KdV.HillEnergyRadicandProduct
import NLS.SequenceSpaces.IntegerSymmetricSums
import NLS.ComplexAnalysis.RealSquareRootCensus
import NLS.KdV.HillCentralEnergyLabeling
import NLS.ComplexAnalysis.AnalyticSquarePullback
import NLS.KdV.HillSignedEnergyLabels
import NLS.KdV.HillEnergyRootAnalytic
import NLS.ComplexAnalysis.ComplexSquareRootShift
import NLS.KdV.HillEnergyFrequencyBounds
import NLS.ComplexAnalysis.EndpointRootBounds
import NLS.KdV.HillCanonicalEnergyRootProduct
import NLS.KdV.HillPhysicalIntegerActions
import NLS.Articles.KdVEstimates.PhysicalIntegerEstimates
import NLS.KdV.HillActionSquareBound
import NLS.KdV.HillNativeIntegerLower
import NLS.KdV.HillHamiltonianNormBounds
import NLS.KdV.HillHamiltonianConvolutionBounds
import NLS.KdV.HillForwardSobolevBound
import NLS.Articles.KdVEstimates.IntegerEstimates
import NLS.KdV.HillLowerSobolevTrace
import NLS.SequenceSpaces.TriangularHierarchyBounds
import NLS.KdV.HillInverseSobolevBound
import NLS.Articles.KdVEstimates.InverseIntegerEstimate
import NLS.KdV.HillGlobalMomentBounds
import NLS.KdV.HillIntegerActionMoments
import NLS.KdV.HillSummedMomentComparison
import NLS.KdV.HillUniformMomentComparison
import NLS.KdV.HillIntegerSobolev
import NLS.KdV.HillSobolevTraceFamily
import NLS.KdV.HillSobolevHierarchyTrace
import NLS.ComplexAnalysis.LaurentContourCoefficient
import NLS.KdV.HillHierarchyPhaseModel
import NLS.KdV.HillL2HierarchySquareAsymptotics
import NLS.KdV.HillSmoothHierarchyTraceLimit
import NLS.KdV.HillSmoothHierarchyTrace
import NLS.DifferentialPolynomial.JetMajorants
import NLS.DifferentialPolynomial.ScalarInterpolationExponents
import NLS.KdV.HillSobolevHierarchy
import NLS.KdV.HillHamiltonianMonomials
import NLS.KdV.HillMonomialInterpolation
import NLS.KdV.HillHamiltonianAbsorption
import NLS.KdV.HillHamiltonianCoercivity
import NLS.DifferentialPolynomial.WeightedJetReduction
import NLS.KdV.HillRiccatiRemainder
import NLS.KdV.HillHamiltonianReduction
import NLS.KdV.HillHierarchyTraceCoefficient
import NLS.KdV.HillHierarchyReality
import NLS.KdV.HillSecondHamiltonian
import NLS.DifferentialPolynomial.PowerSeriesDerivation
import NLS.DifferentialPolynomial.DifferentialRiccati
import NLS.DifferentialPolynomial.LogarithmicDerivative
import NLS.DifferentialPolynomial.ScalarRiccatiLogarithm
import NLS.KdV.HillRiccatiHierarchy
import NLS.KdV.HillHierarchyPhase
import NLS.KdV.HillHierarchyMomentContinuity
import NLS.KdV.HillSobolevEnergy
import NLS.KdV.HillH1EnergyTrace
import NLS.ComplexAnalysis.WeightedSquareRemainder
import NLS.ComplexAnalysis.EnergyContourCoefficient
import NLS.KdV.HillL2UpperEnergySquareAsymptotics
import NLS.KdV.HillL2EnergySquareCircleAsymptotics
import NLS.KdV.HillSmoothEnergyTraceLimit
import NLS.KdV.HillHighMomentSigns
import NLS.KdV.HillSmoothEnergyTrace
import NLS.KdV.HillFinitePhysicalPotential
import NLS.KdV.HillRealWeightedTruncation
import NLS.KdV.HillL2QuadraticTrace
import NLS.SequenceSpaces.LocalSeriesContinuity
import NLS.KdV.HillActionTailBudget
import NLS.KdV.HillLocallyUniformActionTails
import NLS.KdV.HillWeightedActionContinuity
import NLS.KdV.HillRealActionContinuity
import NLS.ComplexAnalysis.LaurentSquareRemainder
import NLS.ComplexAnalysis.UpperCircleReflection
import NLS.ComplexAnalysis.QuadraticContourCoefficient
import NLS.ComplexAnalysis.NonnegativeComplexSeries
import NLS.KdV.HillContinuousReality
import NLS.KdV.HillFreeCircleGeometry
import NLS.KdV.HillFreeTraceContour
import NLS.KdV.HillL2UpperSquareAsymptotics
import NLS.KdV.HillL2SquareCircleAsymptotics
import NLS.KdV.HillSmoothQuadraticTraceLimit
import NLS.KdV.HillSmoothQuadraticTrace
import NLS.ComplexAnalysis.LocalSinhComparison
import NLS.ComplexAnalysis.ContinuousIntervalBranch
import NLS.ComplexAnalysis.WeightedCoshInverse
import NLS.ComplexAnalysis.ImaginaryCoshInverse
import NLS.ComplexAnalysis.ConnectedPhaseControl
import NLS.KdV.HillL2BandPhase
import NLS.ZakharovShabat.FreeCosineZeroAudit
import NLS.ZakharovShabat.NLSHamiltonianPhasePolynomial
import NLS.KdV.HillL2BandAnchors
import NLS.KdV.HillFreeUpperArcs
import NLS.KdV.HillL2UpperArcAsymptotics
import NLS.ComplexAnalysis.UnimodularWeightedTraceError
import NLS.ZakharovShabat.ClassicalWeightedResidualStability
import NLS.ZakharovShabat.NLSWKBCarrierWeightedBounds
import NLS.ZakharovShabat.NLSWKBComparison
import NLS.ZakharovShabat.NLSWKBWeightedComparison
import NLS.ZakharovShabat.NLSHamiltonianDiscriminantAsymptotics
import NLS.ZakharovShabat.NLSHamiltonianWeightedAsymptotics
import NLS.KdV.RiccatiEnergy
import NLS.KdV.ClassicalTraceAsymptotics
import NLS.KdV.ClassicalWeightedTraceAsymptotics
import NLS.ComplexAnalysis.RealCenteredHoleGeometry
import NLS.KdV.HillFiniteBandCover
import NLS.KdV.HillOuterTraceGeometry
import NLS.ComplexAnalysis.FiniteCircleHoleDecomposition
import NLS.KdV.HillOuterTraceDomain
import NLS.KdV.HillFiniteTraceContour
import NLS.KdV.HillOuterTraceExhaustion
import NLS.KdV.HillOuterTraceLimit
import NLS.KdV.FreeHill
import NLS.KdV.HillComplement
import NLS.KdV.HillReduction
import NLS.KdV.HillSobolev
import NLS.KdV.HillPhysical
import NLS.KdV.HillAnalytic
import NLS.KdV.HillLocalization
import NLS.KdV.HillZeroCount
import NLS.KdV.HillWeightedCoefficients
import NLS.KdV.HillBilinearSymmetry
import NLS.FunctionalAnalysis.TwoDimensionalDeterminant
import NLS.KdV.HillSpectralLipschitz
import NLS.KdV.HillRootSeparation
import NLS.SequenceSpaces.WeightedInsertion
import NLS.SequenceSpaces.PositiveFourierTail
import NLS.SequenceSpaces.ReciprocalSquareTail
import NLS.KdV.HillPeriodOnePotential
import NLS.KdV.HillGapTail
import NLS.KdV.ConstantUpperSpectralBridge
import NLS.KdV.ClassicalSpectralSymmetry
import NLS.KdV.ClassicalDiscriminant
import NLS.KdV.ClassicalHillFlow
import NLS.KdV.HillClassicalIdentification
import NLS.FunctionalAnalysis.AbsoluteContinuityTranslation
import NLS.FunctionalAnalysis.LinearVolterraLinearity
import NLS.KdV.ClassicalHillMultipliers
import NLS.KdV.HillFullPeriod
import NLS.KdV.HillDiscriminantNecessity
import NLS.KdV.HillFirstOrderReduction
import NLS.KdV.HillL2SpectralCriterion
import NLS.KdV.HillDiscriminantComparison
import NLS.ComplexAnalysis.EntireEvenSquareDescent
import NLS.KdV.HillL2EnergyDiscriminant
import NLS.KdV.HillWeightIndependence
import NLS.KdV.HillPhysicalGapBounds
import NLS.ComplexAnalysis.ZeroCountHomotopy
import NLS.ComplexAnalysis.TwoZeroOrderComparison
import NLS.KdV.ClassicalLocalPrimitive
import NLS.KdV.ClassicalFreePrimitive
import NLS.KdV.HillRealSpectrum
import NLS.KdV.HillCharacteristicZeros
import NLS.KdV.HillRealGapPairs
import NLS.KdV.HillWideLocalization
import NLS.ComplexAnalysis.RealDiameterDisc
import NLS.SequenceSpaces.OrderedOneSidedEnumeration
import NLS.KdV.HillFreeSpectrum
import NLS.KdV.HillCentralCounting
import NLS.KdV.HillCentralRoots
import NLS.KdV.HillGlobalRealLabels
import NLS.KdV.HillRealLabelingUniqueness
import NLS.KdV.HillCanonicalRealLabels
import NLS.KdV.HillCanonicalGapBounds
import NLS.SequenceSpaces.OrderedFiniteContinuity
import NLS.KdV.HillCumulativeCounts
import NLS.KdV.HillLabelContinuity
import NLS.KdV.HillCanonicalFreeLabels
import NLS.KdV.HillRealTraceParity
import NLS.ComplexAnalysis.TracePrimitiveContinuation
import NLS.KdV.HillL2SourcePrimitive
import NLS.KdV.HillL2HighContourMoments
import NLS.ComplexAnalysis.TracePrimitiveMoments
import NLS.KdV.HillL2ContourDeformation
import NLS.Fourier.ContinuousConjugation
import NLS.KdV.ClassicalHillConjugation
import NLS.KdV.HillL2Conjugation
import NLS.ComplexAnalysis.TracePrimitiveReflection
import NLS.KdV.HillL2PrimitiveReflection
import NLS.KdV.HillRealBands
import NLS.ComplexAnalysis.RealSimpleZeroSigns
import NLS.KdV.HillRealGapSigns
import NLS.KdV.HillRealGapIntegrals
import NLS.ComplexAnalysis.AnalyticDiscSquareRoot
import NLS.ComplexAnalysis.AnalyticTwoZeroRoot
import NLS.ComplexAnalysis.TwoZeroDeflation
import NLS.ComplexAnalysis.TwoZeroRootEndpointBound
import NLS.KdV.HillL2GapCutRoots
import NLS.KdV.HillL2GapCutPrimitives
import NLS.KdV.HillL2GapCutBoundary
import NLS.KdV.HillL2CollapsedGapMoments
import NLS.ComplexAnalysis.TraceRootPrimitive
import NLS.KdV.HillL2NormalizedCutPrimitive
import NLS.KdV.HillL2CutPrimitiveReflection
import NLS.KdV.HillL2CutPrimitiveEndpointValues
import NLS.ComplexAnalysis.LogarithmStripNormalization
import NLS.KdV.HillL2RealSourcePhase
import NLS.KdV.HillL2CutRealPhase
import NLS.KdV.HillL2CutEndpointNormalization
import NLS.ComplexAnalysis.RealCutConjugation
import NLS.ComplexAnalysis.GapPrimitiveSquare
import NLS.ComplexAnalysis.CoshSquareCoordinate
import NLS.KdV.HillL2CutPrimitiveSquare
import NLS.KdV.HillL2CutSquareTrace
import NLS.KdV.HillL2CutSquareDeflation
import NLS.ComplexAnalysis.RealTwoZeroUnit
import NLS.ComplexAnalysis.RealEndpointRootBoundary
import NLS.KdV.HillL2CutPrimitiveUnit
import NLS.KdV.HillL2CutUnitOrientation
import NLS.KdV.HillL2GapBoundaryValues
import NLS.Articles.KdVEstimates.EstimateAdapter
import NLS.ComplexAnalysis.RealGapEllipse
import NLS.ComplexAnalysis.RealGapEllipseHomotopy
import NLS.ComplexAnalysis.RealGapEllipseIntegral
import NLS.ComplexAnalysis.RealGapEllipseLimit
import NLS.ComplexAnalysis.RealCutCircleIntegral
import NLS.ComplexAnalysis.NestedCircleHomotopy
import NLS.ComplexAnalysis.AnalyticCutContour
import NLS.KdV.HillL2GapContourIntegral
import NLS.KdV.HillL2HighGapMoments
import NLS.KdV.HillL2DiscAsymptotics
import NLS.ZakharovShabat.ContinuousPotentialL2Bound
import NLS.KdV.ClassicalSpectralEmbedding
import NLS.KdV.ClassicalHillSpectrum
import NLS.KdV.ClassicalSourcePrimitive
import NLS.KdV.ClassicalContourCoverage
import NLS.KdV.ClassicalHillDiscAsymptotics
import NLS.KdV.ClassicalHillHighTracePhase
import NLS.KdV.HillL2TraceControl
import NLS.ZakharovShabat.ClassicalSolutionInjectivity
import NLS.KdV.ClassicalHillGreen
import NLS.KdV.ClassicalHighGapPairs
import NLS.KdV.ClassicalHillReality
import NLS.KdV.ClassicalHillPrimitiveSheets
import NLS.KdV.ClassicalHillPrimitiveReflection
import NLS.KdV.ClassicalHillBandNormalization
import NLS.KdV.ClassicalHillHighPrimitiveStrip
import NLS.KdV.HillL2PrimitiveStrip
import NLS.KdV.ClassicalBranchPrimitive
import NLS.KdV.ClassicalCoshStripControl
import NLS.KdV.ClassicalHillSmallDiscTrace
import NLS.KdV.ClassicalHillSmallGapCoverage
import NLS.KdV.ClassicalHillHighEndpointNormalization
import NLS.KdV.ClassicalHillSquaredPrimitiveMatching
import NLS.KdV.ClassicalHillWholeGapSquares
import NLS.KdV.HillL2WholeGapSquares
import NLS.ComplexAnalysis.AnalyticLocalLipschitz
import NLS.KdV.ClassicalHillFreeSquareComparison
import NLS.KdV.HillL2FreeSquareComparison
import NLS.KdV.HillL2HighGapPairs
import NLS.KdV.HillL2SmallGapCoverage
import NLS.KdV.HillL2GapSquareFamilies
import NLS.KdV.HillL2GapQuotients
import NLS.ComplexAnalysis.NormalizedSquareRootBounds
import NLS.KdV.HillL2GapQuotientAsymptotics
import NLS.KdV.HillHighMomentComparison
import NLS.KdV.HillL2GapSquareIdentification
import NLS.KdV.HillRealGapUnitBound
import NLS.KdV.HillEventualActionGapBound
import NLS.KdV.HillWeightedRealActions
import NLS.KdV.ActionHamiltonianMoments
import NLS.ComplexAnalysis.TracePrimitiveFunctoriality
import NLS.KdV.ClassicalL2PrimitiveAgreement
import NLS.ComplexAnalysis.PositiveRealPart
import NLS.KdV.HillL2HalfPlaneSheets
import NLS.ComplexAnalysis.UpperTracePrimitiveExtension
import NLS.KdV.HillL2RegularBoundary
import NLS.ComplexAnalysis.RealCoshTrace
import NLS.KdV.HillL2BoundaryGapProfile
import NLS.KdV.HillL2UpperCutAgreement
import Lean.Util.CollectAxioms
import NLS.ComplexAnalysis.UpperLogarithmBoundary
import NLS.KdV.HillL2AllBoundaryLimits
import NLS.ComplexAnalysis.ParametricUpperLogarithmBoundary
import NLS.KdV.HillL2BoundaryLabelContinuity
import NLS.KdV.HillL2AllEndpointNormalization
import NLS.KdV.HillL2GlobalGapBoundaryValues
import NLS.KdV.HillL2BandContinuation
import NLS.ComplexAnalysis.ClosedUpperExtension
import NLS.KdV.HillL2CutBounds
import NLS.ComplexAnalysis.RealGapDiscIsolation
import NLS.KdV.HillRealGapContours
import NLS.ComplexAnalysis.BoundedPuncturedCircleIntegral
import NLS.KdV.HillL2AllGapContourIntegrals
import NLS.KdV.HillL2RealCutDifferential
import NLS.KdV.HillL2RealContourMoments
import NLS.ComplexAnalysis.BoundaryAnalyticCoordinate
import NLS.ComplexAnalysis.CoshSquareLocalCoordinate
import NLS.KdV.HillL2AllGapSquares
import NLS.ComplexAnalysis.ShiftedSquarePeriod
import NLS.KdV.HillL2SquareGapPeriods
import NLS.KdV.HillHierarchyMomentSummability
import NLS.KdV.HillL2EndpointContinuity
import NLS.KdV.HillL2GroundSquare
import NLS.FunctionalAnalysis.UnitComplexCurveIntegral
import NLS.ComplexAnalysis.ScalarStateCrossMass
import NLS.ComplexAnalysis.QuadraticPuncturedLimit
import NLS.KdV.HillDirichletLagrange
import NLS.KdV.HillDirichletSimplicity
import NLS.KdV.HillDirichletRootBranches
import NLS.KdV.HillFreeDirichlet
import NLS.ComplexAnalysis.ClosedIntervalRoots
import NLS.ComplexAnalysis.PositiveZeroUniqueness
import NLS.KdV.HillDirichletGapExistence
import NLS.KdV.HillDirichletGapUniqueness
import NLS.KdV.HillDirichletLabels
import NLS.KdV.HillDirichletLabelContinuity
import NLS.KdV.HillDirichletSlope
import NLS.KdV.HillDirichletNormingData
import NLS.KdV.HillDirichletAnalyticLabels
import NLS.KdV.HillDirichletAnalyticNorming
import NLS.KdV.HillDirichletBranchDerivatives
import NLS.KdV.HillDirichletPotentialDerivative
import NLS.KdV.HillDirichletKernelNormalization
import NLS.KdV.HillDirichletGradients
import NLS.KdV.ClassicalHillDirichletBrackets
import NLS.ComplexAnalysis.RealEnergySquareRoot
import NLS.KdV.HillStateJointContinuity
import NLS.KdV.HillRealPeriodOneTruncation
import NLS.ComplexAnalysis.ScalarStateSquaredPairing
import NLS.KdV.HillDirichletSquaredPairing
import NLS.KdV.HillDirichletGradientCurves
import NLS.KdV.HillDirichletGardnerBrackets
import NLS.KdV.HillDirichletGradientH1
import NLS.KdV.ClassicalHillMixedPairings
import NLS.ComplexAnalysis.ScalarStateMixedPairing
import NLS.KdV.HillDirichletCosineData
import NLS.KdV.HillDirichletMixedPairings
import NLS.KdV.HillDirichletSlopePotentialDerivative
import NLS.KdV.HillDirichletSlopeVariation
import NLS.Fourier.ContinuousConstants
import NLS.KdV.HillDirichletSlopeShift
import NLS.KdV.HillLogNormingGradient
import NLS.KdV.HillPhysicalDirectionPairing
import NLS.KdV.HillLogNormingCotangent
import NLS.KdV.HillLogNormingRegularity
import NLS.KdV.HillMixedGardnerBrackets
import NLS.KdV.ClassicalHillLogNormingBrackets
import NLS.KdV.HillLogNormingGardnerBrackets
import NLS.KdV.HillAbelianRootBox
import NLS.KdV.HillAbelianNumeratorProduct
import NLS.KdV.HillAbelianProductContinuity
import NLS.KdV.HillAbelianProductZeros
import NLS.ComplexAnalysis.ContinuousCircleIntegral
import NLS.KdV.HillAbelianCandidatePeriods
import NLS.KdV.HillAbelianNormalizationProblem
import NLS.KdV.HillFreeAbelianRoots
import NLS.KdV.HillFreeAbelianQuotient
import NLS.KdV.HillRealGapContourDiscs
import NLS.KdV.HillFreeAbelianNormalization
import NLS.KdV.HillAbelianCircleIntegrability
import NLS.KdV.HillFreeAbelianRootVariation
import NLS.KdV.HillFreeAbelianPeriodJacobian
import NLS.ComplexAnalysis.HilbertWeightedProduct
import NLS.SequenceSpaces.PositiveReciprocalLattice
import NLS.KdV.HillAbelianHilbertInput
import NLS.KdV.HillAbelianHilbertProduct
import NLS.KdV.HillGapRootHilbertCoordinates
import NLS.KdV.HillAbelianHilbertPeriods
import NLS.KdV.HillAbelianComplexRoot
import NLS.KdV.HillAbelianComplexPeriods
import NLS.ComplexAnalysis.HilbertPositiveProducts
import NLS.SequenceSpaces.PositiveDeletedProjection
import NLS.SequenceSpaces.PositiveDeletedSpace
import NLS.KdV.HillFreeAbelianResidue
import NLS.KdV.HillFreeSeparatedWeights
import NLS.KdV.HillFreeAbelianProductSeparation
import NLS.KdV.HillFreeScaledPeriodIdentity
import NLS.KdV.HillFreePeriodSequence
import NLS.KdV.HillFreePeriodDerivative
import NLS.KdV.HillFreeSupportedPeriodMap
import NLS.ComplexAnalysis.ScalarSineDuhamel
import NLS.ComplexAnalysis.DuhamelIntegralBounds
import NLS.ComplexAnalysis.UnitIntervalNormEnergy
import NLS.KdV.ClassicalHillDuhamel
import NLS.KdV.ClassicalHillSmallPotential
import NLS.KdV.HillContinuousPotentialMass
import NLS.KdV.HillL2SmallPotentialTrace
import NLS.ComplexAnalysis.InverseSquareRootBounds
import NLS.KdV.HillSmallPotentialRadicand
import NLS.KdV.HillFreeGapContourGeometry
import NLS.ComplexAnalysis.SineAnnulusLowerBound
import NLS.KdV.HillFreeContourRadicandBound
import NLS.KdV.HillCommonComplexContourDomain
import NLS.KdV.HillComplexPeriodDomainAnalytic
import NLS.KdV.HillCommonComplexPeriods
import NLS.KdV.HillComplexContourInverseRoot
import NLS.KdV.HillFreeContourSeparation
import NLS.KdV.HillFreeContourWeights
import NLS.KdV.HillScaledFreeContourQuotient
import NLS.KdV.HillContourHilbertProductSeparation
import NLS.ComplexAnalysis.NormalizedCircleIntegralBounds
import NLS.KdV.HillContourHilbertPsiBounds
import NLS.KdV.HillComplexPeriodIntegrandBounds
import NLS.KdV.HillComplexPeriodErrorBounds
import NLS.KdV.HillComplexPeriodControl
import NLS.KdV.HillComplexPeriodCoordinates
import NLS.KdV.HillComplexPeriodSequence
import NLS.KdV.HillComplexPeriodAnalytic
import NLS.KdV.HillComplexSupportedPeriodMap
import NLS.KdV.HillComplexImplicitPeriodRoots
import NLS.KdV.HillComplexPeriodLocalRootGerm
import NLS.KdV.HillComplexNormalizedPeriodGerm
import NLS.KdV.HillComplexNumeratorZeros
import NLS.ComplexAnalysis.TraceRootBranchUniqueness
import NLS.ComplexAnalysis.DenseNonreal
import NLS.KdV.HillComplexRootSourceMatching
import NLS.KdV.HillPhysicalRootSourceIdentification
import NLS.KdV.HillSourceRealBandPreservation
import NLS.KdV.HillFreeContourPhysicalRoot
import NLS.KdV.HillAbelianPeriodConjugation
import NLS.KdV.HillFreeContourSpectralGapIsolation
import NLS.ComplexAnalysis.ImplicitLocalUniqueness
import NLS.SequenceSpaces.PositiveDeletedConjugation
import NLS.KdV.HillAbelianImplicitRootReality
import NLS.KdV.HillPhysicalNormalizedPeriodGerm
import NLS.ComplexAnalysis.RealIntegralZero
import NLS.ComplexAnalysis.CosineZeroPeriod
import NLS.ComplexAnalysis.RealGapZeroPeriod
import NLS.KdV.HillHilbertRootCoordinates
import NLS.KdV.HillHilbertNumeratorReality
import NLS.KdV.HillFreeEnergySeparation
import NLS.KdV.HillHilbertRootIsolation
import NLS.KdV.HillHilbertRootGermIsolation
import NLS.KdV.HillOmittedEnergyRootProduct
import NLS.KdV.HillOmittedEnergyRootNonvanishing
import NLS.KdV.HillDeflatedCanonicalRoot
import NLS.KdV.HillDeflatedCanonicalRootPhase
import NLS.ComplexAnalysis.ConvexCutCirclePeriod
import NLS.KdV.HillSourceBandLabelPreservation
import NLS.KdV.HillFreeContourPhysicalBandBounds
import NLS.KdV.HillPhysicalNumeratorGapZero
import NLS.KdV.HillPhysicalNumeratorGapContainment
import NLS.KdV.HillPhysicalGapRootGerm
import NLS.KdV.HillPhysicalNormalizedGapPeriodGerm
import NLS.KdV.HillFilledGapCutDomain
import NLS.KdV.HillPhysicalContourPeriods
import NLS.KdV.HillIntrinsicComplexPeriods
import NLS.KdV.HillIntrinsicNormalizedGapPeriodGerm
import NLS.KdV.HillAbelianPhysicalRootSequence
import NLS.KdV.HillPhysicalGapBoxNormalization
import NLS.ComplexAnalysis.CompactNonzeroNormLowerBound
import NLS.KdV.HillGapBoxNumeratorReality
import NLS.KdV.HillGlobalGapPeriodCriterion
import NLS.KdV.HillGapBoxPeriodNonvanishing
import NLS.KdV.HillCanonicalRootConjugation
import NLS.KdV.HillIntrinsicPeriodReality
import NLS.KdV.HillAbelianRootUpdate
import NLS.KdV.HillAbelianRootSlope
import NLS.KdV.HillRootSlopeNonvanishing
import NLS.KdV.HillIntrinsicPeriodLinearity
import NLS.KdV.HillRootPeriodAffineFormula
import NLS.KdV.HillRootPeriodGapLocation
import NLS.KdV.HillRootCandidateUpdate
import NLS.KdV.HillRootPeriodContinuity
import NLS.KdV.HillContinuousGapRootMap
import NLS.FunctionalAnalysis.CountableIntervalBox
import NLS.FunctionalAnalysis.FiniteIntervalBoxFixedPoint
import NLS.FunctionalAnalysis.CountableIntervalBoxFixedPoint
import NLS.KdV.HillGlobalPeriodRoots
import NLS.KdV.HillGlobalNormalizedDifferentials
import NLS.KdV.HillGlobalDifferentialReality
import NLS.KdV.HillGapSignedRootFrequencies
import NLS.KdV.HillGapRootEnergyProduct
import NLS.KdV.HillGapProductExteriorBounds
import NLS.KdV.HillGapEnergyProductSimpleZeros
import NLS.KdV.HillGapNumeratorDecay
import NLS.KdV.HillEntirePeriodInterpolation
import NLS.KdV.HillGlobalDifferentialUniqueness
import NLS.KdV.HillGlobalRootUniqueness
import NLS.KdV.HillGlobalDifferentialLocalIdentification
import NLS.KdV.HillGlobalDifferentialFreeAnalyticGerm
import NLS.KdV.HillGapRootHilbertCompactness
import NLS.KdV.HillRootCoordinateAffineVariation
import NLS.KdV.HillIntrinsicPeriodRootJacobian
import NLS.KdV.HillComplexRootCoordinatePeriods
import NLS.KdV.HillAnalyticCoordinatePeriodRoots
import NLS.KdV.HillIntrinsicPeriodReflection
import NLS.KdV.HillComplexEntirePeriodInterpolation
import NLS.KdV.HillEntireNumeratorRootVariation

/-! Transitive audit of the shared KdV foundations and article adapters.
The article's main theorems are not claimed by this audit. -/

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let shared := #[``NLS.FiniteSpectralDeterminant.det_prod_formula,
    ``NLS.FiniteSpectralDeterminant.determinant_shift_bound,
    ``NLS.Weight.pullback, ``NLS.Weight.pullback_apply,
    ``NLS.WeightedCoeff.insertIsometry, ``NLS.WeightedCoeff.insertIsometry_image,
    ``NLS.WeightedCoeff.insertIsometry_outside, ``NLS.WeightedCoeff.norm_insertIsometry,
    ``NLS.Coeff.pair_sq_le_norm_sq, ``NLS.Coeff.positive_pair_tail_sq,
    ``NLS.ReciprocalSeries.summable_nat_reciprocal_sq_tail,
    ``NLS.ReciprocalSeries.tsum_nat_reciprocal_sq_tail_le,
    ``NLS.SpectralWeight.doubleIndex, ``NLS.SpectralWeight.doubleIndex_apply,
    ``NLS.FunctionalAnalysis.absolutelyContinuousOnInterval_comp_add_right,
    ``NLS.LinearVolterra.solution_add, ``NLS.LinearVolterra.solution_zero_initial,
    ``NLS.ComplexAnalysis.complex_sqrt_sq,
    ``NLS.ComplexAnalysis.analyticOnNhd_entire_even_square_descent,
    ``NLS.ComplexAnalysis.isLocallyConstant_analyticZeroCount,
    ``NLS.ComplexAnalysis.analyticZeroCount_eq_of_homotopy,
    ``NLS.ComplexAnalysis.analyticOrderNatAt_eq_of_two_zero_counts,
    ``NLS.ComplexAnalysis.ofReal_mem_realDiameter_closedBall_iff,
    ``NLS.ComplexAnalysis.ofReal_mem_realDiameter_sphere_iff,
    ``NLS.ComplexAnalysis.ne_zero_on_realDiameter_sphere,
    ``NLS.appendPairedTail, ``NLS.appendPairedTail_prefix,
    ``NLS.appendPairedTail_even, ``NLS.appendPairedTail_odd,
    ``NLS.monotone_appendPairedTail,
    ``NLS.ComplexAnalysis.eventually_analyticZeroCount_eq_of_continuous_family,
    ``NLS.finiteLowerCount, ``NLS.finiteLowerCount_le_iff,
    ``NLS.index_lt_finiteLowerCount_iff, ``NLS.tendsto_ordered_finite_of_counts,
    ``NLS.Fourier.continuousFourierCLM_star,
    ``NLS.ComplexAnalysis.circleIntegral_pow_mul_deriv_eq_neg,
    ``NLS.ComplexAnalysis.circleIntegral_eq_conj_of_anti_conj,
    ``NLS.ComplexAnalysis.circleIntegral_im_eq_zero_of_anti_conj,
    ``NLS.ComplexAnalysis.not_isLocalExtr_of_simple_real_zero,
    ``NLS.ComplexAnalysis.negative_on_preconnected_of_nonzero,
    ``NLS.ComplexAnalysis.positive_right_of_negative_left,
    ``NLS.ComplexAnalysis.positive_left_of_negative_right,
    ``NLS.ComplexAnalysis.above_pos_level_of_square_gt,
    ``NLS.ComplexAnalysis.above_pos_level_of_square_gt_left,
    ``NLS.ComplexAnalysis.analyticOnNhd_continuous_squareRoot,
    ``NLS.ComplexAnalysis.exists_analytic_squareRoot_on_ball,
    ``NLS.ComplexAnalysis.endpointRoot,
    ``NLS.ComplexAnalysis.midpoint_mem_complex_segment,
    ``NLS.ComplexAnalysis.endpointRoot_sq,
    ``NLS.ComplexAnalysis.analyticOnNhd_endpointRoot,
    ``NLS.ComplexAnalysis.exists_analytic_squareRoot_on_two_zero_cut,
    ``NLS.ComplexAnalysis.twoZeroQuotient,
    ``NLS.ComplexAnalysis.dslope_zero_at_second_zero,
    ``NLS.ComplexAnalysis.twoZeroQuotient_factor,
    ``NLS.ComplexAnalysis.analyticOnNhd_twoZeroQuotient,
    ``NLS.ComplexAnalysis.twoZeroQuotient_ne_zero,
    ``NLS.ComplexAnalysis.norm_twoZeroQuotient_le,
    ``NLS.ComplexAnalysis.exists_two_zero_root_endpoint_bound,
    ``NLS.ComplexAnalysis.exists_primitive_on_disc_complement_of_zero_period,
    ``NLS.ComplexAnalysis.exists_primitive_segment_left_boundary_limit,
    ``NLS.ComplexAnalysis.exists_primitive_segment_right_boundary_limit,
    ``NLS.ComplexAnalysis.hasDerivAt_traceRoot_multiplier,
    ``NLS.ComplexAnalysis.exp_primitive_of_traceRoot,
    ``NLS.ComplexAnalysis.exp_neg_primitive_of_traceRoot,
    ``NLS.ComplexAnalysis.traceRoot_identities_of_exp,
    ``NLS.ComplexAnalysis.traceRoot_primitive_reflection,
    ``NLS.ComplexAnalysis.traceRoot_primitive_boundary_values,
    ``NLS.ComplexAnalysis.multiplier_eq_exp_of_normalized_primitive,
    ``NLS.ComplexAnalysis.real_mem_Ioo_of_preconnected_avoids,
    ``NLS.ComplexAnalysis.sinh_eq_zero_of_re_zero_im_int_pi,
    ``NLS.ComplexAnalysis.exp_neg_I_nat_pi,
    ``NLS.ComplexAnalysis.eq_zero_of_exp_eq_one_of_abs_im_le_pi,
    ``NLS.ComplexAnalysis.eq_of_exp_eq_of_abs_im_sub_le_pi,
    ``NLS.ComplexAnalysis.conj_mem_real_cut,
    ``NLS.ComplexAnalysis.gapPrimitiveSquareExtension,
    ``NLS.ComplexAnalysis.gapPrimitiveSquareExtension_spec,
    ``NLS.ComplexAnalysis.coshSquareCoordinate,
    ``NLS.ComplexAnalysis.coshSquareCoordinate_sq,
    ``NLS.ComplexAnalysis.analyticOnNhd_coshSquareCoordinate,
    ``NLS.ComplexAnalysis.coshSquareCoordinate_ofReal,
    ``NLS.ComplexAnalysis.coshSquareCoordinate_neg_ofReal,
    ``NLS.ComplexAnalysis.coshSquareCoordinate_re_le_one_of_nonpos,
    ``NLS.ComplexAnalysis.cosh_add_I_nat_pi,
    ``NLS.ComplexAnalysis.deriv_coshSquareCoordinate_zero,
    ``NLS.ComplexAnalysis.deriv_ne_zero_of_analyticOrderNatAt_eq_one,
    ``NLS.ComplexAnalysis.im_eq_zero_of_mem_real_segment,
    ``NLS.ComplexAnalysis.not_mem_real_segment_of_im_ne_zero,
    ``NLS.ComplexAnalysis.real_two_zero_unit_conj,
    ``NLS.ComplexAnalysis.endpointRoot_real_gap_limits,
    ``NLS.ZakharovShabat.normalizedStandardRoot_re_neg_of_gt_rightEndpoint,
    ``NLS.ZakharovShabat.normalizedStandardRoot_tendsto_gap_upper_side,
    ``NLS.ZakharovShabat.normalizedStandardRoot_tendsto_gap_lower_side,
    ``NLS.ComplexAnalysis.realGapEllipse,
    ``NLS.ComplexAnalysis.realGapEllipse_re,
    ``NLS.ComplexAnalysis.realGapEllipse_im,
    ``NLS.ComplexAnalysis.realGapEllipse_zero,
    ``NLS.ComplexAnalysis.realGapEllipse_two_pi,
    ``NLS.ComplexAnalysis.hasDerivAt_realGapEllipse,
    ``NLS.ComplexAnalysis.realGapEllipse_mem_closedBall,
    ``NLS.ComplexAnalysis.re_mem_Icc_of_mem_real_segment,
    ``NLS.ComplexAnalysis.realGapEllipse_not_mem_segment,
    ``NLS.ComplexAnalysis.tendsto_realGapEllipse,
    ``NLS.ComplexAnalysis.realGapEllipsePath,
    ``NLS.ComplexAnalysis.realGapEllipsePath_contDiffOn,
    ``NLS.ComplexAnalysis.circlePath_symm_apply,
    ``NLS.ComplexAnalysis.circlePath_symm_contDiffOn,
    ``NLS.ComplexAnalysis.realGapEllipse_affine_coordinates,
    ``NLS.ComplexAnalysis.realGapEllipse_affine_mem_closedBall,
    ``NLS.ComplexAnalysis.realGapEllipse_affine_not_mem_segment,
    ``NLS.ComplexAnalysis.curveIntegral_realGapEllipse_eq_neg_circleIntegral,
    ``NLS.ComplexAnalysis.curveIntegral_realGapEllipse_eq_intervalIntegral,
    ``NLS.ComplexAnalysis.realGapEllipse_limit_mem_Icc,
    ``NLS.ComplexAnalysis.tendsto_realGapEllipse_lower,
    ``NLS.ComplexAnalysis.tendsto_realGapEllipse_upper,
    ``NLS.ComplexAnalysis.tendsto_deriv_realGapEllipse,
    ``NLS.ComplexAnalysis.norm_deriv_realGapEllipse_le,
    ``NLS.ComplexAnalysis.tendsto_realGapEllipse_intervalIntegral,
    ``NLS.ComplexAnalysis.integral_real_cosine_pullback,
    ``NLS.ComplexAnalysis.tendsto_curveIntegral_realGapEllipse,
    ``NLS.ComplexAnalysis.exists_norm_bound_of_continuous_square_on_compact,
    ``NLS.ComplexAnalysis.circleIntegral_eq_neg_real_cut_jump,
    ``NLS.ComplexAnalysis.lineMap_circleMap_centers_radii,
    ``NLS.ComplexAnalysis.affineCircleHomotopy_ne_of_mem_both_balls,
    ``NLS.ComplexAnalysis.affineCircleHomotopy_mem_outer_closedBall,
    ``NLS.ComplexAnalysis.circleIntegral_eq_of_analytic_cut_nestedCircles,
    ``NLS.ComplexAnalysis.norm_two_root_quotient_sub_le_on_disc,
    ``NLS.ZakharovShabat.norm_continuousPotentialL2Class_le_two_norm,
    ``NLS.ZakharovShabat.continuousPotentialL2CLM,
    ``NLS.ZakharovShabat.continuousPotentialL2CLM_apply,
    ``NLS.ZakharovShabat.classicalSolution_injective_initial,
    ``NLS.ZakharovShabat.classicalSolution_eq_zero_imp_initial_eq_zero,
    ``NLS.ComplexAnalysis.exists_local_lipschitz_bound_of_analyticAt,
    ``NLS.ComplexAnalysis.norm_sqrt_sub_one_le,
    ``NLS.ComplexAnalysis.prescribedSquareRoot_analytic_and_close,
    ``NLS.ComplexAnalysis.re_pos_of_analyticOnNhd_nonneg_not_constant,
    ``NLS.ComplexAnalysis.tendsto_real_upper_vertical,
    ``NLS.ComplexAnalysis.real_upper_nhds_neBot,
    ``NLS.ComplexAnalysis.exists_upper_trace_primitive_extension_on_ball,
    ``NLS.ComplexAnalysis.cosh_real_coordinate,
    ``NLS.ComplexAnalysis.cosh_imaginary_coordinate,
    ``NLS.ComplexAnalysis.real_cosh_trace_coordinates,
    ``NLS.ComplexAnalysis.abs_real_cosh_trace_of_re_ne_zero,
    ``NLS.ComplexAnalysis.re_eq_zero_of_real_cosh_trace_band,
    ``NLS.ComplexAnalysis.re_eq_arcosh_of_real_cosh_trace_gap,
    ``NLS.ComplexAnalysis.phase_eq_on_of_sin_eq_zero,
    ``NLS.ComplexAnalysis.exists_upper_logarithm_boundary_limit,
    ``NLS.ComplexAnalysis.continuous_real_boundary_of_upper_limits,
    ``NLS.ComplexAnalysis.continuous_boundary_logarithm_of_constant_exponential,
    ``NLS.ComplexAnalysis.realBoundaryExtension,
    ``NLS.ComplexAnalysis.continuousOn_realBoundaryExtension_upper,
    ``NLS.ComplexAnalysis.exists_bound_realBoundaryExtension_on_closedBall,
    ``NLS.ComplexAnalysis.ofReal_mem_ordered_segment,
    ``NLS.ComplexAnalysis.real_gap_disc_exterior_band,
    ``NLS.ComplexAnalysis.circleIntegral_eq_zero_of_bounded_puncture,
    ``NLS.ComplexAnalysis.continuousAt_realBoundaryExtension_of_limits,
    ``NLS.ComplexAnalysis.analyticAt_of_continuousAt_coordinate,
    ``NLS.ComplexAnalysis.deriv_coshSquareCoordinate_sq_ne_zero,
    ``NLS.ComplexAnalysis.circleIntegral_pow_mul_shifted_square,
    ``NLS.ComplexAnalysis.real_closedBall_subset_diameter_ball,
    ``NLS.ComplexAnalysis.real_closedBalls_disjoint_of_separated,
    ``NLS.ComplexAnalysis.circleIntegral_eq_sum_of_finite_holes,
    ``NLS.ComplexAnalysis.norm_unimodular_trace_error_le_separate_bounds,
    ``NLS.ZakharovShabat.classical_zero_initial_forced_duhamel,
    ``NLS.ZakharovShabat.norm_zero_initial_forced_le_exp_weight,
    ``NLS.ZakharovShabat.exists_nlsWKBCarrier_weighted_bounds,
    ``NLS.ZakharovShabat.classicalPotentialOfFunctions,
    ``NLS.ZakharovShabat.classicalPotentialOfFunctions_apply,
    ``NLS.ZakharovShabat.exists_nlsWKBVector_solution_error_bound,
    ``NLS.ZakharovShabat.exists_nlsWKBVector_endpoint_error_bound,
    ``NLS.ZakharovShabat.exists_nlsWKBVector_upper_solution_error_bound,
    ``NLS.ZakharovShabat.exists_nlsWKBVector_upper_endpoint_error_bound,
    ``NLS.ZakharovShabat.classicalSolution_one_snd,
    ``NLS.ZakharovShabat.nlsHamiltonianPhase,
    ``NLS.ZakharovShabat.exists_classicalDiscriminant_hamiltonian_error_bound,
    ``NLS.ZakharovShabat.exists_classicalDiscriminant_upper_hamiltonian_error_bound,
    ``NLS.ComplexAnalysis.exists_norm_sub_le_two_mul_sinh_sub,
    ``NLS.ComplexAnalysis.norm_cosh_shift_sub,
    ``NLS.ComplexAnalysis.exists_norm_phase_sub_le_discriminant_error,
    ``NLS.ComplexAnalysis.mem_Ioo_of_continuous_avoiding_endpoint_levels,
    ``NLS.ComplexAnalysis.norm_sinh_increment_weighted_le,
    ``NLS.ComplexAnalysis.norm_phase_sub_le_weighted_cosh_error,
    ``NLS.ComplexAnalysis.norm_imaginary_phase_le_cosh_shift,
    ``NLS.ComplexAnalysis.norm_lt_everywhere_of_local_improvement,
    ``NLS.ComplexAnalysis.cosh_phase_control_of_anchor,
    ``NLS.ZakharovShabat.freeCosineZero,
    ``NLS.ZakharovShabat.freeCosineZero_im,
    ``NLS.ZakharovShabat.freeCosineZero_mem_verticalStrip,
    ``NLS.ZakharovShabat.freeCosineZero_separated,
    ``NLS.ZakharovShabat.tendsto_norm_freeCosineZero,
    ``NLS.ZakharovShabat.freeDiscriminant_freeCosineZero,
    ``NLS.ZakharovShabat.norm_div_free_at_freeCosineZero,
    ``NLS.ZakharovShabat.not_exists_exterior_cosine_quotient_bound,
    ``NLS.ZakharovShabat.nlsHamiltonianCorrection,
    ``NLS.ZakharovShabat.nlsHamiltonianCorrection_zero,
    ``NLS.ZakharovShabat.analyticAt_nlsHamiltonianCorrection,
    ``NLS.ZakharovShabat.nlsHamiltonianPhase_eq_correction,
    ``NLS.ZakharovShabat.nlsHamiltonianCorrection_tendsto,
    ``NLS.ZakharovShabat.iteratedDeriv_nlsHamiltonianCorrection,
    ``NLS.ComplexAnalysis.inverse_power_ratio_le_one,
    ``NLS.ComplexAnalysis.norm_weighted_laurent_term_le,
    ``NLS.ComplexAnalysis.norm_square_model_laurent_error_le,
    ``NLS.ComplexAnalysis.norm_square_error_of_phase_error,
    ``NLS.ComplexAnalysis.norm_square_laurent_error_of_phase_error,
    ``NLS.ComplexAnalysis.exists_upper_circleMap_parameter,
    ``NLS.ComplexAnalysis.weighted_norm_bound_on_circle_of_upper_reflection,
    ``NLS.ComplexAnalysis.norm_quadratic_circle_coefficient_sub_le,
    ``NLS.ComplexAnalysis.hasSum_of_nonnegative_real_partial_limit,
    ``NLS.continuousAt_tsum_of_locally_small_nat_tails,
    ``NLS.exists_local_nat_property_pullback,
    ``NLS.ComplexAnalysis.hasSum_of_eventually_nonnegative_real_partial_limit,
    ``NLS.ComplexAnalysis.norm_square_error_of_phase_error_general,
    ``NLS.ComplexAnalysis.norm_square_model_energy_error_le,
    ``NLS.ComplexAnalysis.norm_square_energy_error_of_phase_error,
    ``NLS.ComplexAnalysis.norm_energy_circle_coefficient_sub_le,
    ``NLS.nat_tsum_tail_antitone_of_nonneg,
    ``NLS.DifferentialPolynomial.powerSeriesDerivation,
    ``NLS.DifferentialPolynomial.coeff_powerSeriesDerivation,
    ``NLS.DifferentialPolynomial.powerSeriesDerivation_C,
    ``NLS.DifferentialPolynomial.powerSeriesDerivation_X,
    ``NLS.DifferentialPolynomial.powerSeriesDerivation_commute,
    ``NLS.DifferentialPolynomial.differentialRiccatiSequence,
    ``NLS.DifferentialPolynomial.differentialRiccatiSequence_zero,
    ``NLS.DifferentialPolynomial.differentialRiccatiSequence_one,
    ``NLS.DifferentialPolynomial.differentialRiccatiSequence_recurrence,
    ``NLS.DifferentialPolynomial.differentialRiccatiSequence_unique,
    ``NLS.DifferentialPolynomial.differentialRiccatiSeries,
    ``NLS.DifferentialPolynomial.coeff_differentialRiccatiSeries,
    ``NLS.DifferentialPolynomial.differentialRiccatiSeries_equation,
    ``NLS.DifferentialPolynomial.differentialRiccatiSeries_unique,
    ``NLS.DifferentialPolynomial.differentialRiccatiSequence_neg_derivation,
    ``NLS.DifferentialPolynomial.differentialRiccatiSeries_neg_derivation,
    ``NLS.DifferentialPolynomial.powerSeriesDerivation_neg,
    ``NLS.DifferentialPolynomial.logarithmicPrimitiveCoefficient,
    ``NLS.DifferentialPolynomial.derivation_logarithmicPrimitiveCoefficient,
    ``NLS.DifferentialPolynomial.scalarRiccatiLogInput,
    ``NLS.DifferentialPolynomial.scalarRiccati_log_derivative_identity,
    ``NLS.DifferentialPolynomial.derivation_scalarRiccati_log_odd,
    ``NLS.DifferentialPolynomial.HasWeightedJetReduction,
    ``NLS.DifferentialPolynomial.HasWeightedJetReduction.of_order,
    ``NLS.DifferentialPolynomial.HasWeightedJetReduction.zero,
    ``NLS.DifferentialPolynomial.HasWeightedJetReduction.add,
    ``NLS.DifferentialPolynomial.HasWeightedJetReduction.sum,
    ``NLS.DifferentialPolynomial.HasWeightedJetReduction.add_spatialDerivative,
    ``NLS.DifferentialPolynomial.hasWeightedJetReduction_of_jetOrder,
    ``NLS.DifferentialPolynomial.exists_weighted_jet_reduction,
    ``NLS.DifferentialPolynomial.norm_eval_le_lower_jet_majorant,
    ``NLS.DifferentialPolynomial.scalar_two_factor_interpolation_exponents,
    ``NLS.DifferentialPolynomial.scalar_monomial_interpolation_power_range,
    ``NLS.ComplexAnalysis.circleIntegrable_zero_zpow,
    ``NLS.ComplexAnalysis.circleIntegral_zero_zpow,
    ``NLS.ComplexAnalysis.normalized_circleIntegral_const_mul_zpow,
    ``NLS.ComplexAnalysis.normalized_circleIntegral_weighted_zpow,
    ``NLS.ComplexAnalysis.circleIntegrable_weighted_zpow,
    ``NLS.ComplexAnalysis.normalized_circleIntegral_weighted_finsum,
    ``NLS.ComplexAnalysis.sum_rectangle_ite_eq_antidiagonal,
    ``NLS.ComplexAnalysis.norm_weighted_circle_integral_sub_model_le,
    ``NLS.ComplexAnalysis.circleIntegrable_weighted_finsum,
    ``NLS.SequenceSpaces.hierarchy_mass_product_le,
    ``NLS.SequenceSpaces.exists_hierarchy_action_majorant,
    ``NLS.SequenceSpaces.hierarchy_mass_mono,
    ``NLS.SequenceSpaces.exists_hierarchy_action_majorant_lower,
    ``NLS.ComplexAnalysis.norm_normalizedStandardRoot_sub_center_le,
    ``NLS.ComplexAnalysis.norm_endpointRoot_div_sub_one_le,
    ``NLS.ComplexAnalysis.norm_complexSqrt_sub_positive_le,
    ``NLS.ComplexAnalysis.analyticOrderNatAt_comp_sq_zero,
    ``NLS.SequenceSpaces.sum_symmetric_interval,
    ``NLS.SequenceSpaces.sum_range_one_and_pairs,
    ``NLS.ComplexAnalysis.count_opposite_square_root_pair,
    ``NLS.ComplexAnalysis.square_root_real_coordinate_bounds,
    ``NLS.ZakharovShabat.PeriodicEndpointPair.of_candidates,
    ``NLS.ComplexAnalysis.isPreconnected_of_contains_nonreal_and_real_interval,
    ``NLS.ComplexAnalysis.endpointRoot_real_left,
    ``NLS.ComplexAnalysis.analyticOrderNatAt_linear_mul_comp_sq_zero,
    ``NLS.ComplexAnalysis.endpointRoot_ne_zero_of_not_mem_segment,
    ``NLS.ComplexAnalysis.norm_div_sub_one_le_of_half_error,
    ``NLS.ComplexAnalysis.norm_critical_endpoint_ratio_le,
    ``NLS.SequenceSpaces.nat_square_separation_ge_sum,
    ``NLS.ComplexAnalysis.endpointRoot_real_right,
    ``NLS.ComplexAnalysis.critical_endpoint_ratio_real_positive,
    ``NLS.ComplexAnalysis.HasProd.positive_real_of_each,
    ``NLS.ComplexAnalysis.norm_endpointRoot_ge_right_distance,
    ``NLS.SequenceSpaces.prod_range_div_telescope_le,
    ``NLS.ComplexAnalysis.hasDerivAt_gap_arcsin,
    ``NLS.ComplexAnalysis.intervalIntegrable_gap_arcsine_kernel,
    ``NLS.ComplexAnalysis.integral_gap_arcsine_kernel,
    ``NLS.ComplexAnalysis.integral_eq_weighted_deriv_of_zero_endpoints,
    ``NLS.SequenceSpaces.nonneg_series_cauchy_schwarz,
    ``NLS.SequenceSpaces.square_sum_le_of_weight_lower_bound,
    ``NLS.SequenceSpaces.reciprocal_square_separation_bound,
    ``NLS.SequenceSpaces.summable_quadratic_separation_tail,
    ``NLS.SequenceSpaces.quadratic_separation_cauchy_schwarz,
    ``NLS.ComplexAnalysis.norm_hasProd_le_exp_sum,
    ``NLS.SequenceSpaces.weighted_cutoff_denominator_lower,
    ``NLS.SequenceSpaces.corrected_weighted_gap_tail_exponent_le_one,
    ``NLS.SpectralWeight.nat_weight_le_fixed_shift_realExtension,
    ``NLS.SpectralWeight.ceil_eight_rpow_weight_bound,
    ``NLS.SpectralWeight.product,
    ``NLS.SpectralWeight.product_apply,
    ``NLS.SpectralWeight.sobolev_product_dominates,
    ``NLS.SpectralWeight.ceiling_cutoff_weight_le,
    ``NLS.SequenceSpaces.ceiling_weighted_cutoff_le_quadratic,
    ``NLS.FunctionalAnalysis.unitCurveIntegral,
    ``NLS.FunctionalAnalysis.unitCurveIntegral_apply,
    ``NLS.ComplexAnalysis.scalarStateMass,
    ``NLS.ComplexAnalysis.continuous_scalarStateMass,
    ``NLS.ComplexAnalysis.scalarStateMass_eq_integral,
    ``NLS.ComplexAnalysis.scalarStateMass_pos_of_first_derivative,
    ``NLS.ZakharovShabat.l2SolutionCurve_ne_zero,
    ``NLS.FunctionalAnalysis.unitComplexCurveIntegral,
    ``NLS.FunctionalAnalysis.unitComplexCurveIntegral_apply,
    ``NLS.ComplexAnalysis.scalarStateCrossMass,
    ``NLS.ComplexAnalysis.scalarStateCrossMass_eq_integral,
    ``NLS.ComplexAnalysis.continuous_scalarStateCrossMass,
    ``NLS.ComplexAnalysis.scalarStateCrossMass_self_real,
    ``NLS.ComplexAnalysis.tendsto_sq_punctured,
    ``NLS.ComplexAnalysis.isClosed_exists_zero_in_variable_Icc,
    ``NLS.ComplexAnalysis.eq_of_zero_of_pos_derivative_at_zeros,
    ``NLS.ComplexAnalysis.complex_sqrt_real_formula,
    ``NLS.ComplexAnalysis.continuous_complex_sqrt_real,
    ``NLS.ComplexAnalysis.scalarStateSquaredPairing,
    ``NLS.ComplexAnalysis.scalarStateSquaredPairing_eq_integral,
    ``NLS.ComplexAnalysis.continuous_scalarStateSquaredPairing,
    ``NLS.ComplexAnalysis.scalarStateMixedPairing,
    ``NLS.ComplexAnalysis.scalarStateMixedPairing_eq_integral,
    ``NLS.ComplexAnalysis.continuous_scalarStateMixedPairing,
    ``NLS.Fourier.continuousFourierCLM_const,
    ``NLS.ComplexAnalysis.continuous_circleIntegral_of_continuous_joint_on_sphere,
    ``NLS.ComplexAnalysis.hilbertWeightedProduct,
    ``NLS.ComplexAnalysis.hilbertWeightedPartialProduct,
    ``NLS.ComplexAnalysis.summable_norm_hilbertProductInput,
    ``NLS.ComplexAnalysis.multipliable_hilbertWeightedFactors,
    ``NLS.ComplexAnalysis.tendsto_hilbertWeightedPartialProduct,
    ``NLS.ComplexAnalysis.tendstoUniformlyOn_hilbertWeightedPartialProduct,
    ``NLS.ComplexAnalysis.analyticOnNhd_hilbertWeightedPartialProduct,
    ``NLS.ComplexAnalysis.analyticOnNhd_hilbertWeightedProduct,
    ``NLS.ComplexAnalysis.hilbertWeightedProduct_ne_zero_iff,
    ``NLS.ComplexAnalysis.norm_hilbertWeightedProduct_le,
    ``NLS.ComplexAnalysis.norm_hilbertWeightedProduct_sub_one_le,
    ``NLS.Coeff.positivePuncturedLattice,
    ``NLS.Coeff.positivePuncturedLattice_apply,
    ``NLS.Coeff.positivePuncturedLattice_natSucc,
    ``NLS.Coeff.norm_positivePuncturedLattice_two_le,
    ``NLS.ComplexAnalysis.hilbertWeightedProduct_eq_positive_tprod,
    ``NLS.ComplexAnalysis.multipliable_positive_hilbertWeightedFactors,
    ``NLS.ComplexAnalysis.hilbertWeightedProduct_zero,
    ``NLS.Coeff.positiveDeletedSymbol,
    ``NLS.Coeff.positiveDeletedProjection,
    ``NLS.Coeff.positiveDeletedProjection_apply,
    ``NLS.Coeff.positiveDeletedProjection_eq_self_iff,
    ``NLS.Coeff.positiveDeletedProjection_idempotent,
    ``NLS.PositiveDeletedCoeff,
    ``NLS.Coeff.positiveDeleted_fixed,
    ``NLS.Coeff.positiveDeletedProjectionTo,
    ``NLS.Coeff.positiveDeletedProjectionTo_coe,
    ``NLS.ComplexAnalysis.scalar_sine_duhamel,
    ``NLS.ComplexAnalysis.scalar_cosine_duhamel,
    ``NLS.ComplexAnalysis.norm_complex_cos_le_exp_im,
    ``NLS.ComplexAnalysis.norm_complex_sin_le_exp_im,
    ``NLS.ComplexAnalysis.norm_trig_mul_real_le,
    ``NLS.ComplexAnalysis.norm_sine_duhamel_integral_le,
    ``NLS.ComplexAnalysis.norm_cosine_duhamel_integral_le,
    ``NLS.ComplexAnalysis.integral_norm_sq_unit_le_energy,
    ``NLS.ComplexAnalysis.norm_inv_sqrt_sub_one_le,
    ``NLS.ComplexAnalysis.mem_slitPlane_of_norm_sub_one_le_half,
    ``NLS.ComplexAnalysis.exists_uniform_sine_lower_annulus,
    ``NLS.ComplexAnalysis.norm_normalized_circleIntegral_difference_le,
    ``NLS.ComplexAnalysis.TracePrimitiveFamily.root_eq_continuous_radial_branch,
    ``NLS.ComplexAnalysis.dense_complex_nonreal,
    ``NLS.ComplexAnalysis.exists_injective_augmented_implicit_neighborhood,
    ``NLS.Coeff.positiveDeletedConjugate,
    ``NLS.Coeff.positiveDeletedConjugate_coe,
    ``NLS.Coeff.positiveDeletedConjugate_zero,
    ``NLS.Coeff.continuous_positiveDeletedConjugate,
    ``NLS.ComplexAnalysis.exists_zero_of_continuousOn_integral_eq_zero,
    ``NLS.ComplexAnalysis.integral_cosineGapPoint_eq_zero_of_zero_period,
    ``NLS.ComplexAnalysis.exists_gap_zero_of_real_zero_period,
    ``NLS.ComplexAnalysis.exists_gap_zero_of_rotated_zero_period,
    ``NLS.ComplexAnalysis.eq_zero_of_collapsed_endpointRoot_period,
    ``NLS.ComplexAnalysis.exists_segment_zero_of_endpointRoot_zero_period,
    ``NLS.ComplexAnalysis.exists_segment_zero_of_deflated_root_period,
    ``NLS.ComplexAnalysis.circleIntegral_eq_of_convex_cut_domain,
    ``NLS.ComplexAnalysis.exists_pos_norm_lower_bound_of_compactSpace,
    ``NLS.FunctionalAnalysis.countableIntervalBox,
    ``NLS.FunctionalAnalysis.isCompact_countableIntervalBox,
    ``NLS.FunctionalAnalysis.intervalBoxFiniteLift,
    ``NLS.FunctionalAnalysis.continuous_intervalBoxFiniteLift,
    ``NLS.FunctionalAnalysis.intervalBoxFiniteProjection,
    ``NLS.FunctionalAnalysis.continuous_intervalBoxFiniteProjection,
    ``NLS.FunctionalAnalysis.intervalBox_projection_lift_fixed,
    ``NLS.FunctionalAnalysis.exists_finite_coordinate_fixed_point,
    ``NLS.FunctionalAnalysis.exists_fixed_point_countableIntervalBox]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`NLS.KdV).isPrefixOf name || (`NLS.Articles.KdVEstimates).isPrefixOf name ||
        (`NLS.ComplexAnalysis.TracePrimitiveFamily).isPrefixOf name ||
        shared.contains name then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      checked := checked + 1
  if checked == 0 then
    throwError "No candidate declarations were audited."
  logInfo m!"KdV foundation: transitive axiom audit passed for {checked} declarations."
