import NLS.FunctionalAnalysis.ComplexRealEquiv
import NLS.Dynamics.ComplexBirkhoffCoordinatesExponent
import NLS.Dynamics.ConjugatePairEquiv
import NLS.Poisson.ComplexCanonicalCoordinates
import NLS.ZakharovShabat.SourceRealBallCoreIdentity
import NLS.ZakharovShabat.SourceComplexBirkhoffCanonical
import NLS.ZakharovShabat.SobolevHierarchySymmetries
import NLS.MKdV.HierarchyRestriction
import NLS.ZakharovShabat.ClassicalNLSFourthHamiltonian
import NLS.ZakharovShabat.ClassicalNLSFourthVariation
import NLS.MKdV.ClassicalEnergyVariation
import NLS.MKdV.ClassicalFourthFlowRestriction
import NLS.Articles.MKdVBelowL2.SmoothRenormalization
import NLS.Articles.MKdVBelowL2.TranslationFourier
import NLS.Articles.MKdVBelowL2.PhysicalBirkhoff
import NLS.Articles.MKdVBelowL2.CompatibleBirkhoffFamily
import NLS.Articles.MKdVBelowL2.PhysicalBirkhoffCanonical
import NLS.Articles.MKdVBelowL2.HilbertBirkhoffIdentification
import NLS.Articles.MKdVBelowL2.RealBirkhoffFamily
import NLS.Articles.MKdVBelowL2.Theorem12
import NLS.Articles.MKdVBelowL2.ClassicalRenormalizedFourthFlow
import NLS.Articles.MKdVBelowL2.FourthMomentSummability

#print axioms NLS.FunctionalAnalysis.complexRealEquiv
#print axioms NLS.FunctionalAnalysis.complexRealEquiv_apply
#print axioms NLS.FunctionalAnalysis.complexRealEquiv_symm_apply
#print axioms NLS.Birkhoff.rectangularToComplex_exponent
#print axioms NLS.Birkhoff.conjugatePairSubmodule
#print axioms NLS.Birkhoff.conjugatePairEquiv
#print axioms NLS.Birkhoff.conjugatePairEquiv_val
#print axioms NLS.Birkhoff.isClosed_conjugatePairSubmodule
#print axioms NLS.Birkhoff.conjugatePairCompleteSpace
#print axioms NLS.Poisson.complexMinusCotangent
#print axioms NLS.Poisson.complexPlusCotangent
#print axioms NLS.Poisson.complexCoordinateScale_square
#print axioms NLS.Poisson.complex_canonical_of_rectangular
#print axioms NLS.Poisson.RegularSourceCotangent.bivector_eq_sourceBivector
#print axioms NLS.ZakharovShabat.eqOn_sourceRealBallCore_of_real_agreement
#print axioms NLS.ZakharovShabat.SourceBirkhoffMapComplexData.complex_map_regular_canonical
#print axioms NLS.ZakharovShabat.SourceBirkhoffMapComplexData.complex_coordinates_analytic
#print axioms NLS.ZakharovShabat.SourceBirkhoffMapComplexData.complex_map_canonical_on_core
#print axioms NLS.ZakharovShabat.hierarchyComponentSwap
#print axioms NLS.ZakharovShabat.hierarchyComponentSwap_apply
#print axioms NLS.ZakharovShabat.sobolevNLSHamiltonian_neg
#print axioms NLS.ZakharovShabat.sobolevNLSHamiltonian_swap
#print axioms NLS.ZakharovShabat.fderiv_sobolevNLSHamiltonian_swap
#print axioms NLS.ZakharovShabat.hierarchyReciprocalScaling
#print axioms NLS.ZakharovShabat.hierarchyReciprocalScaling_apply
#print axioms NLS.ZakharovShabat.fderiv_sobolevNLSHamiltonian_reciprocal_scaling
#print axioms NLS.MKdV.hierarchyDiagonal
#print axioms NLS.MKdV.hierarchyDiagonal_apply
#print axioms NLS.MKdV.diagonalNLSHamiltonian
#print axioms NLS.MKdV.analyticAt_diagonalNLSHamiltonian
#print axioms NLS.MKdV.diagonalNLSHamiltonian_even_eq_zero
#print axioms NLS.MKdV.diagonalNLSHamiltonian_one
#print axioms NLS.MKdV.classicalMKdVMass
#print axioms NLS.MKdV.classicalMKdVEnergy
#print axioms NLS.MKdV.classicalNLSHamiltonian_one_diagonal
#print axioms NLS.MKdV.classicalNLSHamiltonian_three_diagonal
#print axioms NLS.ZakharovShabat.nlsRiccatiDensity_three
#print axioms NLS.ZakharovShabat.classicalNLSHamiltonian_four
#print axioms NLS.ZakharovShabat.classicalNLSFourthGradient
#print axioms NLS.ZakharovShabat.classicalNLSHamiltonian_four_swap
#print axioms NLS.ZakharovShabat.classicalNLSHamiltonian_four_variation_fst
#print axioms NLS.ZakharovShabat.hasDerivAt_classicalNLSHamiltonian_four_fst
#print axioms NLS.ZakharovShabat.hasDerivAt_classicalNLSHamiltonian_four_snd
#print axioms NLS.MKdV.classicalMKdVEnergyGradient
#print axioms NLS.MKdV.classicalMKdVEnergy_variation
#print axioms NLS.MKdV.hasDerivAt_classicalMKdVEnergy
#print axioms NLS.MKdV.deriv_classicalMKdVEnergyGradient
#print axioms NLS.MKdV.classicalNLSFourthVectorField
#print axioms NLS.MKdV.classicalNLSFourthVectorField_formula
#print axioms NLS.MKdV.classicalNLSFourthVectorField_diagonal
#print axioms NLS.Articles.MKdVBelowL2.originalDifferential
#print axioms NLS.Articles.MKdVBelowL2.hasDerivAt_renormalizing_translation
#print axioms NLS.Articles.MKdVBelowL2.renormalizedDifferential
#print axioms NLS.Articles.MKdVBelowL2.hasDerivAt_original_translation
#print axioms NLS.Articles.MKdVBelowL2.coefficient_renormalizing_translation
#print axioms NLS.Articles.MKdVBelowL2.coefficient_original_translation
#print axioms NLS.Articles.MKdVBelowL2.PhysicalFL
#print axioms NLS.Articles.MKdVBelowL2.physicalCoefficients
#print axioms NLS.Articles.MKdVBelowL2.physicalCoefficients_apply
#print axioms NLS.Articles.MKdVBelowL2.physicalBirkhoff
#print axioms NLS.Articles.MKdVBelowL2.physicalBirkhoff_analytic
#print axioms NLS.Articles.MKdVBelowL2.physicalBirkhoff_action
#print axioms NLS.Articles.MKdVBelowL2.exists_physicalBirkhoff
#print axioms NLS.Articles.MKdVBelowL2.physicalRealSubspace
#print axioms NLS.Articles.MKdVBelowL2.PhysicalRealInput
#print axioms NLS.Articles.MKdVBelowL2.isClosed_physicalRealSubspace
#print axioms NLS.Articles.MKdVBelowL2.physicalRealInputCompleteSpace
#print axioms NLS.Articles.MKdVBelowL2.physicalRealCoefficientsCL
#print axioms NLS.Articles.MKdVBelowL2.physicalRealCoefficientsCL_val
#print axioms NLS.Articles.MKdVBelowL2.physicalRealCoefficients
#print axioms NLS.Articles.MKdVBelowL2.physicalRealBirkhoff
#print axioms NLS.Articles.MKdVBelowL2.range_physicalRealBirkhoff
#print axioms NLS.Articles.MKdVBelowL2.physicalRealBirkhoff_geometry
#print axioms NLS.Articles.MKdVBelowL2.physicalBirkhoff_real
#print axioms NLS.Articles.MKdVBelowL2.physicalBirkhoff_real_action
#print axioms NLS.Articles.MKdVBelowL2.physicalRealBirkhoff_surjective
#print axioms NLS.Articles.MKdVBelowL2.physicalRealBirkhoff_isOpenEmbedding
#print axioms NLS.Articles.MKdVBelowL2.exists_physicalRealBirkhoff_geometry
#print axioms NLS.Articles.MKdVBelowL2.physicalRealBirkhoff_analytic
#print axioms NLS.Articles.MKdVBelowL2.physicalRealBirkhoff_localInverse
#print axioms NLS.Articles.MKdVBelowL2.OriginalBirkhoffChart
#print axioms NLS.Articles.MKdVBelowL2.exists_originalBirkhoffChart
#print axioms NLS.Articles.MKdVBelowL2.originalBirkhoffChart
#print axioms NLS.Articles.MKdVBelowL2.compatibleBirkhoffDomain
#print axioms NLS.Articles.MKdVBelowL2.compatibleBirkhoff
#print axioms NLS.Articles.MKdVBelowL2.compatibleBirkhoffDomain_open_real
#print axioms NLS.Articles.MKdVBelowL2.compatibleBirkhoff_analytic
#print axioms NLS.Articles.MKdVBelowL2.physicalCoefficients_exponent_of_same_distributions
#print axioms NLS.Articles.MKdVBelowL2.compatibleBirkhoff_eq_on_intersection
#print axioms NLS.Articles.MKdVBelowL2.compatibleBirkhoff_coordinates_on_intersection
#print axioms NLS.Articles.MKdVBelowL2.compatibleBirkhoff_zero
#print axioms NLS.Articles.MKdVBelowL2.compatibleBirkhoff_canonical
#print axioms NLS.Articles.MKdVBelowL2.physicalFLBracket
#print axioms NLS.Articles.MKdVBelowL2.compatibleBirkhoff_canonical_complex
#print axioms NLS.Articles.MKdVBelowL2.physicalHilbertRealization
#print axioms NLS.Articles.MKdVBelowL2.physicalHilbertRealization_val
#print axioms NLS.Articles.MKdVBelowL2.physicalHilbertRealization_coefficients
#print axioms NLS.Articles.MKdVBelowL2.compatibleBirkhoff_eq_intrinsic
#print axioms NLS.Articles.MKdVBelowL2.physicalHilbertPairEquiv
#print axioms NLS.Articles.MKdVBelowL2.physicalFLBracket_eq_integral_bracket
#print axioms NLS.Articles.MKdVBelowL2.realBirkhoffFamily
#print axioms NLS.Articles.MKdVBelowL2.realBirkhoffFamily_val
#print axioms NLS.Articles.MKdVBelowL2.realBirkhoffFamily_geometry
#print axioms NLS.Articles.MKdVBelowL2.realBirkhoffFamily_localInverse
#print axioms NLS.Articles.MKdVBelowL2.realBirkhoffFamily_surjective
#print axioms NLS.Articles.MKdVBelowL2.realBirkhoffFamily_globalInverse
#print axioms NLS.Articles.MKdVBelowL2.theorem1_2_at_exponent
#print axioms NLS.Articles.MKdVBelowL2.theorem1_2_compatible
#print axioms NLS.Articles.MKdVBelowL2.theorem1_2_hilbert
#print axioms NLS.Articles.MKdVBelowL2.theorem1_2_hilbert_globalInverse
#print axioms NLS.Articles.MKdVBelowL2.classicalRenormalizedFourthField
#print axioms NLS.Articles.MKdVBelowL2.classicalRenormalizedFourthField_diagonal
#print axioms NLS.Articles.MKdVBelowL2.classicalRenormalizedFourthField_gardner
#print axioms NLS.Articles.MKdVBelowL2.exists_summable_cube
#print axioms NLS.Articles.MKdVBelowL2.norm_index_ratio_le
#print axioms NLS.Articles.MKdVBelowL2.summable_weighted_moment_of_row
#print axioms NLS.Articles.MKdVBelowL2.exists_weighted_moment_summable
#print axioms NLS.Articles.MKdVBelowL2.fourthFrequencyCandidate
#print axioms NLS.Articles.MKdVBelowL2.exists_fourthFrequencyCandidate
#print axioms NLS.Articles.MKdVBelowL2.fourthFrequencyCandidate_eq_of_coefficients
