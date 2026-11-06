import NLS.MKdV.MiuraRealCartesianGeneralLocalInverse

/-! # Actual Cartesian local inverses at every original real H1 input

These are full original-L2 / native half-order Banach inverse charts
around arbitrary H1 basepoints. Global inversion, native higher-order
inverse charts and cross-mode Gardner canonicity are separate claims.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem physical_Cartesian_complex_Jacobian_bijective_general_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    Function.Bijective (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)) :=
  miuraCartesianJacobian_bijective_H1 a ha

theorem physical_Cartesian_derivative_equivalence_general_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ L : NLS.Coeff.physicalRealSubmodule 2 ≃L[ℝ] MiuraRealCartesianTarget,
      L.toContinuousLinearMap = fderiv ℝ miuraPhysicalCartesianMap (miuraPhysicalH1L2Point a ha) :=
  exists_miuraPhysicalCartesian_derivative_equiv_H1 a ha

theorem physical_Cartesian_analytic_local_inverse_general_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ P : OpenPartialHomeomorph (NLS.Coeff.physicalRealSubmodule 2) MiuraRealCartesianTarget,
      (P : NLS.Coeff.physicalRealSubmodule 2 → MiuraRealCartesianTarget) = miuraPhysicalCartesianMap ∧
      miuraPhysicalH1L2Point a ha ∈ P.source ∧ AnalyticOnNhd ℝ miuraPhysicalCartesianMap P.source ∧
        AnalyticOnNhd ℝ P.symm P.target :=
  exists_miuraPhysicalCartesian_analytic_chart_H1 a ha

end NLS.Articles.MKdVNLSHierarchies
