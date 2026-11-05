import NLS.MKdV.MiuraCartesianFredholm

/-! # General-profile compactness and the remaining Jacobian obligation

The native physical Cartesian derivative has compact remainder from its
free equivalence at every original real L2 source. A derivative-kernel
proof would therefore give genuine analytic local coordinates there.
No kernel assertion is inferred from this reduction alone.
-/
noncomputable section
open Set NLS.MKdV
open scoped ENNReal
namespace NLS.Articles.MKdVNLSHierarchies

theorem physical_Cartesian_derivative_compact_remainder
    (a : NLS.Coeff.physicalRealSubmodule 2) :
    IsCompactOperator (fderiv ℝ miuraPhysicalCartesianMap a-
      miuraCartesianRealFreeEquiv.toContinuousLinearMap) :=
  isCompactOperator_miuraPhysicalCartesianJacobian_sub_free a

theorem physical_Cartesian_derivative_bijective_iff_injective
    (a : NLS.Coeff.physicalRealSubmodule 2) :
    Function.Bijective (fderiv ℝ miuraPhysicalCartesianMap a) ↔
      Function.Injective (fderiv ℝ miuraPhysicalCartesianMap a) :=
  miuraPhysicalCartesianJacobian_bijective_iff_injective a

theorem physical_Cartesian_analytic_chart_of_derivative_injective
    (a : NLS.Coeff.physicalRealSubmodule 2)
    (hinj : Function.Injective (fderiv ℝ miuraPhysicalCartesianMap a)) :
    ∃ P : OpenPartialHomeomorph (NLS.Coeff.physicalRealSubmodule 2) MiuraRealCartesianTarget,
      (P : NLS.Coeff.physicalRealSubmodule 2 → MiuraRealCartesianTarget) = miuraPhysicalCartesianMap ∧
      a ∈ P.source ∧ AnalyticOnNhd ℝ miuraPhysicalCartesianMap P.source ∧
        AnalyticOnNhd ℝ P.symm P.target :=
  exists_miuraPhysicalCartesian_analytic_chart_of_derivative_injective a hinj

end NLS.Articles.MKdVNLSHierarchies
