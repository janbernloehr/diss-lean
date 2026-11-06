import NLS.MKdV.MiuraCartesianJacobianCompact
import NLS.MKdV.MiuraRealCartesianMap

/-! # Compact Jacobian remainder on the physical real source and target -/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem fderiv_miuraPhysicalCartesianMap (a : Coeff.physicalRealSubmodule 2) :
    fderiv ℝ miuraPhysicalCartesianMap a = miuraCartesianRealProjection.comp
      (((fderiv ℂ miuraPositiveCartesianMap a.val).restrictScalars ℝ).comp
        (Coeff.physicalRealSubmodule 2).subtypeL) := by
  exact (@NLS.ComplexAnalysis.hasFDerivAt_real_linear_transport
    (Coeff.physicalRealSubmodule 2) (Coeff 2) MiuraPositiveCartesianTarget MiuraRealCartesianTarget
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Coeff.physicalRealSubmodule 2).subtypeL miuraCartesianRealProjection miuraPositiveCartesianMap a
    (analyticAt_miuraPositiveCartesianMap a.val a.property).differentiableAt).fderiv

theorem miuraCartesianRealFreeEquiv_projection :
    miuraCartesianRealProjection.comp
      ((miuraCartesianFreeJacobian.restrictScalars ℝ).comp (Coeff.physicalRealSubmodule 2).subtypeL) =
        miuraCartesianRealFreeEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro a
  exact miuraCartesianRealProjection_real (miuraCartesianRealFreeJacobian a)

/-- At every physical real profile, the actual real derivative differs
from the free real Banach equivalence by a compact operator. -/
theorem isCompactOperator_miuraPhysicalCartesianJacobian_sub_free
    (a : Coeff.physicalRealSubmodule 2) :
    IsCompactOperator (fderiv ℝ miuraPhysicalCartesianMap a-
      miuraCartesianRealFreeEquiv.toContinuousLinearMap) := by
  have hR : IsCompactOperator
      ((fderiv ℂ miuraPositiveCartesianMap a.val-miuraCartesianFreeJacobian).restrictScalars ℝ) :=
    isCompactOperator_miuraCartesianJacobian_sub_free a.val a.property
  have hc := (hR.comp_clm (Coeff.physicalRealSubmodule 2).subtypeL).clm_comp miuraCartesianRealProjection
  have he : fderiv ℝ miuraPhysicalCartesianMap a-miuraCartesianRealFreeEquiv.toContinuousLinearMap =
      miuraCartesianRealProjection.comp
        (((fderiv ℂ miuraPositiveCartesianMap a.val-miuraCartesianFreeJacobian).restrictScalars ℝ).comp
          (Coeff.physicalRealSubmodule 2).subtypeL) := by
    rw [fderiv_miuraPhysicalCartesianMap,← miuraCartesianRealFreeEquiv_projection]
    apply ContinuousLinearMap.ext
    intro b
    exact (map_sub miuraCartesianRealProjection _ _).symm
  rw [he]
  exact hc

end NLS.MKdV
