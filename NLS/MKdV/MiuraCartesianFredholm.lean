import NLS.MKdV.MiuraRealCartesianJacobianCompact
import NLS.FunctionalAnalysis.CompactPerturbationEquivalence

/-! # The Fredholm reduction for the actual Cartesian derivative

The compact decomposition reduces Banach invertibility to a zero-kernel
proof, on both the full complex source and the physical real spaces.
The injectivity premise is explicit; it is not supplied by compactness.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraCartesianNormalizedJacobian (a : Coeff 2) : Coeff 2 →L[ℂ] Coeff 2 :=
  miuraCartesianFreeInverse.comp (fderiv ℂ miuraPositiveCartesianMap a)

theorem isCompactOperator_miuraCartesianNormalizedJacobian_sub_id (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    IsCompactOperator (miuraCartesianNormalizedJacobian a-ContinuousLinearMap.id ℂ (Coeff 2)) := by
  have he : miuraCartesianNormalizedJacobian a-ContinuousLinearMap.id ℂ (Coeff 2) =
      miuraCartesianFreeInverse.comp (fderiv ℂ miuraPositiveCartesianMap a-miuraCartesianFreeJacobian) := by
    apply ContinuousLinearMap.ext
    intro h
    change miuraCartesianFreeInverse (fderiv ℂ miuraPositiveCartesianMap a h)-h =
      miuraCartesianFreeInverse (fderiv ℂ miuraPositiveCartesianMap a h-miuraCartesianFreeJacobian h)
    rw [map_sub,miuraCartesianFreeInverse_jacobian]
  rw [he]
  exact (isCompactOperator_miuraCartesianJacobian_sub_free a ha).clm_comp miuraCartesianFreeInverse

theorem miuraCartesianJacobian_bijective_iff_injective (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    Function.Bijective (fderiv ℂ miuraPositiveCartesianMap a) ↔
      Function.Injective (fderiv ℂ miuraPositiveCartesianMap a) := by
  refine ⟨fun h => h.1,fun h => ?_⟩
  exact NLS.FunctionalAnalysis.bijective_of_injective_of_compact_sub_equiv
    miuraCartesianFreeEquiv (fderiv ℂ miuraPositiveCartesianMap a)
    (isCompactOperator_miuraCartesianJacobian_sub_free a ha) h

theorem miuraPhysicalCartesianJacobian_bijective_iff_injective
    (a : Coeff.physicalRealSubmodule 2) :
    Function.Bijective (fderiv ℝ miuraPhysicalCartesianMap a) ↔
      Function.Injective (fderiv ℝ miuraPhysicalCartesianMap a) := by
  refine ⟨fun h => h.1,fun h => ?_⟩
  exact @NLS.FunctionalAnalysis.bijective_of_injective_of_compact_sub_equiv
    ℝ (Coeff.physicalRealSubmodule 2) MiuraRealCartesianTarget
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    miuraCartesianRealFreeEquiv (fderiv ℝ miuraPhysicalCartesianMap a)
    (isCompactOperator_miuraPhysicalCartesianJacobian_sub_free a) h

theorem exists_miuraPhysicalCartesian_derivative_equiv_of_injective
    (a : Coeff.physicalRealSubmodule 2)
    (hinj : Function.Injective (fderiv ℝ miuraPhysicalCartesianMap a)) :
    ∃ L : Coeff.physicalRealSubmodule 2 ≃L[ℝ] MiuraRealCartesianTarget,
      L.toContinuousLinearMap = fderiv ℝ miuraPhysicalCartesianMap a := by
  exact @NLS.FunctionalAnalysis.exists_equiv_of_injective_of_compact_sub_equiv
    ℝ (Coeff.physicalRealSubmodule 2) MiuraRealCartesianTarget
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    miuraCartesianRealFreeEquiv (fderiv ℝ miuraPhysicalCartesianMap a)
    (isCompactOperator_miuraPhysicalCartesianJacobian_sub_free a) hinj

theorem exists_miuraPhysicalCartesian_analytic_chart_of_derivative_injective
    (a : Coeff.physicalRealSubmodule 2)
    (hinj : Function.Injective (fderiv ℝ miuraPhysicalCartesianMap a)) :
    ∃ P : OpenPartialHomeomorph (Coeff.physicalRealSubmodule 2) MiuraRealCartesianTarget,
      (P : Coeff.physicalRealSubmodule 2 → MiuraRealCartesianTarget) = miuraPhysicalCartesianMap ∧
      a ∈ P.source ∧ AnalyticOnNhd ℝ miuraPhysicalCartesianMap P.source ∧
        AnalyticOnNhd ℝ P.symm P.target := by
  obtain ⟨L,hL⟩ := exists_miuraPhysicalCartesian_derivative_equiv_of_injective a hinj
  exact @NLS.ComplexAnalysis.exists_real_analytic_openPartialHomeomorph_of_fderiv_equiv
    (Coeff.physicalRealSubmodule 2) MiuraRealCartesianTarget
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    miuraPhysicalCartesianMap a (analyticAt_miuraPhysicalCartesianMap a) L hL.symm

end NLS.MKdV
