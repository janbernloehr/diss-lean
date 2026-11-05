import NLS.MKdV.MiuraCartesianJacobianInvertible

/-! # Actual physical real analytic inverse charts at arbitrary H1 basepoints

The open charts use the original L2 and native half-order real Banach
spaces. The basepoint may be any real H1 profile, with all gaps allowed.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraPhysicalCartesianJacobian_inclusion (a h : Coeff.physicalRealSubmodule 2) :
    ((fderiv ℝ miuraPhysicalCartesianMap a) h).val =
      (fderiv ℂ miuraPositiveCartesianMap a.val) h.val := by
  let I : MiuraRealCartesianTarget →L[ℝ] MiuraPositiveCartesianTarget := miuraCartesianRealSubmodule.subtypeL
  have hI : HasFDerivAt (I : MiuraRealCartesianTarget → MiuraPositiveCartesianTarget) I (miuraPhysicalCartesianMap a) := I.hasFDerivAt
  have hd := @HasFDerivAt.comp ℝ inferInstance
    (Coeff.physicalRealSubmodule 2) inferInstance inferInstance
    MiuraRealCartesianTarget inferInstance miuraRealCartesianTargetNormedSpace
    MiuraPositiveCartesianTarget inferInstance inferInstance
    miuraPhysicalCartesianMap (fderiv ℝ miuraPhysicalCartesianMap a) a
    (I : MiuraRealCartesianTarget → MiuraPositiveCartesianTarget) I hI
    (analyticAt_miuraPhysicalCartesianMap a).differentiableAt.hasFDerivAt
  have hc := ((analyticAt_miuraPositiveCartesianMap a.val a.property).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp
    a (Coeff.physicalRealSubmodule 2).subtypeL.hasFDerivAt
  have he : (fun b : Coeff.physicalRealSubmodule 2 => (miuraPhysicalCartesianMap b).val) =
      (fun b => miuraPositiveCartesianMap b.val) := funext miuraPhysicalCartesianMap_inclusion
  change HasFDerivAt (fun b : Coeff.physicalRealSubmodule 2 => (miuraPhysicalCartesianMap b).val) _ a at hd
  change HasFDerivAt (fun b : Coeff.physicalRealSubmodule 2 => miuraPositiveCartesianMap b.val) _ a at hc
  rw [he] at hd
  exact congrArg (fun L : Coeff.physicalRealSubmodule 2 →L[ℝ] MiuraPositiveCartesianTarget => L h) (hd.unique hc)

def miuraPhysicalH1L2Point (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) : Coeff.physicalRealSubmodule 2 :=
  ⟨scalarInclusion a,fun j => by simpa only [scalarInclusion_apply] using ha j⟩

theorem miuraPhysicalCartesianJacobian_injective_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    Function.Injective (fderiv ℝ miuraPhysicalCartesianMap (miuraPhysicalH1L2Point a ha)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro h hh
  apply Subtype.ext
  have hz := congrArg Subtype.val hh
  rw [miuraPhysicalCartesianJacobian_inclusion] at hz
  change (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)) h.val = 0 at hz
  apply (miuraCartesianJacobian_bijective_H1 a ha).1
  exact hz.trans (map_zero _).symm

theorem miuraPhysicalCartesianJacobian_bijective_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    Function.Bijective (fderiv ℝ miuraPhysicalCartesianMap (miuraPhysicalH1L2Point a ha)) :=
  (miuraPhysicalCartesianJacobian_bijective_iff_injective _).2 (miuraPhysicalCartesianJacobian_injective_H1 a ha)

theorem exists_miuraPhysicalCartesian_derivative_equiv_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ L : Coeff.physicalRealSubmodule 2 ≃L[ℝ] MiuraRealCartesianTarget,
      L.toContinuousLinearMap = fderiv ℝ miuraPhysicalCartesianMap (miuraPhysicalH1L2Point a ha) :=
  exists_miuraPhysicalCartesian_derivative_equiv_of_injective _ (miuraPhysicalCartesianJacobian_injective_H1 a ha)

/-- No derivative-injectivity premise remains: each physical H1 profile
has a genuine real analytic local inverse on full original-L2 neighborhoods. -/
theorem exists_miuraPhysicalCartesian_analytic_chart_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ P : OpenPartialHomeomorph (Coeff.physicalRealSubmodule 2) MiuraRealCartesianTarget,
      (P : Coeff.physicalRealSubmodule 2 → MiuraRealCartesianTarget) = miuraPhysicalCartesianMap ∧
      miuraPhysicalH1L2Point a ha ∈ P.source ∧ AnalyticOnNhd ℝ miuraPhysicalCartesianMap P.source ∧
        AnalyticOnNhd ℝ P.symm P.target :=
  exists_miuraPhysicalCartesian_analytic_chart_of_derivative_injective _ (miuraPhysicalCartesianJacobian_injective_H1 a ha)

end NLS.MKdV
