import NLS.MKdV.MiuraSobolevCartesianJacobianInvertible

/-! # Real native Cartesian derivatives and analytic inverse charts

The actual real derivative has the same compact free remainder and is
injective by its complex inclusion. This proves real analytic inverse
charts in the full native norms at every physical profile of order s>=1.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem fderiv_miuraPhysicalSobolevCartesianMap (s : ℕ) (a : MiuraRealSobolevSource s) :
    fderiv ℝ (miuraPhysicalSobolevCartesianMap s) a = (miuraSobolevCartesianRealProjection s).comp
      (((fderiv ℂ (miuraSobolevPositiveCartesianMap s) a.val).restrictScalars ℝ).comp
        (MiuraRealSobolevSource s).subtypeL) := by
  exact (@NLS.ComplexAnalysis.hasFDerivAt_real_linear_transport
    (MiuraRealSobolevSource s) (ScalarSobolev s) (MiuraPositiveSobolevTarget s) (MiuraRealSobolevCartesianTarget s)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (MiuraRealSobolevSource s).subtypeL (miuraSobolevCartesianRealProjection s) (miuraSobolevPositiveCartesianMap s) a
    (analyticAt_miuraSobolevPositiveCartesianMap s a.val a.property).differentiableAt).fderiv

theorem miuraSobolevCartesianRealFreeEquiv_projection (s : ℕ) :
    (miuraSobolevCartesianRealProjection s).comp
      (((miuraSobolevCartesianFreeEquiv s).toContinuousLinearMap.restrictScalars ℝ).comp
        (MiuraRealSobolevSource s).subtypeL) = (miuraSobolevCartesianRealFreeEquiv s).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro a
  change miuraSobolevCartesianRealProjection s (miuraSobolevCartesianFreeEquiv s a.val) = _
  rw [← miuraSobolevCartesianRealFreeEquiv_inclusion s a]
  exact miuraSobolevCartesianRealProjection_real s _

theorem isCompactOperator_miuraPhysicalSobolevCartesianJacobian_sub_free
    (s : ℕ) (a : MiuraRealSobolevSource s) :
    IsCompactOperator (fderiv ℝ (miuraPhysicalSobolevCartesianMap s) a-
      (miuraSobolevCartesianRealFreeEquiv s).toContinuousLinearMap) := by
  have hR : IsCompactOperator
      ((fderiv ℂ (miuraSobolevPositiveCartesianMap s) a.val-
        (miuraSobolevCartesianFreeEquiv s).toContinuousLinearMap).restrictScalars ℝ) :=
    isCompactOperator_miuraSobolevCartesianJacobian_sub_free s a.val a.property
  have hc := (hR.comp_clm (MiuraRealSobolevSource s).subtypeL).clm_comp (miuraSobolevCartesianRealProjection s)
  have he : fderiv ℝ (miuraPhysicalSobolevCartesianMap s) a-
      (miuraSobolevCartesianRealFreeEquiv s).toContinuousLinearMap =
      (miuraSobolevCartesianRealProjection s).comp
        (((fderiv ℂ (miuraSobolevPositiveCartesianMap s) a.val-
          (miuraSobolevCartesianFreeEquiv s).toContinuousLinearMap).restrictScalars ℝ).comp
            (MiuraRealSobolevSource s).subtypeL) := by
    rw [fderiv_miuraPhysicalSobolevCartesianMap,← miuraSobolevCartesianRealFreeEquiv_projection]
    apply ContinuousLinearMap.ext
    intro b
    exact (map_sub (miuraSobolevCartesianRealProjection s) _ _).symm
  rw [he]
  exact hc

theorem miuraPhysicalSobolevCartesianJacobian_inclusion (s : ℕ) (a h : MiuraRealSobolevSource s) :
    ((fderiv ℝ (miuraPhysicalSobolevCartesianMap s) a) h).val =
      (fderiv ℂ (miuraSobolevPositiveCartesianMap s) a.val) h.val := by
  let J : MiuraRealSobolevCartesianTarget s →L[ℝ] MiuraPositiveSobolevTarget s :=
    (miuraSobolevCartesianRealSubmodule s).subtypeL
  have hJ : HasFDerivAt (J : MiuraRealSobolevCartesianTarget s → MiuraPositiveSobolevTarget s) J
      (miuraPhysicalSobolevCartesianMap s a) := J.hasFDerivAt
  have hd := @HasFDerivAt.comp ℝ inferInstance
    (MiuraRealSobolevSource s) inferInstance inferInstance
    (MiuraRealSobolevCartesianTarget s) inferInstance inferInstance
    (MiuraPositiveSobolevTarget s) inferInstance inferInstance
    (miuraPhysicalSobolevCartesianMap s) (fderiv ℝ (miuraPhysicalSobolevCartesianMap s) a) a
    (J : MiuraRealSobolevCartesianTarget s → MiuraPositiveSobolevTarget s) J hJ
    (analyticAt_miuraPhysicalSobolevCartesianMap s a).differentiableAt.hasFDerivAt
  have hc := ((analyticAt_miuraSobolevPositiveCartesianMap s a.val a.property).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp
    a (MiuraRealSobolevSource s).subtypeL.hasFDerivAt
  have he : (fun b : MiuraRealSobolevSource s => (miuraPhysicalSobolevCartesianMap s b).val) =
      (fun b => miuraSobolevPositiveCartesianMap s b.val) := funext (miuraPhysicalSobolevCartesianMap_inclusion s)
  change HasFDerivAt (fun b : MiuraRealSobolevSource s => (miuraPhysicalSobolevCartesianMap s b).val) _ a at hd
  change HasFDerivAt (fun b : MiuraRealSobolevSource s => miuraSobolevPositiveCartesianMap s b.val) _ a at hc
  rw [he] at hd
  exact congrArg (fun L : MiuraRealSobolevSource s →L[ℝ] MiuraPositiveSobolevTarget s => L h) (hd.unique hc)

theorem miuraPhysicalSobolevCartesianJacobian_injective (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    Function.Injective (fderiv ℝ (miuraPhysicalSobolevCartesianMap s) a) := by
  intro h k hhk
  apply Subtype.ext
  apply miuraSobolevCartesianJacobian_injective s hs a.val a.property
  simpa only [miuraPhysicalSobolevCartesianJacobian_inclusion] using congrArg Subtype.val hhk

theorem miuraPhysicalSobolevCartesianJacobian_bijective (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    Function.Bijective (fderiv ℝ (miuraPhysicalSobolevCartesianMap s) a) := by
  exact @NLS.FunctionalAnalysis.bijective_of_injective_of_compact_sub_equiv
    ℝ (MiuraRealSobolevSource s) (MiuraRealSobolevCartesianTarget s)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (miuraSobolevCartesianRealFreeEquiv s) _
    (isCompactOperator_miuraPhysicalSobolevCartesianJacobian_sub_free s a)
    (miuraPhysicalSobolevCartesianJacobian_injective s hs a)

theorem exists_miuraPhysicalSobolevCartesian_derivative_equiv (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    ∃ L : MiuraRealSobolevSource s ≃L[ℝ] MiuraRealSobolevCartesianTarget s,
      L.toContinuousLinearMap = fderiv ℝ (miuraPhysicalSobolevCartesianMap s) a := by
  exact @NLS.FunctionalAnalysis.exists_equiv_of_injective_of_compact_sub_equiv
    ℝ (MiuraRealSobolevSource s) (MiuraRealSobolevCartesianTarget s)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (miuraSobolevCartesianRealFreeEquiv s) _
    (isCompactOperator_miuraPhysicalSobolevCartesianJacobian_sub_free s a)
    (miuraPhysicalSobolevCartesianJacobian_injective s hs a)

/-- Every physical real H^s profile, s>=1, has an actual real analytic
inverse chart in the full native order-(s+1/2) target and signed mean. -/
theorem exists_miuraPhysicalSobolevCartesian_analytic_chart (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    ∃ P : OpenPartialHomeomorph (MiuraRealSobolevSource s) (MiuraRealSobolevCartesianTarget s),
      (P : MiuraRealSobolevSource s → MiuraRealSobolevCartesianTarget s) = miuraPhysicalSobolevCartesianMap s ∧
      a ∈ P.source ∧ AnalyticOnNhd ℝ (miuraPhysicalSobolevCartesianMap s) P.source ∧
        AnalyticOnNhd ℝ P.symm P.target := by
  obtain ⟨L,hL⟩ := exists_miuraPhysicalSobolevCartesian_derivative_equiv s hs a
  exact @NLS.ComplexAnalysis.exists_real_analytic_openPartialHomeomorph_of_fderiv_equiv
    (MiuraRealSobolevSource s) (MiuraRealSobolevCartesianTarget s)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (miuraPhysicalSobolevCartesianMap s) a (analyticAt_miuraPhysicalSobolevCartesianMap s a) L hL.symm

end NLS.MKdV
