import NLS.MKdV.MiuraSobolevCartesianRealForm

/-! # The actual Cartesian maps in the physical real Sobolev norms -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraSobolevPositiveCartesianMap_physicalReal (s : ℕ) (a : MiuraRealSobolevSource s) :
    miuraSobolevPositiveCartesianMap s a.val ∈ miuraSobolevCartesianRealSubmodule s := by
  apply (mem_miuraSobolevCartesianRealSubmodule_iff s _).mpr
  constructor
  · intro n
    have hr := miuraSobolevCartesianSequence_real s a.val a.property n
    change ((WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 (miuraSobolevCartesianSequence s a.val).1).val.val n).im = 0 ∧
      ((WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 (miuraSobolevCartesianSequence s a.val).2).val.val n).im = 0
    rw [WeightedCoeff.positiveProjection_apply,WeightedCoeff.positiveProjection_apply]
    by_cases hn : 0 < n
    · simpa only [if_pos hn] using hr
    · simp only [if_neg hn,Complex.zero_im,and_self]
  · change (a.val.val 0).im = 0
    have he := congrArg Complex.im (a.property 0)
    simp only [neg_zero,Complex.conj_im] at he
    linarith

def miuraPhysicalSobolevCartesianMap (s : ℕ) (a : MiuraRealSobolevSource s) : MiuraRealSobolevCartesianTarget s :=
  miuraSobolevCartesianRealProjection s (miuraSobolevPositiveCartesianMap s a.val)

theorem miuraPhysicalSobolevCartesianMap_inclusion (s : ℕ) (a : MiuraRealSobolevSource s) :
    (miuraPhysicalSobolevCartesianMap s a).val = miuraSobolevPositiveCartesianMap s a.val :=
  congrArg Subtype.val (miuraSobolevCartesianRealProjection_real s
    ⟨miuraSobolevPositiveCartesianMap s a.val,miuraSobolevPositiveCartesianMap_physicalReal s a⟩)

theorem analyticAt_miuraPhysicalSobolevCartesianMap (s : ℕ) (a : MiuraRealSobolevSource s) :
    AnalyticAt ℝ (miuraPhysicalSobolevCartesianMap s) a := by
  exact @analyticAt_real_linear_transport
    (MiuraRealSobolevSource s) (ScalarSobolev s) (MiuraPositiveSobolevTarget s) (MiuraRealSobolevCartesianTarget s)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (MiuraRealSobolevSource s).subtypeL (miuraSobolevCartesianRealProjection s) (miuraSobolevPositiveCartesianMap s) a
    (analyticAt_miuraSobolevPositiveCartesianMap s a.val a.property)

theorem fderiv_miuraPhysicalSobolevCartesianMap_zero (s : ℕ) :
    fderiv ℝ (miuraPhysicalSobolevCartesianMap s) 0 = (miuraSobolevCartesianRealFreeEquiv s).toContinuousLinearMap := by
  have hzero : ∀ j : ℤ, (0 : ScalarSobolev s).val j = conj ((0 : ScalarSobolev s).val (-j)) := by intro j; simp
  have hq := @hasFDerivAt_real_linear_transport
    (MiuraRealSobolevSource s) (ScalarSobolev s) (MiuraPositiveSobolevTarget s) (MiuraRealSobolevCartesianTarget s)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (MiuraRealSobolevSource s).subtypeL (miuraSobolevCartesianRealProjection s) (miuraSobolevPositiveCartesianMap s)
    (0 : MiuraRealSobolevSource s) (analyticAt_miuraSobolevPositiveCartesianMap s 0 hzero).differentiableAt
  have he : (miuraSobolevCartesianRealProjection s).comp
      (((fderiv ℂ (miuraSobolevPositiveCartesianMap s) 0).restrictScalars ℝ).comp (MiuraRealSobolevSource s).subtypeL) =
      (miuraSobolevCartesianRealFreeEquiv s).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro a
    change miuraSobolevCartesianRealProjection s (miuraSobolevCartesianFreeJacobian s a.val) = _
    rw [miuraSobolevCartesianFreeJacobian_eq_equiv]
    change miuraSobolevCartesianRealProjection s (miuraSobolevCartesianFreeEquiv s a.val) = _
    rw [← miuraSobolevCartesianRealFreeEquiv_inclusion s a]
    exact miuraSobolevCartesianRealProjection_real s _
  change HasFDerivAt (miuraPhysicalSobolevCartesianMap s) ((miuraSobolevCartesianRealProjection s).comp
    (((fderiv ℂ (miuraSobolevPositiveCartesianMap s) 0).restrictScalars ℝ).comp (MiuraRealSobolevSource s).subtypeL)) 0 at hq
  rw [he] at hq
  exact hq.fderiv

theorem miuraPhysicalSobolevCartesianMap_zero (s : ℕ) : miuraPhysicalSobolevCartesianMap s 0 = 0 := by
  apply Subtype.ext
  rw [miuraPhysicalSobolevCartesianMap_inclusion]
  exact miuraSobolevPositiveCartesianMap_zero s

end NLS.MKdV
