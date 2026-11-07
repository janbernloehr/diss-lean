import NLS.KdV.HillCanonicalCartesianFirstVariation
import NLS.KdV.HillFreeCanonicalActionAmplitude
import NLS.KdV.HillActionAngleCartesian

/-! The actual action-normalized Cartesian coordinate differential at
zero, with both signed Fourier modes and the exact positive amplitude. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

theorem fderiv_hillHminusActionAngleFactorPlus_zero_mean_zero (n : ℕ+)
    (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ (hillHminusActionAngleFactorPlus n) 0) h=
      h.val (-(n:ℤ))/((Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusActionAmplitudeDomain 0 hr
  have hA := (analyticOnNhd_hillHminusCanonicalActionAmplitude n 0 h0).differentiableAt
  have hB := (analyticOnNhd_hillHminusAbelianCartesianPlus n 0
    (hillHminusOffIndexBoundedDomain_subset_analytic (hillHminusActionAmplitudeDomain_subset_bounded h0))).differentiableAt
  have hz := (hillHminusAbelianCartesian_zero_of_real_closed_gap n 0 hr
    (hillHminusCanonicalGapSquare_zero n)).1
  have hd := fderiv_mul_apply_of_right_zero (hillHminusCanonicalActionAmplitude n)
    (hillHminusAbelianCartesianPlus n) 0 h hA hB hz
  change (fderiv ℂ (hillHminusActionAngleFactorPlus n) 0) h = _ at hd
  rw [hd,hillHminusCanonicalActionAmplitude_zero,
    fderiv_hillHminusAbelianCartesianPlus_zero_mean_zero n h hh]
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

theorem fderiv_hillHminusActionAngleFactorMinus_zero_mean_zero (n : ℕ+)
    (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ (hillHminusActionAngleFactorMinus n) 0) h=
      h.val (n:ℤ)/((Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusActionAmplitudeDomain 0 hr
  have hA := (analyticOnNhd_hillHminusCanonicalActionAmplitude n 0 h0).differentiableAt
  have hB := (analyticOnNhd_hillHminusAbelianCartesianMinus n 0
    (hillHminusOffIndexBoundedDomain_subset_analytic (hillHminusActionAmplitudeDomain_subset_bounded h0))).differentiableAt
  have hz := (hillHminusAbelianCartesian_zero_of_real_closed_gap n 0 hr
    (hillHminusCanonicalGapSquare_zero n)).2
  have hd := fderiv_mul_apply_of_right_zero (hillHminusCanonicalActionAmplitude n)
    (hillHminusAbelianCartesianMinus n) 0 h hA hB hz
  change (fderiv ℂ (hillHminusActionAngleFactorMinus n) 0) h = _ at hd
  rw [hd,hillHminusCanonicalActionAmplitude_zero,
    fderiv_hillHminusAbelianCartesianMinus_zero_mean_zero n h hh]
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

theorem fderiv_hillHminusActionAngleX_zero_mean_zero (n : ℕ+)
    (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ (hillHminusActionAngleX n) 0) h=
      (h.val (-(n:ℤ))+h.val (n:ℤ))/((2)*((Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusActionAmplitudeDomain 0 hr
  have hP := (analyticOnNhd_hillHminusActionAngleFactorPlus n 0 h0).differentiableAt.hasFDerivAt
  have hM := (analyticOnNhd_hillHminusActionAngleFactorMinus n 0 h0).differentiableAt.hasFDerivAt
  have hd := ((hP.add hM).fun_mul (hasFDerivAt_const ((2:ℂ)⁻¹) (0:PeriodOneHminusOne))).fderiv
  change fderiv ℂ (fun q => (hillHminusActionAngleFactorPlus n q+hillHminusActionAngleFactorMinus n q)*(2:ℂ)⁻¹) 0 = _ at hd
  unfold hillHminusActionAngleX
  simp only [div_eq_mul_inv]
  rw [hd]
  simp only [smul_apply,smul_eq_mul,add_apply,zero_apply,mul_zero,zero_add]
  rw [fderiv_hillHminusActionAngleFactorPlus_zero_mean_zero n h hh,
    fderiv_hillHminusActionAngleFactorMinus_zero_mean_zero n h hh]
  ring

theorem fderiv_hillHminusActionAngleY_zero_mean_zero (n : ℕ+)
    (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ (hillHminusActionAngleY n) 0) h=
      (h.val (-(n:ℤ))-h.val (n:ℤ))/((2*I)*((Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusActionAmplitudeDomain 0 hr
  have hP := (analyticOnNhd_hillHminusActionAngleFactorPlus n 0 h0).differentiableAt.hasFDerivAt
  have hM := (analyticOnNhd_hillHminusActionAngleFactorMinus n 0 h0).differentiableAt.hasFDerivAt
  have hd := ((hP.sub hM).fun_mul (hasFDerivAt_const ((2*I:ℂ)⁻¹) (0:PeriodOneHminusOne))).fderiv
  change fderiv ℂ (fun q => (hillHminusActionAngleFactorPlus n q-hillHminusActionAngleFactorMinus n q)*(2*I:ℂ)⁻¹) 0 = _ at hd
  unfold hillHminusActionAngleY
  simp only [div_eq_mul_inv]
  rw [hd]
  simp only [smul_apply,smul_eq_mul,add_apply,sub_apply,zero_apply,mul_zero,zero_add]
  rw [fderiv_hillHminusActionAngleFactorPlus_zero_mean_zero n h hh,
    fderiv_hillHminusActionAngleFactorMinus_zero_mean_zero n h hh]
  ring

end NLS.KdV
