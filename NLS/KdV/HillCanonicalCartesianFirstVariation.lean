import NLS.KdV.HillPhysicalDiagonalFirstVariation
import NLS.KdV.HillAbelianCartesian

/-! Exact free differential of the intrinsic diagonal and complete Abelian
Cartesian factors. The complete infinite phase is retained throughout. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

theorem fderiv_hillHminusDiagonalCartesianPlus_zero_mean_zero (n : ℕ+)
    (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ (hillHminusDiagonalCartesianPlus n) 0) h=2*h.val (-(n:ℤ)) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  obtain ⟨P,h0,_⟩ := exists_hillProductEquationPatch 0 hr
  obtain ⟨r,hrpos,_,heq⟩ := exists_common_intrinsic_diagonal_Cartesian_patch_ball P 0 h0 hr
  have he : hillHminusDiagonalCartesianPlus n =ᶠ[𝓝 0] P.physicalOnIndexCartesianPlus n := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hrpos)] with a ha
    exact (heq n a ha).1
  rw [he.fderiv_eq]
  exact P.fderiv_physicalOnIndexCartesianPlus_zero_mean_zero h0 n h hh

theorem fderiv_hillHminusDiagonalCartesianMinus_zero_mean_zero (n : ℕ+)
    (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ (hillHminusDiagonalCartesianMinus n) 0) h=2*h.val (n:ℤ) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  obtain ⟨P,h0,_⟩ := exists_hillProductEquationPatch 0 hr
  obtain ⟨r,hrpos,_,heq⟩ := exists_common_intrinsic_diagonal_Cartesian_patch_ball P 0 h0 hr
  have he : hillHminusDiagonalCartesianMinus n =ᶠ[𝓝 0] P.physicalOnIndexCartesianMinus n := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hrpos)] with a ha
    exact (heq n a ha).2
  rw [he.fderiv_eq]
  exact P.fderiv_physicalOnIndexCartesianMinus_zero_mean_zero h0 n h hh

theorem fderiv_hillHminusAbelianCartesianPlus_zero_mean_zero (n : ℕ+)
    (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ (hillHminusAbelianCartesianPlus n) 0) h=2*h.val (-(n:ℤ)) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusOffIndexAnalyticDomain 0 hr
  have hd := (analyticOnNhd_hillHminusDiagonalCartesianPlus n 0
    (hillHminusOffIndexAnalyticDomain_subset_physical h0)).differentiableAt
  have hc : DifferentiableAt ℂ (fun q => Complex.exp (I*hillHminusOffIndexAbelianCorrection n q)) 0 :=
    (analyticAt_const.mul (analyticOnNhd_hillHminusOffIndexAbelianCorrection n 0 h0)).cexp.differentiableAt
  have hz := (hillHminusDiagonalCartesian_zero_of_real_closed_gap n 0 hr
    (hillHminusCanonicalGapSquare_zero n)).1
  have hb := fderiv_mul_apply_of_left_zero (hillHminusDiagonalCartesianPlus n)
    (fun q => Complex.exp (I*hillHminusOffIndexAbelianCorrection n q)) 0 h hd hc hz
  change (fderiv ℂ (hillHminusAbelianCartesianPlus n) 0) h = _ at hb
  rw [hb,fderiv_hillHminusDiagonalCartesianPlus_zero_mean_zero n h hh,
    hillHminusOffIndexAbelianCorrection_zero,mul_zero,Complex.exp_zero,mul_one]

theorem fderiv_hillHminusAbelianCartesianMinus_zero_mean_zero (n : ℕ+)
    (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ (hillHminusAbelianCartesianMinus n) 0) h=2*h.val (n:ℤ) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusOffIndexAnalyticDomain 0 hr
  have hd := (analyticOnNhd_hillHminusDiagonalCartesianMinus n 0
    (hillHminusOffIndexAnalyticDomain_subset_physical h0)).differentiableAt
  have hc : DifferentiableAt ℂ (fun q => Complex.exp (-I*hillHminusOffIndexAbelianCorrection n q)) 0 :=
    (analyticAt_const.mul (analyticOnNhd_hillHminusOffIndexAbelianCorrection n 0 h0)).cexp.differentiableAt
  have hz := (hillHminusDiagonalCartesian_zero_of_real_closed_gap n 0 hr
    (hillHminusCanonicalGapSquare_zero n)).2
  have hb := fderiv_mul_apply_of_left_zero (hillHminusDiagonalCartesianMinus n)
    (fun q => Complex.exp (-I*hillHminusOffIndexAbelianCorrection n q)) 0 h hd hc hz
  change (fderiv ℂ (hillHminusAbelianCartesianMinus n) 0) h = _ at hb
  rw [hb,fderiv_hillHminusDiagonalCartesianMinus_zero_mean_zero n h hh,
    hillHminusOffIndexAbelianCorrection_zero,mul_zero,Complex.exp_zero,mul_one]

end NLS.KdV
