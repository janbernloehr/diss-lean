import NLS.ZakharovShabat.ClassicalUniformRemainderL2Budget
import NLS.ZakharovShabat.PhysicalH1Density
import NLS.ZakharovShabat.L2StripStability

/-! The H1 error budget grows linearly in H1 while the exponential is
controlled by a fixed physical L2 ball. This permits Fourier truncation
at a spectral-frequency-dependent cutoff. -/
noncomputable section
open Set Metric Complex NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

theorem norm_periodicH1SolutionCurve_sub_free_L2_budget
    (a : ScalarDomain 2 × ScalarDomain 2) (R H : ℝ)
    (hR : ‖sobolevSourceInclusion a‖≤R)
    (z : ℂ) (hz : z≠0) (hH : |z.im|≤H) (v : ℂ × ℂ) :
    ‖l2SolutionCurve (sourcePeriodicH1L2Class a) z v-l2SolutionCurve 0 z v‖ ≤
      ((8+2*Real.pi)*(1+R*Real.exp R)*Real.exp H)*‖a‖/‖z‖*‖v‖ := by
  let c := (Coeff.periodDoubleSobolev a.1,Coeff.periodDoubleSobolev a.2)
  let φ := classicalSobolevPotential c
  have hR0 : 0≤R := (norm_nonneg _).trans hR
  have hc : ‖c‖≤2*‖a‖ := max_le
    ((Coeff.norm_periodDoubleSobolev_le a.1).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le a) (by norm_num)))
    ((Coeff.norm_periodDoubleSobolev_le a.2).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le a) (by norm_num)))
  have hL : classicalPotentialL2Norm φ=‖sobolevSourceInclusion a‖ := by
    rw [← norm_continuousPotentialL2Class]
    exact (congrArg norm (sourcePeriodicH1L2Class_eq_classical a)).symm.trans
      (norm_sourcePeriodicH1L2Class a)
  have hLn : 0≤classicalPotentialL2Norm φ := Real.sqrt_nonneg _
  have hbudget : classicalFirstBornUniformBudget φ≤(8+2*Real.pi)*(2*‖a‖) :=
    (classicalFirstBornUniformBudget_sobolev_le c).trans
      (mul_le_mul_of_nonneg_left hc (by positivity))
  have hF : 1+classicalPotentialL2Norm φ*Real.exp (classicalPotentialL2Norm φ)≤1+R*Real.exp R := by
    rw [hL]
    gcongr
  obtain ⟨hf,hg,hfi,hgi⟩ := classicalSobolevPotential_regular c
  rw [sourcePeriodicH1L2Class_eq_classical,l2SolutionCurve_of_continuous]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖classicalSolutionCurve φ z v t-l2SolutionCurve 0 z v t‖≤_
  rw [classicalSolutionCurve_apply,l2SolutionCurve_free]
  change ‖classicalSolutionRemainder φ z v t‖≤_
  have hn := classicalNormalizedRemainder_le_inverse_frequency_L2 φ hf hg hfi hgi z hz v t
  have hB := classicalFirstBornUniformBudget_nonneg φ
  have hn' : Real.exp (-(|z.im| *t.val))*‖classicalSolutionRemainder φ z v t‖ ≤
      ((8+2*Real.pi)*(2*‖a‖)*‖v‖/(2*‖z‖))*(1+R*Real.exp R) := by
    apply hn.trans
    exact mul_le_mul
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget (norm_nonneg _)) (by positivity))
      hF (by positivity) (by positivity)
  have htH : |z.im| *t.val≤H := by nlinarith [abs_nonneg z.im,t.property.2]
  calc
    _ = Real.exp (|z.im| *t.val)*
        (Real.exp (-(|z.im| *t.val))*‖classicalSolutionRemainder φ z v t‖) := by
      rw [← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
    _ ≤ Real.exp (|z.im| *t.val)*
        (((8+2*Real.pi)*(2*‖a‖)*‖v‖/(2*‖z‖))*(1+R*Real.exp R)) :=
      mul_le_mul_of_nonneg_left hn' (Real.exp_nonneg _)
    _ ≤ Real.exp H*(((8+2*Real.pi)*(2*‖a‖)*‖v‖/(2*‖z‖))*(1+R*Real.exp R)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr htH) (by positivity)
    _ = _ := by ring

end NLS.ZakharovShabat
