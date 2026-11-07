import NLS.KdV.HillPeriodOneL1Comparison
import NLS.KdV.ClassicalHillFreeTraceVariation
import NLS.Fourier.PeriodOneTrigPairing
import NLS.FunctionalAnalysis.LinearSourceRestrictionDerivative
import NLS.ComplexAnalysis.MixedSpectralSourceDerivative

/-! The ACTUAL native Hill trace first variation at the free potential.
Every complex H-minus-one mean-zero direction annihilates the ENTIRE
energy discriminant, including zero energy. -/
noncomputable section
open Set Complex Filter Topology NLS.LinearVolterra NLS.Fourier NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusDiscriminant_eq_classical_L1 (a : Coeff 1) (μ : ℂ) :
    hillHminusDiscriminant (periodOneL1Inclusion a) μ =
      classicalHillDiscriminant (periodOneL1PotentialCurve a) μ := by
  rw [periodOneL1Inclusion,ContinuousLinearMap.comp_apply,hillHminusDiscriminant_eq_hillL2,
    ← hillContinuousCoefficients_periodOneSynthesis,hillL2Discriminant_eq_classical]
  rfl

theorem fderiv_hillHminusDiscriminant_L1 (μ : ℂ) (a : Coeff 1) :
    (fderiv ℂ (fun q => hillHminusDiscriminant q μ) 0) (periodOneL1Inclusion a) =
      (fderiv ℂ (fun Q => classicalHillDiscriminant Q μ) 0) (periodOneL1PotentialCurve a) := by
  have hN : DifferentiableAt ℂ (fun q => hillHminusDiscriminant q μ) 0 :=
    ((analyticOnNhd_hillHminusDiscriminant_joint (μ,0) (mem_univ _)).comp
      (f := fun q : PeriodOneHminusOne => (μ,q)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hP : DifferentiableAt ℂ (fun Q => classicalHillDiscriminant Q μ) 0 :=
    ((analyticOnNhd_classicalHillDiscriminant_joint (μ,0) (mem_univ _)).comp
      (f := fun Q : Curve ℂ => (μ,Q)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hNc := NLS.FunctionalAnalysis.fderiv_comp_linear_zero _ periodOneL1Inclusion hN
  have hPc := NLS.FunctionalAnalysis.fderiv_comp_linear_zero _ periodOneL1PotentialCurve hP
  have he : (fun b => hillHminusDiscriminant (periodOneL1Inclusion b) μ) =
      fun b => classicalHillDiscriminant (periodOneL1PotentialCurve b) μ :=
    funext (fun b => hillHminusDiscriminant_eq_classical_L1 b μ)
  rw [he,hPc] at hNc
  have hh := congrArg (fun L : Coeff 1 →L[ℂ] ℂ => L a) hNc
  simpa only [ContinuousLinearMap.comp_apply] using hh.symm

theorem fderiv_hillHminusDiscriminant_free_sq_L1 (z : ℂ) (hz : z ≠ 0) (a : Coeff 1) :
    (fderiv ℂ (fun q => hillHminusDiscriminant q (z^2)) 0) (periodOneL1Inclusion a) =
      sin z/z*a 0 := by
  rw [fderiv_hillHminusDiscriminant_L1,fderiv_classicalHillDiscriminant_free _ z hz]
  congr 1
  calc
    _ = ∫ t in (0:ℝ)..1, periodOneSynthesis a t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hti : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht
      rw [extend_coe (periodOneL1PotentialCurve a) ⟨t,hti⟩,periodOneL1PotentialCurve_apply]
    _ = a 0 := integral_periodOneSynthesis a

theorem fderiv_hillHminusDiscriminant_free_sq (z : ℂ) (hz : z ≠ 0) (h : PeriodOneHminusOne) :
    (fderiv ℂ (fun q => hillHminusDiscriminant q (z^2)) 0) h = sin z/z*h.val 0 := by
  have he := denseRange_periodOneL1Inclusion.equalizer
    (fderiv ℂ (fun q => hillHminusDiscriminant q (z^2)) 0).continuous
    ((WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 0).continuous.const_mul (sin z/z)) (by
      funext a
      simpa only [Function.comp_def,WeightedCoeff.evalCLM_apply,periodOneL1Inclusion_apply] using
        fderiv_hillHminusDiscriminant_free_sq_L1 z hz a)
  exact congrFun he h

theorem continuous_hillHminusDiscriminant_free_variation (h : PeriodOneHminusOne) :
    Continuous (fun μ => (fderiv ℂ (fun q => hillHminusDiscriminant q μ) 0) h) := by
  let F : ℂ × PeriodOneHminusOne → ℂ := fun t => hillHminusDiscriminant t.2 t.1
  let ev : ((ℂ × PeriodOneHminusOne) →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (0,h)
  have hc : Continuous (fun t => (fderiv ℂ F t) (0,h)) :=
    (ev.comp_analyticOnNhd analyticOnNhd_hillHminusDiscriminant_joint.fderiv).continuous
  have he : (fun μ => (fderiv ℂ (fun q => hillHminusDiscriminant q μ) 0) h) =
      fun μ => (fderiv ℂ F (μ,0)) (0,h) := by
    funext μ
    rw [fderiv_source_section_eq_joint F μ 0
      (analyticOnNhd_hillHminusDiscriminant_joint (μ,0) (mem_univ _)).differentiableAt,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply]
  rw [he]
  exact hc.comp (continuous_id.prodMk continuous_const)

theorem fderiv_hillHminusDiscriminant_free_mean_zero (h : PeriodOneHminusOne)
    (hh : h.val 0 = 0) (μ : ℂ) :
    (fderiv ℂ (fun q => hillHminusDiscriminant q μ) 0) h = 0 := by
  let S := {μ : ℂ | (fderiv ℂ (fun q => hillHminusDiscriminant q μ) 0) h = 0}
  have hS : IsClosed S := isClosed_eq (continuous_hillHminusDiscriminant_free_variation h) continuous_const
  have hsub : ({0}ᶜ : Set ℂ) ⊆ S := by
    intro w hw
    have hw0 : w ≠ 0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hw
    obtain ⟨z,rfl⟩ := IsAlgClosed.exists_pow_nat_eq w (by norm_num : 0 < 2)
    have hz : z ≠ 0 := fun he => hw0 (by simp only [he,zero_pow (by norm_num : (2:ℕ) ≠ 0)])
    change (fderiv ℂ (fun q => hillHminusDiscriminant q (z^2)) 0) h = 0
    rw [fderiv_hillHminusDiscriminant_free_sq z hz,hh,mul_zero]
  exact hS.closure_subset_iff.mpr hsub (dense_compl_singleton (0:ℂ) μ)

end NLS.KdV
