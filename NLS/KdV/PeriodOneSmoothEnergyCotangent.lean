import NLS.KdV.PeriodOneHamiltonianGradient
import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra
import NLS.SequenceSpaces.SobolevModeDualExt
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.Poisson.HminusGradientPairing

/-! The GENUINE smooth physical KdV energy gradient defines a bounded
cotangent on the original Hminus-one space. Its restriction is the FULL
complex H1 energy differential, and its Gardner direction has exactly
the Fourier coefficients of -q_xxx+6*q*q_x. -/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ZakharovShabat NLS.Poisson NLS.WeightedCoeff
open scoped ContDiff ENNReal
namespace NLS.KdV

theorem contDiff_classicalKdVGradient (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (classicalKdVGradient q) :=
  (NLS.FunctionalAnalysis.contDiff_iteratedDeriv q hq 2).neg.add (contDiff_const.mul (hq.pow 2))

def periodOneH1RoughInclusion : ScalarDomain 2 →L[ℂ] PeriodOneHminusOne :=
  periodOneL2Inclusion.comp scalarInclusion

theorem periodOneH1RoughInclusion_apply (q : ScalarDomain 2) (k : ℤ) :
    (periodOneH1RoughInclusion q).val k=q.val k := by
  change (periodOneL2Inclusion (scalarInclusion q)).val k=_
  rw [periodOneL2Inclusion_apply,scalarInclusion_apply]

def periodOneSmoothKdVGradient (q : ScalarDomain 2)
    (hq : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ)))) :
    WeightedCoeff (Weight.sobolev 1) 2 :=
  WeightedCoeff.exponentInclusion (Weight.sobolev 1) (by norm_num : (1:ℝ≥0∞)≤2)
    ⟨periodOneCoefficient (classicalKdVGradient (fun x : ℝ => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ)))),
      memlp_periodOneCoefficient_sobolev_one 1 zero_le_one _ (contDiff_classicalKdVGradient _ hq)
        (classicalKdVGradient_periodic _ (periodOneSobolevSynthesis_periodic q))⟩

theorem periodOneSmoothKdVGradient_apply (q : ScalarDomain 2)
    (hq : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ)))) (k : ℤ) :
    (periodOneSmoothKdVGradient q hq).val k=
      periodOneCoefficient (classicalKdVGradient (fun x : ℝ => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ)))) k :=
  WeightedCoeff.exponentInclusion_apply _ _ _ k

def periodOneSmoothKdVEnergyCotangent (q : ScalarDomain 2)
    (hq : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ)))) :
    PeriodOneHminusOne →L[ℂ] ℂ :=
  (WeightedCoeff.sobolevBilinearPairing (p:=2) (q:=2) 1) (periodOneSmoothKdVGradient q hq)

theorem periodOneSmoothKdVEnergyCotangent_restrict (q : ScalarDomain 2)
    (hq : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ)))) :
    (periodOneSmoothKdVEnergyCotangent q hq).comp periodOneH1RoughInclusion=
      fderiv ℂ periodOneKdVHamiltonian q := by
  apply scalarMode_dual_ext
  intro n
  have hm : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis (scalarMode (p:=2) n 1) (x : AddCircle (2:ℝ))) := by
    simpa only [periodOneSobolevSynthesis_scalarMode,one_mul] using contDiff_wave_infty (2*n)
  have hline : HasDerivAt (fun z : ℂ => q+z • scalarMode n 1) (scalarMode (p:=2) n 1) 0 := by
    simpa only [one_smul] using! ((hasDerivAt_id (0:ℂ)).smul_const (scalarMode (p:=2) n 1)).const_add q
  have hd := (analyticAt_periodOneKdVHamiltonian q).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq
    0 hline (by simp)
  have hv := hd.unique (hasDerivAt_periodOneKdVHamiltonian_gradient q (scalarMode n 1) hq hm)
  simp only [periodOneSobolevSynthesis_scalarMode,one_mul] at hv
  change periodOneSmoothKdVEnergyCotangent q hq (periodOneH1RoughInclusion (scalarMode n 1))=_
  rw [periodOneSmoothKdVEnergyCotangent,WeightedCoeff.sobolevBilinearPairing_apply]
  have he : (∑' k : ℤ, (periodOneSmoothKdVGradient q hq).val k*
      (periodOneH1RoughInclusion (scalarMode n 1)).val (-k))=(periodOneSmoothKdVGradient q hq).val (-n) := by
    simp [periodOneH1RoughInclusion_apply,scalarMode_apply,neg_eq_iff_eq_neg]
  rw [he,periodOneSmoothKdVGradient_apply]
  rw [hv]
  change fourierCoeffOn (by norm_num : (0:ℝ)<1) _ (-n)=_
  rw [← unitFourierCoefficient_eq_fourierCoeffOn,unitFourierCoefficient]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [mul_neg,neg_neg]
  ring

theorem periodOneSmoothKdVEnergyCotangent_physical_vector (q : ScalarDomain 2)
    (hq : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ)))) (k : ℤ) :
    (gardnerHamiltonianDirection (periodOneSmoothKdVEnergyCotangent q hq)).val k=
      periodOneCoefficient (classicalKdVVectorField (fun x : ℝ => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ)))) k := by
  change (gardnerDerivative (hminusCotangentCLM
    ((WeightedCoeff.sobolevBilinearPairing (p:=2) (q:=2) 1) (periodOneSmoothKdVGradient q hq)))).val k=_
  rw [hminusCotangentCLM_sobolevBilinearPairing,gardnerDerivative_apply,periodOneSmoothKdVGradient_apply]
  rw [← deriv_classicalKdVGradient _ hq,periodOneCoefficient_deriv_of_smooth_periodic _
    (contDiff_classicalKdVGradient _ hq) (classicalKdVGradient_periodic _ (periodOneSobolevSynthesis_periodic q))]
  ring

end NLS.KdV
