import NLS.Articles.KdVPseudomeasures.OriginalHillH1TransverseSlope
import NLS.FunctionalAnalysis.RealCircleDerivative

/-! Actual canonical physical KdV energy is stationary along every native
mode circle. The literal infinitesimal tangent is i*z_n in the selected mode. -/
noncomputable section
open Complex NLS.WeightedCoeff NLS.FunctionalAnalysis
namespace NLS.Articles.KdVPseudomeasures

theorem hillH1CanonicalHamiltonian_mode_circle
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (n : ℕ+) (t : ℝ) :
    hillH1CanonicalHamiltonian (z+hillH1ModeCLM n ((realCirclePhase t-1)*z.val.val.val (n:ℤ)))=
      hillH1CanonicalHamiltonian z := by
  have hc : (realCirclePhase t*z.val.val.val (n:ℤ))*
      (starRingEnd ℂ) (realCirclePhase t*z.val.val.val (n:ℤ))=
      z.val.val.val (n:ℤ)*(starRingEnd ℂ) (z.val.val.val (n:ℤ)) := by
    rw [map_mul]
    calc
      _ = (realCirclePhase t*(starRingEnd ℂ) (realCirclePhase t))*
          (z.val.val.val (n:ℤ)*(starRingEnd ℂ) (z.val.val.val (n:ℤ))) := by ring
      _ = _ := by rw [realCirclePhase_mul_conj,one_mul]
  have h := hillH1CanonicalHamiltonian_mode_replace z n (realCirclePhase t*z.val.val.val (n:ℤ)) hc
  have he : realCirclePhase t*z.val.val.val (n:ℤ)-z.val.val.val (n:ℤ)=
      (realCirclePhase t-1)*z.val.val.val (n:ℤ) := by ring
  simpa only [fourierRealModeReplace,he,hillH1ModeCLM] using h

theorem hillH1CanonicalHamiltonian_fderiv_circle_zero
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (n : ℕ+) :
    (fderiv ℝ hillH1CanonicalHamiltonian z) (hillH1ModeCLM n (I*z.val.val.val (n:ℤ)))=0 :=
  @fderiv_circle_tangent_eq_zero (RealSignedHilbert (signedStepOrder (1/2) 1))
    inferInstance inferInstance hillH1CanonicalHamiltonian z (hillH1ModeCLM n)
    (z.val.val.val (n:ℤ)) (analyticAt_hillH1CanonicalHamiltonian z).differentiableAt
    (hillH1CanonicalHamiltonian_mode_circle z n)

theorem hillH1CanonicalHamiltonian_radial_gradient_relation
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (n : ℕ+) :
    (z.val.val.val (n:ℤ)).re*((fderiv ℝ hillH1CanonicalHamiltonian z) (hillH1ModeCLM n I))=
      (z.val.val.val (n:ℤ)).im*hillH1RealModeDerivative n z := by
  have he : I*z.val.val.val (n:ℤ)=
      (-(z.val.val.val (n:ℤ)).im) • (1:ℂ)+(z.val.val.val (n:ℤ)).re • I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have ht := hillH1CanonicalHamiltonian_fderiv_circle_zero z n
  rw [he,map_add,map_smul,map_smul,map_add,map_smul,map_smul] at ht
  change -(z.val.val.val (n:ℤ)).im*hillH1RealModeDerivative n z+
    (z.val.val.val (n:ℤ)).re*((fderiv ℝ hillH1CanonicalHamiltonian z) (hillH1ModeCLM n I))=0 at ht
  linarith

end NLS.Articles.KdVPseudomeasures
