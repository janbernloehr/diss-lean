import NLS.Fourier.DistributionDilation
import NLS.Fourier.HomogeneousNLSScaling
import Mathlib.Analysis.Distribution.TemperedDistribution

/-! # Physical NLS dilation on actual tempered distributions

This implements the critical full-line dilation statement from the introduction, printed p. 10.
-/

noncomputable section
open MeasureTheory Complex
open scoped SchwartzMap FourierTransform
namespace NLS.Fourier

/-- The physical NLS amplitude and dilation on actual tempered distributions. -/
def lineTemperedNLSScaling (c : ℝ) (hc : 0 < c) : 𝓢'(ℝ,ℂ) →L[ℂ] 𝓢'(ℝ,ℂ) :=
  (c:ℂ) • distributionDilationCLM c hc.ne'

/-- The physical amplitude cancels the spatial inverse Jacobian exactly. -/
theorem lineTemperedNLSScaling_apply (c : ℝ) (hc : 0 < c)
    (T : 𝓢'(ℝ,ℂ)) (g : 𝓢(ℝ,ℂ)) :
    lineTemperedNLSScaling c hc T g = T (schwartzDilationCLM c⁻¹ (inv_ne_zero hc.ne') g) := by
  change (c:ℂ)*((c:ℂ)⁻¹*T (schwartzDilationCLM c⁻¹ (inv_ne_zero hc.ne') g)) = _
  rw [← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'),one_mul]

/-- The actual Schwartz Fourier transform retains the exact dilation amplitude. -/
theorem fourier_schwartzNLSScaling (c : ℝ) (hc : 0 < c) (g : 𝓢(ℝ,ℂ)) (ξ : ℝ) :
    (c:ℂ)*𝓕 (schwartzDilationCLM c hc.ne' g) ξ = 𝓕 g (ξ/c) := by
  have h := fourier_scalarNLS_dilation hc (g : ℝ → ℂ) ξ
  have he : (fun x : ℝ => (c:ℂ)*g (c*x)) =
      (((c:ℂ) • schwartzDilationCLM c hc.ne' g : 𝓢(ℝ,ℂ)) : ℝ → ℂ) := rfl
  rw [he] at h
  change 𝓕 ((c:ℂ) • schwartzDilationCLM c hc.ne' g) ξ = _ at h
  rw [FourierTransform.fourier_smul] at h
  exact h

/-- Fourier covariance of the physical NLS scaling holds for every tempered distribution. -/
theorem fourier_lineTemperedNLSScaling (c : ℝ) (hc : 0 < c) (T : 𝓢'(ℝ,ℂ)) :
    𝓕 (lineTemperedNLSScaling c hc T) =
      distributionDilation c⁻¹ (inv_ne_zero hc.ne') (𝓕 T) := by
  ext g
  rw [TemperedDistribution.fourier_apply,lineTemperedNLSScaling_apply,
    distributionDilation_apply,TemperedDistribution.fourier_apply]
  simp only [Complex.ofReal_inv,inv_inv]
  have he : schwartzDilationCLM c⁻¹ (inv_ne_zero hc.ne') (𝓕 g) =
      (c:ℂ) • 𝓕 (schwartzDilationCLM c hc.ne' g) := by
    ext ξ
    change 𝓕 g (c⁻¹*ξ) = (c:ℂ)*𝓕 (schwartzDilationCLM c hc.ne' g) ξ
    simpa only [div_eq_mul_inv,mul_comm ξ c⁻¹] using (fourier_schwartzNLSScaling c hc g ξ).symm
  rw [he,map_smul,smul_eq_mul]

/-- The inverse physical dilation recovers the same original distribution. -/
theorem lineTemperedNLSScaling_inverse (c : ℝ) (hc : 0 < c) (T : 𝓢'(ℝ,ℂ)) :
    lineTemperedNLSScaling c⁻¹ (inv_pos.mpr hc) (lineTemperedNLSScaling c hc T) = T := by
  ext g
  rw [lineTemperedNLSScaling_apply,lineTemperedNLSScaling_apply]
  congr 1
  ext ξ
  simp only [schwartzDilationCLM_apply,inv_inv]
  congr 1
  field_simp

end NLS.Fourier
