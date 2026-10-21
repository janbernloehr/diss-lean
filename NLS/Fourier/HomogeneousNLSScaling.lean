import NLS.Fourier.IntervalDilation
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Homogeneous Fourier energy and the critical NLS exponent

This implements the physical dilation and energy statement from the introduction, printed p. 10.
-/

noncomputable section
open MeasureTheory Complex
open scoped ENNReal FourierTransform
namespace NLS.Fourier

/-- Full-line nonnegative integrals scale with the actual inverse Jacobian. -/
theorem lintegral_line_dilation {c : ℝ} (hc : 0 < c) (F : ℝ → ℝ≥0∞) :
    (∫⁻ x : ℝ, F (c*x)) = ENNReal.ofReal c⁻¹ * ∫⁻ x : ℝ, F x := by
  have hm : MeasurePreserving (fun x : ℝ => c*x) volume (ENNReal.ofReal c⁻¹ • volume) := by
    refine ⟨by fun_prop,?_⟩
    simpa only [abs_of_pos (inv_pos.mpr hc)] using Real.map_volume_mul_left hc.ne'
  have he : MeasurableEmbedding (fun x : ℝ => c*x) :=
    (Homeomorph.mulLeft₀ c hc.ne').isClosedEmbedding.measurableEmbedding
  simpa only [lintegral_smul_measure,smul_eq_mul] using hm.lintegral_comp_emb he F

/-- The Fourier transform of the actual one-dimensional NLS scaling has no
amplitude factor after its spatial Jacobian is canceled. -/
theorem fourier_scalarNLS_dilation {c : ℝ} (hc : 0 < c) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (c:ℂ)*f (c*x)) ξ = 𝓕 f (ξ/c) := by
  let G : ℝ → ℂ := fun y => Complex.exp ((-2*Real.pi*y*(ξ/c):ℝ)*Complex.I)*f y
  have harg (x : ℝ) : -2*Real.pi*(c*x)*(ξ/c) = -2*Real.pi*x*ξ := by
    field_simp
  calc
    _ = (c:ℂ)*(∫ x : ℝ, G (c*x)) := by
      rw [Real.fourier_real_eq_integral_exp_smul,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [G,harg,smul_eq_mul]
      ring
    _ = (c:ℂ)*(c⁻¹:ℝ)*(∫ y : ℝ, G y) := by
      rw [Measure.integral_comp_mul_left]
      simp only [abs_of_pos (inv_pos.mpr hc),Complex.real_smul]
      ring
    _ = 𝓕 f (ξ/c) := by
      rw [← Complex.ofReal_mul,mul_inv_cancel₀ hc.ne',Complex.ofReal_one,one_mul,
        Real.fourier_real_eq_integral_exp_smul]
      rfl

/-- Extended squared homogeneous Sobolev energy of frequency data.
The nonnegative integral includes infinite energies. -/
def homogeneousSpectralEnergy (s : ℝ) (F : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ : ℝ, ENNReal.ofReal (|ξ|^(2*s)) * ENNReal.ofReal (‖F ξ‖^2)

/-- The exact homogeneous energy scaling in dimension one. -/
theorem homogeneousSpectralEnergy_dilation {c : ℝ} (hc : 0 < c) (s : ℝ) (F : ℝ → ℂ) :
    homogeneousSpectralEnergy s (fun ξ : ℝ => F (ξ/c)) =
      ENNReal.ofReal (c^(2*s+1)) * homogeneousSpectralEnergy s F := by
  have hweight (ξ : ℝ) : |ξ|^(2*s) = c^(2*s)*|c⁻¹*ξ|^(2*s) := by
    have he : c*|c⁻¹*ξ| = |ξ| := by
      rw [abs_mul,abs_of_pos (inv_pos.mpr hc),← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]
    rw [← Real.mul_rpow hc.le (abs_nonneg _),he]
  unfold homogeneousSpectralEnergy
  calc
    _ = ENNReal.ofReal (c^(2*s)) *
        ∫⁻ ξ : ℝ, ENNReal.ofReal (|c⁻¹*ξ|^(2*s)) * ENNReal.ofReal (‖F (c⁻¹*ξ)‖^2) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro ξ
      rw [hweight ξ,ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]
      simp only [mul_assoc,div_eq_mul_inv,mul_comm ξ c⁻¹]
    _ = ENNReal.ofReal (c^(2*s)) *
        (ENNReal.ofReal c * ∫⁻ ξ : ℝ, ENNReal.ofReal (|ξ|^(2*s)) * ENNReal.ofReal (‖F ξ‖^2)) := by
      rw [lintegral_line_dilation (inv_pos.mpr hc)
        (fun ξ : ℝ => ENNReal.ofReal (|ξ|^(2*s)) * ENNReal.ofReal (‖F ξ‖^2)),inv_inv]
    _ = _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _),Real.rpow_add hc,Real.rpow_one]

/-- The homogeneous Sobolev energy of the actual Fourier transform. -/
def homogeneousSobolevEnergy (s : ℝ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  homogeneousSpectralEnergy s (𝓕 f)

/-- The actual NLS dilation scales squared homogeneous H^s energy by c^(2s+1). -/
theorem homogeneousSobolevEnergy_scalarNLS_dilation {c : ℝ} (hc : 0 < c)
    (s : ℝ) (f : ℝ → ℂ) :
    homogeneousSobolevEnergy s (fun x : ℝ => (c:ℂ)*f (c*x)) =
      ENNReal.ofReal (c^(2*s+1))*homogeneousSobolevEnergy s f := by
  unfold homogeneousSobolevEnergy
  have he : 𝓕 (fun x : ℝ => (c:ℂ)*f (c*x)) = fun ξ => 𝓕 f (ξ/c) :=
    funext (fourier_scalarNLS_dilation hc f)
  rw [he,homogeneousSpectralEnergy_dilation hc]

/-- The critical negative-half homogeneous energy is exactly invariant,
including the finite-energy class and infinite values. -/
theorem homogeneousCriticalEnergy_scalarNLS_dilation {c : ℝ} (hc : 0 < c) (f : ℝ → ℂ) :
    homogeneousSobolevEnergy (-1/2) (fun x : ℝ => (c:ℂ)*f (c*x)) =
      homogeneousSobolevEnergy (-1/2) f := by
  rw [homogeneousSobolevEnergy_scalarNLS_dilation hc]
  norm_num

end NLS.Fourier
