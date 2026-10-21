import NLS.Fourier.CriticalHomogeneousSobolev

/-! # Exact finite-energy Fourier-density characterization

This implements the critical full-line dilation statement from the introduction, printed p. 10.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier

/-- The critical spectral measure and Lebesgue measure have the same null sets. -/
theorem volume_absolutelyContinuous_criticalFrequencyMeasure :
    (volume : Measure ℝ) ≪ criticalFrequencyMeasure := by
  apply withDensity_absolutelyContinuous' (by fun_prop)
  filter_upwards [volume.ae_ne (0:ℝ)] with ξ hξ
  exact ENNReal.ofReal_ne_zero_iff.mpr (norm_pos_iff.mpr hξ)

/-- Dividing a Fourier density by |xi| converts its critical energy into weighted L2 energy. -/
theorem lintegral_criticalInverseDensity (F : ℝ → ℂ) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (‖(‖ξ‖:ℂ)⁻¹*F ξ‖^2) ∂criticalFrequencyMeasure) =
      homogeneousSpectralEnergy (-(1:ℝ)/2) F := by
  rw [lintegral_criticalFrequencyMeasure,homogeneousSpectralEnergy]
  apply lintegral_congr
  intro ξ
  norm_num only [show (2:ℝ)*(-(1:ℝ)/2) = -1 by norm_num,Real.rpow_neg_one]
  rw [← Real.norm_eq_abs ξ,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg ξ),mul_pow]
  rw [← ENNReal.ofReal_mul (norm_nonneg _),← ENNReal.ofReal_mul (by positivity)]
  congr 1
  by_cases hξ : ξ = 0
  · simp [hξ]
  · field_simp

/-- Every measurable Fourier density of finite critical energy has a weighted L2 representative. -/
theorem memLp_criticalInverseDensity (F : ℝ → ℂ) (hF : AEStronglyMeasurable F volume)
    (he : homogeneousSpectralEnergy (-(1:ℝ)/2) F < ⊤) :
    MemLp (fun ξ : ℝ => (‖ξ‖:ℂ)⁻¹*F ξ) 2 criticalFrequencyMeasure := by
  have hFν : AEStronglyMeasurable F criticalFrequencyMeasure :=
    hF.mono_ac (withDensity_absolutelyContinuous _ _)
  refine ⟨(by fun_prop),?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat,ENNReal.rpow_two]
  have hi : (∫⁻ ξ : ℝ, ‖(‖ξ‖:ℂ)⁻¹*F ξ‖ₑ^2 ∂criticalFrequencyMeasure) =
      homogeneousSpectralEnergy (-(1:ℝ)/2) F := by
    simpa only [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm] using lintegral_criticalInverseDensity F
  rw [hi]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) he.ne

/-- Every finite-energy Fourier density has a critical-space representative with the exact norm. -/
theorem exists_criticalHomogeneousSobolev_of_finite_energy (F : ℝ → ℂ)
    (hF : AEStronglyMeasurable F volume) (he : homogeneousSpectralEnergy (-(1:ℝ)/2) F < ⊤) :
    ∃ f : CriticalHomogeneousSobolev,
      (fun ξ => (‖ξ‖:ℂ)*f ξ) =ᵐ[volume] F ∧
      homogeneousSpectralEnergy (-(1:ℝ)/2) F = ENNReal.ofReal (‖f‖^2) := by
  let hf := memLp_criticalInverseDensity F hF he
  let f : CriticalHomogeneousSobolev := hf.toLp (fun ξ : ℝ => (‖ξ‖:ℂ)⁻¹*F ξ)
  have hcoef : (fun ξ => (‖ξ‖:ℂ)*f ξ) =ᵐ[volume] F := by
    have ha : (f : ℝ → ℂ) =ᵐ[volume] (fun ξ : ℝ => (‖ξ‖:ℂ)⁻¹*F ξ) :=
      volume_absolutelyContinuous_criticalFrequencyMeasure.ae_eq hf.coeFn_toLp
    filter_upwards [ha,volume.ae_ne (0:ℝ)] with ξ hξ hzero
    rw [hξ,← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hzero)),one_mul]
  refine ⟨f,hcoef,?_⟩
  rw [← homogeneousSpectralEnergy_criticalDensity f]
  apply lintegral_congr_ae
  filter_upwards [hcoef] with ξ hξ
  rw [hξ]

/-- The complete critical model is exactly the original distributions whose Fourier
transform has a measurable density of finite critical homogeneous energy. -/
theorem isCriticalHomogeneousSobolev_iff_fourier_density (T : 𝓢'(ℝ,ℂ)) :
    IsCriticalHomogeneousSobolev T ↔
      ∃ F : ℝ → ℂ, AEStronglyMeasurable F volume ∧
        homogeneousSpectralEnergy (-(1:ℝ)/2) F < ⊤ ∧
        ∀ g : 𝓢(ℝ,ℂ), 𝓕 T g = ∫ ξ : ℝ, g ξ*F ξ := by
  constructor
  · rintro ⟨f,hf⟩
    have hm : AEStronglyMeasurable (fun ξ : ℝ => f ξ) volume :=
      (Lp.aestronglyMeasurable f).mono_ac volume_absolutelyContinuous_criticalFrequencyMeasure
    refine ⟨(fun ξ => (‖ξ‖:ℂ)*f ξ),(by fun_prop),?_,?_⟩
    · rw [homogeneousSpectralEnergy_criticalDensity]
      exact ENNReal.ofReal_lt_top
    · intro g
      rw [← hf]
      exact criticalHomogeneousSobolev_fourier_apply f g
  · rintro ⟨F,hF,he,hT⟩
    obtain ⟨f,hcoef,_⟩ := exists_criticalHomogeneousSobolev_of_finite_energy F hF he
    refine ⟨f,?_⟩
    have hfourier : 𝓕 (criticalHomogeneousSobolevDistribution f) = 𝓕 T := by
      ext g
      rw [criticalHomogeneousSobolev_fourier_apply,hT]
      apply integral_congr_ae
      filter_upwards [hcoef] with ξ hξ
      rw [hξ]
    have h := congrArg (fun S : 𝓢'(ℝ,ℂ) => 𝓕⁻ S) hfourier
    simpa only [FourierTransform.fourierInv_fourier_eq] using h

end NLS.Fourier
