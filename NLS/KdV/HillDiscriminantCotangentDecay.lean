import NLS.KdV.HillDiscriminantCotangentModes
import NLS.Fourier.UnitIntervalACWaveDecay
import NLS.SequenceSpaces.ConjugateCotangent
import NLS.SequenceSpaces.DominatedTails

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- A common inverse-bracket bound for the actual coefficient cotangents on
bounded complex Hill source and energy balls, including all low frequencies. -/
theorem exists_hillDiscriminantCotangent_uniform_coefficient_decay (B R : ℝ) (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ q : Coeff 2, ‖q‖≤B → ∀ E : ℂ, ‖E‖≤R → ∀ n : ℤ,
      ‖(fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) (lp.single 2 n 1)‖≤
        C/(1+|(n : ℝ)|) := by
  obtain ⟨A,D,hA,hD,hbound⟩ := exists_hillDiscriminantGradient_uniform_curve_bounds
    (max B 0) R (le_max_right _ _) hR
  refine ⟨2*A+D,by positivity,?_⟩
  intro q hq E hE n
  obtain ⟨hf,hg⟩ := hbound q (hq.trans (le_max_left _ _)) E hE
  let f := NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve q E)
  let g := NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientSpatialCurve q E)
  have hder : deriv f=ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] g := by
    filter_upwards [ae_hasDerivAt_hillEnergyDiscriminantGradientCurve q E] with x hx
    exact hx.deriv
  have hfi : IntervalIntegrable (deriv f) volume 0 1 := by
    apply ((continuous_extend (hillEnergyDiscriminantGradientSpatialCurve q E)).intervalIntegrable 0 1).congr_ae
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ)≤1)] using hder.symm
  have hgb (t : ℝ) : ‖g t‖≤D :=
    ((hillEnergyDiscriminantGradientSpatialCurve q E).norm_coe_le_norm _).trans hg
  have hdi : (∫ t in (0 : ℝ)..1, ‖deriv f t‖)≤D := by
    have hi := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0 : ℝ)≤1)
      hfi.norm ((continuous_const : Continuous (fun _ : ℝ => D)).intervalIntegrable 0 1) (by
        rw [← restrict_Ioc_eq_restrict_Icc]
        filter_upwards [hder] with t ht
        rw [ht]
        exact hgb t)
    simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using hi
  rw [hillDiscriminantCotangent_single_integral]
  apply Fourier.norm_unitIntegral_mul_wave_le_bracket_of_ac f
    (hillEnergyDiscriminantGradient_H1 q E).1 hfi A D hA hD _ hdi n
  intro t _
  exact ((hillEnergyDiscriminantGradientCurve q E).norm_coe_le_norm _).trans hf

/-- All actual bounded-ball Hill discriminant cotangents share one genuine
square-summable Fourier majorant; the cutoff is uniform before choosing
both the original source and the energy. -/
theorem exists_hillDiscriminantCotangent_coefficient_majorant (B R : ℝ) (hR : 0≤R) :
    ∃ b : Coeff 2, ∀ q : Coeff 2, ‖q‖≤B → ∀ E : ℂ, ‖E‖≤R → ∀ n : ℤ,
      ‖Coeff.conjugateCotangent (by simp : (2 : ℝ≥0∞)≠⊤) (by simp : (2 : ℝ≥0∞)≠⊤)
        (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) n‖≤‖b n‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_hillDiscriminantCotangent_uniform_coefficient_decay B R hR
  let b : Coeff 2 := (C : ℂ) • WeightedCoeff.inverseWeight (Weight.sobolev 1)
    (Weight.inverse_sobolev_one_memlp (by norm_num : (1 : ℝ≥0∞)<2))
  refine ⟨b,?_⟩
  intro q hq E hE n
  have hbn : ‖b n‖=C/(1+|(n : ℝ)|) := by
    change ‖(C : ℂ)*(Weight.sobolev 1 n : ℂ)⁻¹‖=_
    simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC,
      Weight.sobolev_apply,Real.rpow_one,abs_of_pos (by positivity : 0<1+|(n : ℝ)|),div_eq_mul_inv]
  rw [hbn,Coeff.conjugateCotangent_apply]
  exact hbound q hq E hE n

end NLS.KdV
