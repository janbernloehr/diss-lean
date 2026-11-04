import NLS.KdV.HillScaledFreeContourGeometry
import NLS.KdV.HillFreeContourRadicandBound
import NLS.KdV.HillFreeDirichlet
import NLS.ComplexAnalysis.SineAnnulusInner

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillScaledFreeGapContour_sine_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, 1 ≤ n → ∀ E : ℂ,
      E ∈ sphere (hillRealGapCenter 0 h0q h0r n : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n)) →
      b ≤ ‖sin (Complex.sqrt E)‖ := by
  obtain ⟨b,hb,hbound⟩ := exists_uniform_sine_lower_annulus_of_inner (ρ*Real.pi/10)
    (by positivity) (by nlinarith [mul_le_mul_of_nonneg_right hρ1 Real.pi_pos.le,Real.pi_pos])
  refine ⟨b,hb,?_⟩
  intro n hn E hE
  have hg := hillScaledFreeGapContour_frequency_bounds h0q h0r ρ hρ hρ1 n hn E hE
  have hs := hbound (Complex.sqrt E-(n : ℂ)*Real.pi) hg.1 hg.2.1
  have hcos : cos ((n : ℂ)*Real.pi) = (-1 : ℂ)^n := by
    have h := congrArg Complex.ofReal (Real.cos_nat_mul_pi n)
    push_cast at h
    exact h
  have hnorm : ‖sin (Complex.sqrt E-(n : ℂ)*Real.pi)‖ = ‖sin (Complex.sqrt E)‖ := by
    rw [Complex.sin_sub,Complex.sin_nat_mul_pi,hcos,mul_zero,sub_zero,norm_mul,
      norm_pow,norm_neg,norm_one,one_pow,mul_one]
  rwa [hnorm] at hs

theorem exists_hillScaledFreeGapContour_characteristic_bounds (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ d : ℝ, 0 < d ∧ ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, 1 ≤ n → ∀ E : ℂ,
      E ∈ sphere (hillRealGapCenter 0 h0q h0r n : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n)) →
      d ≤ ‖hillL2Radicand 0 E‖ ∧ b/(n : ℝ) ≤ ‖hillL2DirichletCharacteristic 0 E‖ := by
  obtain ⟨b,hb,hbound⟩ := exists_hillScaledFreeGapContour_sine_bound h0q h0r ρ hρ hρ1
  refine ⟨4*b^2,by positivity,2*b/(3*Real.pi),by positivity,?_⟩
  intro n hn E hE
  have hg := hillScaledFreeGapContour_frequency_bounds h0q h0r ρ hρ hρ1 n hn E hE
  have hs := hbound n hn E hE
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hzpos : 0 < ‖Complex.sqrt E‖ := lt_of_lt_of_le (by positivity) hg.2.2.2.1
  have hz0 : Complex.sqrt E ≠ 0 := norm_pos_iff.mp hzpos
  constructor
  · rw [hillL2Radicand_zero,norm_mul,norm_neg,norm_ofNat,norm_pow]
    nlinarith [sq_le_sq₀ hb.le (norm_nonneg (sin (Complex.sqrt E))) |>.mpr hs]
  · have he := hillL2DirichletCharacteristic_free_sq (Complex.sqrt E) hz0
    rw [complex_sqrt_sq] at he
    rw [he,norm_div]
    calc
      _ = b/(3*(n : ℝ)*Real.pi/2) := by field_simp
      _ ≤ b/‖Complex.sqrt E‖ := div_le_div_of_nonneg_left hb.le hzpos hg.2.2.2.2
      _ ≤ ‖sin (Complex.sqrt E)‖/‖Complex.sqrt E‖ := div_le_div_of_nonneg_right hs hzpos.le

end NLS.KdV
