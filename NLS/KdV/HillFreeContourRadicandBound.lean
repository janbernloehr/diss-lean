import NLS.KdV.HillFreeGapContourGeometry
import NLS.KdV.HillCharacteristicZeros
import NLS.ComplexAnalysis.SineAnnulusLowerBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGapContour_free_radicand_bound :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 1 ≤ n → ∀ E : ℂ,
      E ∈ sphere (hillRealGapCenter 0 hq hr n : ℂ)
        (hillRealGapHalfLength 0 hq hr n+hillRealGapCollar 0 hq hr n) →
      d ≤ ‖hillL2Radicand 0 E‖ := by
  obtain ⟨b,hb,hbound⟩ := exists_uniform_sine_lower_annulus
  refine ⟨4*b^2,by positivity,?_⟩
  intro n hn E hE
  have hg := hillFreeGapContour_frequency_bounds hq hr n hn E hE
  have hs := hbound (Complex.sqrt E-(n : ℂ)*Real.pi) hg.1 hg.2.1
  have hcos : cos ((n : ℂ)*Real.pi) = (-1 : ℂ)^n := by
    have h := congrArg Complex.ofReal (Real.cos_nat_mul_pi n)
    push_cast at h
    exact h
  have hnorm : ‖sin (Complex.sqrt E-(n : ℂ)*Real.pi)‖ = ‖sin (Complex.sqrt E)‖ := by
    rw [Complex.sin_sub,Complex.sin_nat_mul_pi,hcos,mul_zero,sub_zero,norm_mul,
      norm_pow,norm_neg,norm_one,one_pow,mul_one]
  rw [hnorm] at hs
  rw [hillL2Radicand_zero,norm_mul,norm_neg,norm_ofNat,norm_pow]
  nlinarith [sq_le_sq₀ hb.le (norm_nonneg (sin (Complex.sqrt E))) |>.mpr hs]

end NLS.KdV
