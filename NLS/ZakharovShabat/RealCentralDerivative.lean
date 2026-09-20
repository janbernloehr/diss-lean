import NLS.ZakharovShabat.CentralPolynomialAnalytic
import NLS.ZakharovShabat.RealType
import NLS.ComplexAnalysis.RealRootedDerivatives

/-!
# Real critical points of the finite central polynomials

The central algebraic count supplies positive degree for every large cutoff.
Reality of the original spectrum and Gauss–Lucas then exclude nonreal zeros
of the normalized central polynomials' derivatives.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every sufficiently large central spectral polynomial has positive degree. -/
theorem exists_cutoff_positive_central_multiplicity (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N : ℕ, ∀ K : ℕ, N ≤ K → ∃ a ∈ centralPeriodicSpectrum hp φ K,
      0 < periodicAlgebraicMultiplicity hp φ a := by
  obtain ⟨N, U, _, _, _, hφ, _, _, h⟩ := exists_uniform_central_multiplicity hp φ
  refine ⟨N, fun K hK => Finset.sum_pos_iff.mp ?_⟩
  rw [(h φ hφ K hK).2.2]
  omega

/-- Positive-degree central approximants for real-type potentials have no nonreal critical points. -/
theorem deriv_normalizedCentral_ne_zero_of_realType (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : IsRealType φ) (N : ℕ)
    (hpos : ∃ a ∈ centralPeriodicSpectrum hp φ N, 0 < periodicAlgebraicMultiplicity hp φ a)
    {z : ℂ} (hz : z.im ≠ 0) : deriv (normalizedCentralPeriodicPolynomial hp φ N) z ≠ 0 := by
  change deriv (fun w => -4*centralPeriodicPolynomial hp φ N w/centralSpectralNormalization N) z ≠ 0
  rw [deriv_div_const, deriv_const_mul_field]
  apply div_ne_zero (mul_ne_zero (by norm_num) ?_) (centralSpectralNormalization_ne_zero N)
  exact NLS.ComplexAnalysis.deriv_prod_real_factors_ne_zero _ _
    (fun a ha => periodicSpectrum_im_eq_zero_of_realType hp φ hφ a
      ((mem_centralPeriodicSpectrum hp φ N a).mp ha).1) hpos hz

/-- One cutoff excludes nonreal critical points from every subsequent normalized central approximant. -/
theorem exists_cutoff_real_normalizedCentral_derivative (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : IsRealType φ) : ∃ N : ℕ, ∀ K : ℕ, N ≤ K → ∀ z : ℂ, z.im ≠ 0 →
      deriv (normalizedCentralPeriodicPolynomial hp φ K) z ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_cutoff_positive_central_multiplicity hp φ
  exact ⟨N, fun K hK z hz => deriv_normalizedCentral_ne_zero_of_realType hp φ hφ K (hN K hK) hz⟩

end NLS.ZakharovShabat
