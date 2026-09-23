import NLS.Fourier.PeriodOneCoefficients
import NLS.Fourier.IntervalL2Realization
import NLS.SequenceSpaces.FiniteCoefficients

/-! # Physical realization of finite period-one coefficients
Finite Fourier polynomials agree with the continuous period-one synthesis,
with the exact even-frequency period-two coefficients. Conjugate-reflected
coefficient pairs give pointwise conjugate physical functions.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped ENNReal ComplexConjugate
namespace NLS.Fourier

/-- A finite Fourier polynomial is its finite-support infinite series. -/
theorem polynomial_eq_tsum (a : ℤ →₀ ℂ) (x : ℝ) :
    polynomial a x = ∑' n : ℤ, a n * wave (2*n) x := by
  symm
  exact tsum_eq_sum fun n hn => by simp [Finsupp.notMem_support_iff.mp hn]

/-- The continuous period-one synthesis of finite input is the literal polynomial. -/
theorem periodOneSynthesis_ofFinsupp (a : ℤ →₀ ℂ) :
    periodOneSynthesis (Coeff.ofFinsupp a) = polynomial a := by
  funext x
  rw [periodOneSynthesis_eq_tsum, polynomial_eq_tsum]
  rfl

/-- Actual period-two Fourier integrals of a finite polynomial are its even insertion. -/
theorem periodTwoCoefficient_polynomial {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : ℤ →₀ ℂ) (n : ℤ) :
    periodTwoCoefficient (polynomial a) n = Coeff.periodDouble (Coeff.ofFinsupp (p := p) a) n := by
  rw [← periodOneSynthesis_ofFinsupp, periodTwoCoefficient_periodOneSynthesis]
  rfl

/-- Hilbert Fourier coefficients of a finite polynomial retain exactly its even insertion. -/
theorem periodTwoL2Coefficients_polynomial (a : ℤ →₀ ℂ)
    (ha : MemLp (polynomial a) 2 (volume.restrict (Ioc 0 2))) :
    periodTwoL2Coefficients (polynomial a) ha = Coeff.periodDouble (Coeff.ofFinsupp a) := by
  ext n
  exact periodTwoCoefficient_polynomial a n

/-- The actual Hilbert synthesis reconstructs the finite period-one polynomial almost everywhere. -/
theorem circlePullback_periodDouble_ofFinsupp (a : ℤ →₀ ℂ) :
    circlePullback (l2Synthesis (Coeff.periodDouble (Coeff.ofFinsupp a)))
      =ᵐ[volume.restrict (Ioc 0 2)] polynomial a := by
  have ha := memLp_two_interval (continuous_polynomial a) 0 2 (by norm_num)
  rw [← periodTwoL2Coefficients_polynomial a ha]
  exact circlePullback_periodTwoL2Coefficients _ ha

/-- Conjugate reflection of finite coefficients is complex conjugation at every physical point. -/
theorem polynomial_conj_of_coefficients (a b : ℤ →₀ ℂ)
    (h : ∀ n, b n = conj (a (-n))) (x : ℝ) : polynomial b x = conj (polynomial a x) := by
  rw [polynomial_eq_tsum, polynomial_eq_tsum, Complex.conj_tsum]
  simp only [h, map_mul]
  have he := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => conj (a n) * conj (wave (2*n) x))
  simpa only [Equiv.neg_apply, mul_neg, wave_neg, starRingEnd_self_apply] using he

end NLS.Fourier
