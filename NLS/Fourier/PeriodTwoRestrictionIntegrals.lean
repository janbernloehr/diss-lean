import NLS.Fourier.PeriodTwoRestriction
import NLS.Fourier.IntervalCoefficientScaling

/-! # Physical Fourier integrals of the period-two restriction

Every input mode, including the odd modes, has the correct unit-interval
Fourier integral. Linearity identifies finite period-two polynomials exactly.
-/

noncomputable section
open Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Unit coefficients of a period-two wave retain the true frequency difference. -/
theorem intervalFourierCoefficient_one_wave (k n : ℤ) :
    intervalFourierCoefficient 1 (wave k) n = unitIntegral (k-2*n) := by
  simp only [intervalFourierCoefficient, div_one, Complex.ofReal_one, one_mul]
  unfold unitIntegral
  apply intervalIntegral.integral_congr
  intro x _
  have he : wave (-n) (2*x) = wave (-2*n) x := by
    unfold wave
    push_cast
    congr 1
    ring
  dsimp only
  rw [he, ← wave_add]
  congr 1
  ring

private theorem paritySample_single_same (r k : ℤ) (c : ℂ) :
    paritySample (p := p) r (Coeff.ofFinsupp (Finsupp.single (2*k+r) c)) =
      Coeff.ofFinsupp (Finsupp.single k c) := by
  ext n
  simp only [paritySample_apply, Coeff.ofFinsupp_apply, Finsupp.single_apply]
  have he : 2*k+r = 2*n+r ↔ k = n := by omega
  simp only [he]

private theorem paritySample_single_even_odd (k : ℤ) (c : ℂ) :
    paritySample (p := p) 0 (Coeff.ofFinsupp (Finsupp.single (2*k+1) c)) = 0 := by
  ext n
  simp [Coeff.ofFinsupp_apply, show 2*k+1 ≠ 2*n by omega]

private theorem paritySample_single_odd_even (k : ℤ) (c : ℂ) :
    paritySample (p := p) 1 (Coeff.ofFinsupp (Finsupp.single (2*k) c)) = 0 := by
  ext n
  simp [Coeff.ofFinsupp_apply, show 2*k ≠ 2*n+1 by omega]

/-- An even input mode is precisely the matching unit-period mode. -/
theorem periodTwoToUnit_single_even (hp1 : 1 < p) (hp : p ≠ ⊤) (k : ℤ) (c : ℂ) :
    periodTwoToUnit hp1 hp (Coeff.ofFinsupp (Finsupp.single (2*k) c)) =
      Coeff.ofFinsupp (Finsupp.single k c) := by
  have he := paritySample_single_same (p := p) 0 k c
  simp only [add_zero] at he
  ext n
  change paritySample 0 _ n + Complex.I * Coeff.shift 1 (shiftedHilbertTransform hp1 hp (paritySample 1 _)) n = _
  rw [he, paritySample_single_odd_even, map_zero]
  simp

/-- An odd input mode contributes the nonzero shifted reciprocal kernel. -/
theorem periodTwoToUnit_single_odd (hp1 : 1 < p) (hp : p ≠ ⊤) (k n : ℤ) (c : ℂ) :
    periodTwoToUnit hp1 hp (Coeff.ofFinsupp (Finsupp.single (2*k+1) c)) n =
      c * (2*Complex.I / ((Real.pi : ℂ)*(2*k-2*n+1))) := by
  change paritySample 0 _ n + Complex.I * Coeff.shift 1 (shiftedHilbertTransform hp1 hp (paritySample 1 _)) n = _
  rw [paritySample_single_even_odd, paritySample_single_same, Coeff.shift_apply,
    shiftedHilbertTransform_finite]
  simp only [lp.coeFn_zero, Pi.zero_apply, zero_add, Finsupp.sum_single_index, zero_mul, Int.cast_sub, Int.cast_one]
  have he : (2*(k : ℂ)-2*((n : ℂ)-1)-1) = 2*k-2*n+1 := by ring
  rw [he]
  ring

/-- Every period-two input mode has its actual physical unit-interval coefficients. -/
theorem periodTwoToUnit_single_integral (hp1 : 1 < p) (hp : p ≠ ⊤) (k n : ℤ) (c : ℂ) :
    periodTwoToUnit hp1 hp (Coeff.ofFinsupp (Finsupp.single k c)) n =
      c * intervalFourierCoefficient 1 (wave k) n := by
  rw [intervalFourierCoefficient_one_wave]
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he, periodTwoToUnit_single_even, show 2*(k/2)-2*n = 2*(k/2-n) by ring, unitIntegral_even]
    simp [Coeff.ofFinsupp_apply, Finsupp.single_apply, sub_eq_zero]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he, periodTwoToUnit_single_odd, show 2*(k/2)+1-2*n = 2*(k/2-n)+1 by ring, unitIntegral_odd]
    push_cast
    ring

/-- Finite synthesis in the raw period-two Fourier convention. -/
def periodTwoPolynomial (a : ℤ →₀ ℂ) (x : ℝ) : ℂ := a.sum (fun k c => c * wave k x)

@[fun_prop] theorem continuous_periodTwoPolynomial (a : ℤ →₀ ℂ) : Continuous (periodTwoPolynomial a) := by
  unfold periodTwoPolynomial Finsupp.sum
  fun_prop

/-- Restriction agrees with the physical unit Fourier integral on every finite input. -/
theorem periodTwoToUnit_finite_integral (hp1 : 1 < p) (hp : p ≠ ⊤) (a : ℤ →₀ ℂ) (n : ℤ) :
    periodTwoToUnit hp1 hp (Coeff.ofFinsupp a) n =
      intervalFourierCoefficient 1 (periodTwoPolynomial a) n := by
  classical
  have he : Coeff.ofFinsupp (p := p) a =
      ∑ k ∈ a.support, Coeff.ofFinsupp (Finsupp.single k (a k)) := by
    rw [← map_sum]
    congr 1
    exact (Finsupp.sum_single a).symm
  rw [he, map_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply, periodTwoToUnit_single_integral]
  simp only [intervalFourierCoefficient, div_one, Complex.ofReal_one, one_mul,
    periodTwoPolynomial, Finsupp.sum, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    ring
  · intro k _
    exact ((continuous_const.mul (continuous_wave k)).mul
      ((continuous_wave (-n)).comp (continuous_const.mul continuous_id))).intervalIntegrable 0 1

end NLS.Fourier
