import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Fourier integrals on the half period

The period-two wave is `exp(i π n x)`. Its integral over `[0,1]` gives the
normalization and shifted reciprocal kernel in Chapter 1, equations (1.8)–(1.9)
and the proof of Lemma 4.3. All signs and constants here follow from actual
interval integrals, including the normalized period-two factor `1/2`.
-/

noncomputable section
open Complex intervalIntegral
open scoped ComplexConjugate
namespace NLS.Fourier

/-- The period-two Fourier wave, in the raw coefficient convention used by both components. -/
def wave (n : ℤ) (x : ℝ) : ℂ := exp (((Real.pi : ℂ) * I * n) * x)

@[simp] theorem wave_zero (x : ℝ) : wave 0 x = 1 := by simp [wave]
@[simp] theorem wave_at_zero (n : ℤ) : wave n 0 = 1 := by simp [wave]

@[fun_prop] theorem continuous_wave (n : ℤ) : Continuous (wave n) := by unfold wave; fun_prop

theorem wave_add (n m : ℤ) (x : ℝ) : wave (n + m) x = wave n x * wave m x := by
  simp only [wave, Int.cast_add]
  rw [mul_add, add_mul, exp_add]

theorem wave_neg (n : ℤ) (x : ℝ) : wave (-n) x = conj (wave n x) := by
  simp only [wave, Int.cast_neg, mul_neg, neg_mul, ← exp_conj]
  congr 1
  simp

theorem wave_reflect (n : ℤ) (x : ℝ) : wave n (2 - x) = wave (-n) x := by
  have he : ((Real.pi : ℂ) * I * n) * (2 - x) =
      (n : ℂ) * (2 * Real.pi * I) + ((Real.pi : ℂ) * I * (-n)) * x := by ring
  simp only [wave, ofReal_sub, ofReal_ofNat, Int.cast_neg]
  rw [he, exp_add, exp_int_mul_two_pi_mul_I, one_mul]

theorem wave_even_at_one (k : ℤ) : wave (2 * k) 1 = 1 := by
  have he : ((Real.pi : ℂ) * I * (2 * k)) = (k : ℂ) * (2 * Real.pi * I) := by ring
  simp [wave, he, exp_int_mul_two_pi_mul_I]

theorem wave_odd_at_one (k : ℤ) : wave (2 * k + 1) 1 = -1 := by
  rw [wave_add, wave_even_at_one]
  simp [wave, exp_pi_mul_I]

/-- Integral of a Fourier wave over the original unit interval. -/
def unitIntegral (n : ℤ) : ℂ := ∫ x in (0 : ℝ)..1, wave n x

@[simp] theorem unitIntegral_zero : unitIntegral 0 = 1 := by simp [unitIntegral]

theorem unitIntegral_of_ne_zero (n : ℤ) (hn : n ≠ 0) :
    unitIntegral n = (wave n 1 - 1) / ((Real.pi : ℂ) * I * n) := by
  have hc : (Real.pi : ℂ) * I * n ≠ 0 := mul_ne_zero
    (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero) (by exact_mod_cast hn)
  simpa [unitIntegral, wave] using (integral_exp_mul_complex (a := 0) (b := 1) hc)

/-- Nonconstant even Fourier modes integrate to zero on the unit interval. -/
theorem unitIntegral_even (k : ℤ) : unitIntegral (2 * k) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · simp [hk]
  · rw [unitIntegral_of_ne_zero _ (by omega), wave_even_at_one]
    simp

/-- The odd half-period modes give the shifted discrete Hilbert kernel, with its exact factor. -/
theorem unitIntegral_odd (k : ℤ) :
    unitIntegral (2 * k + 1) = 2 * I / ((Real.pi : ℂ) * (2 * k + 1)) := by
  have hn : (2 * k + 1 : ℤ) ≠ 0 := by omega
  have hz : (2 * (k : ℂ) + 1) ≠ 0 := by exact_mod_cast hn
  rw [unitIntegral_of_ne_zero _ hn, wave_odd_at_one]
  push_cast
  field_simp
  simp
  ring

/-- The normalized overlap between an input period-one mode and an output period-two mode. -/
def overlap (k n : ℤ) : ℂ := (1 / 2 : ℂ) * ∫ x in (0 : ℝ)..1, wave (2 * k) x * wave (-n) x

theorem overlap_eq_unitIntegral (k n : ℤ) : overlap k n = (1 / 2 : ℂ) * unitIntegral (2 * k - n) := by
  unfold overlap unitIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  change wave (2 * k) x * wave (-n) x = wave (2 * k - n) x
  rw [← wave_add, sub_eq_add_neg]

/-- Even output indices retain half the input coefficient at the matching frequency. -/
theorem overlap_even (k l : ℤ) : overlap k (2 * l) = if k = l then 1 / 2 else 0 := by
  rw [overlap_eq_unitIntegral, show 2 * k - 2 * l = 2 * (k - l) by ring, unitIntegral_even]
  by_cases h : k = l <;> simp [h, sub_eq_zero]

/-- Odd output indices give the shifted reciprocal kernel with factor `i/π`. -/
theorem overlap_odd (k l : ℤ) :
    overlap k (2 * l + 1) = I / ((Real.pi : ℂ) * (2 * k - 2 * l - 1)) := by
  rw [overlap_eq_unitIntegral, show 2 * k - (2 * l + 1) = 2 * (k - l - 1) + 1 by ring,
    unitIntegral_odd]
  push_cast
  ring

end NLS.Fourier
