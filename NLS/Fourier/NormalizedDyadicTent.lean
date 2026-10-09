import NLS.Fourier.DyadicGeometricBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Area-normalized reflected tents on dyadic intervals -/
noncomputable section
open Complex MeasureTheory Set intervalIntegral
namespace NLS.Fourier

/-- The j-th spatial scale. -/
def dyadicTentWidth (j : ℕ) : ℝ := (1/2)^j

/-- An early tent and its reflected negative, normalized to unit positive area. -/
def normalizedDyadicTent (j : ℕ) (x : ℝ) : ℝ :=
  (4*4^j)*oddTentProfile (dyadicTentWidth j) (2*dyadicTentWidth j) x

@[fun_prop] theorem continuous_normalizedDyadicTent (j : ℕ) : Continuous (normalizedDyadicTent j) := by
  unfold normalizedDyadicTent
  fun_prop

theorem dyadicTentWidth_pos (j : ℕ) : 0 < dyadicTentWidth j := by unfold dyadicTentWidth; positivity

theorem dyadicTentWidth_le_quarter (j : ℕ) (hj : 2 ≤ j) : dyadicTentWidth j ≤ 1/4 := by
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) hj
  norm_num only [show (1/2 : ℝ)^2 = 1/4 by norm_num] at h
  exact h

/-- The normalization cancels the squared tent width exactly. -/
theorem four_pow_mul_dyadicTentWidth_sq (j : ℕ) : (4 : ℝ)^j * (dyadicTentWidth j)^2 = 1 := by
  unfold dyadicTentWidth
  rw [← pow_mul, Nat.mul_comm j 2, pow_mul, ← mul_pow]
  norm_num

/-- No mass reaches either endpoint. -/
theorem normalizedDyadicTent_endpoints (j : ℕ) (hj : 2 ≤ j) :
    normalizedDyadicTent j 0 = 0 ∧ normalizedDyadicTent j 1 = 0 := by
  have hd := dyadicTentWidth_pos j
  have hb := dyadicTentWidth_le_quarter j hj
  constructor
  · rw [normalizedDyadicTent,oddTentProfile_eq_zero_near_ends _ _ (by linarith) (by linarith)
      (Or.inl hd.le),mul_zero]
  · rw [normalizedDyadicTent,oddTentProfile_eq_zero_near_ends _ _ (by linarith) (by linarith)
      (Or.inr (by linarith)),mul_zero]

theorem periodOneCoefficient_normalizedDyadicTent (j : ℕ) (n : ℤ) :
    periodOneCoefficient (fun x => (normalizedDyadicTent j x : ℂ)) n =
      ((4*4^j : ℝ) : ℂ)*periodOneCoefficient
        (fun x => (oddTentProfile (dyadicTentWidth j) (2*dyadicTentWidth j) x : ℂ)) n := by
  simp only [normalizedDyadicTent,ofReal_mul,periodOneCoefficient]
  exact fourierCoeffOn.const_mul _ _ n (by norm_num)

@[simp] theorem periodOneCoefficient_normalizedDyadicTent_zero (j : ℕ) :
    periodOneCoefficient (fun x => (normalizedDyadicTent j x : ℂ)) 0 = 0 := by
  rw [periodOneCoefficient_normalizedDyadicTent,periodOneCoefficient_oddTentProfile_zero,mul_zero]

/-- Linear cancellation in the low-frequency regime, with a rational constant. -/
theorem norm_periodOneCoefficient_normalizedDyadicTent_low (j : ℕ) (hj : 2 ≤ j) (n : ℤ) :
    ‖periodOneCoefficient (fun x => (normalizedDyadicTent j x : ℂ)) n‖ ≤
      32*|(n : ℝ)| *(1/2 : ℝ)^j := by
  have hd := dyadicTentWidth_pos j
  have hb := dyadicTentWidth_le_quarter j hj
  have h := norm_periodOneCoefficient_oddTentProfile_le_low (dyadicTentWidth j) (2*dyadicTentWidth j)
    hd.le (by linarith) (by linarith) n
  rw [periodOneCoefficient_normalizedDyadicTent,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4*4^j)]
  calc
    _ ≤ (4*4^j)*(Real.pi*|(n : ℝ)| *(2*dyadicTentWidth j)*(2*dyadicTentWidth j-dyadicTentWidth j)^2) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = 8*Real.pi*|(n : ℝ)| *dyadicTentWidth j := by
      have he := four_pow_mul_dyadicTentWidth_sq j
      linear_combination (8*Real.pi*|(n : ℝ)| *dyadicTentWidth j)*he
    _ ≤ _ := by
      change _ ≤ 32*|(n : ℝ)| *dyadicTentWidth j
      have hπ := Real.pi_lt_four.le
      nlinarith [mul_nonneg (abs_nonneg (n : ℝ)) hd.le]

/-- Quadratic high-frequency decay, again with a rational envelope. -/
theorem norm_periodOneCoefficient_normalizedDyadicTent_high (j : ℕ) (hj : 2 ≤ j) (n : ℤ) :
    |(n : ℝ)|^2 * ‖periodOneCoefficient (fun x => (normalizedDyadicTent j x : ℂ)) n‖ ≤ 8*(4 : ℝ)^j := by
  have hd := dyadicTentWidth_pos j
  have hb := dyadicTentWidth_le_quarter j hj
  have h := norm_periodOneCoefficient_oddTentProfile_mul_frequency_le (dyadicTentWidth j) (2*dyadicTentWidth j)
    hd.le (by linarith) (by linarith) n
  have hπ : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hn := norm_nonneg (periodOneCoefficient (fun x =>
    (oddTentProfile (dyadicTentWidth j) (2*dyadicTentWidth j) x : ℂ)) n)
  have hh : |(n : ℝ)|^2 * ‖periodOneCoefficient (fun x =>
      (oddTentProfile (dyadicTentWidth j) (2*dyadicTentWidth j) x : ℂ)) n‖ ≤ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) hn]
  rw [periodOneCoefficient_normalizedDyadicTent,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4*4^j)]
  nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 4*4^j)]

/-- The lower interaction estimate has no remaining area factor after normalization. -/
theorem integral_normalizedDyadicTent_lower (j : ℕ) (hj : 2 ≤ j) (H : ℝ) (hH : 0 ≤ H) :
    Real.exp (-4*H*dyadicTentWidth j)-Real.exp (-2*H*(1-2*dyadicTentWidth j)) ≤
      ∫ x in (0 : ℝ)..1, normalizedDyadicTent j x*Real.exp (-2*H*x) := by
  have hd := dyadicTentWidth_pos j
  have hb := dyadicTentWidth_le_quarter j hj
  have h := integral_oddTentProfile_mul_exp_lower (dyadicTentWidth j) (2*dyadicTentWidth j)
    hd.le (by linarith) (by linarith) H hH
  calc
    _ = (4*4^j)*((Real.exp (-2*H*(2*dyadicTentWidth j))-
        Real.exp (-2*H*(1-2*dyadicTentWidth j)))*(2*dyadicTentWidth j-dyadicTentWidth j)^2/4) := by
      have he := four_pow_mul_dyadicTentWidth_sq j
      rw [show -2*H*(2*dyadicTentWidth j) = -4*H*dyadicTentWidth j by ring]
      linear_combination -(Real.exp (-4*H*dyadicTentWidth j)-Real.exp (-2*H*(1-2*dyadicTentWidth j)))*he
    _ ≤ (4*4^j)*(∫ x in (0 : ℝ)..1,
        oddTentProfile (dyadicTentWidth j) (2*dyadicTentWidth j) x*Real.exp (-2*H*x)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [normalizedDyadicTent]
      ring

/-- Every sufficiently fine scale contributes at least one quarter. -/
theorem integral_normalizedDyadicTent_ge_quarter (j : ℕ) (hj : 2 ≤ j)
    (H : ℝ) (hH : 3 ≤ H) (hscale : H*dyadicTentWidth j ≤ 1/8) :
    (1/4 : ℝ) ≤ ∫ x in (0 : ℝ)..1, normalizedDyadicTent j x*Real.exp (-2*H*x) := by
  have hd := dyadicTentWidth_le_quarter j hj
  have hearly : (1/2 : ℝ) ≤ Real.exp (-4*H*dyadicTentWidth j) := by
    have h := Real.add_one_le_exp (-4*H*dyadicTentWidth j)
    linarith
  have hlate : Real.exp (-2*H*(1-2*dyadicTentWidth j)) ≤ 1/4 := by
    calc
      _ ≤ Real.exp (-H) := by apply Real.exp_le_exp.mpr; nlinarith
      _ ≤ _ := by
        rw [Real.exp_neg]
        have h : 4 ≤ Real.exp H := by linarith [Real.add_one_le_exp H]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) h
  exact (by linarith : (1/4 : ℝ) ≤ _).trans
    (integral_normalizedDyadicTent_lower j hj H (by linarith))

end NLS.Fourier
