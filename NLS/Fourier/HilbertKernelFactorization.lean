import NLS.Fourier.HilbertKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # A factorization of the ordinary discrete Hilbert kernel

The kernel -1/n is the sum of an ℓ² sequence and its one-step shift. Integral
remainders of the alternating harmonic series supply the decaying factor.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- Positive integral remainders of the alternating harmonic series. -/
def alternatingHarmonicRemainder (n : ℕ) : ℝ := ∫ x in (0:ℝ)..1, x^n/(1+x)

private theorem remainder_integrable (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => x^n/(1+x)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (continuous_pow n).continuousOn (continuous_const.add continuous_id).continuousOn
  intro x hx
  have hx0 : 0 ≤ x := (uIcc_of_le (by norm_num : (0:ℝ) ≤ 1) ▸ hx).1
  change 1+x ≠ 0
  linarith

/-- The remainders are nonnegative and decay at least harmonically. -/
theorem alternatingHarmonicRemainder_bounds (n : ℕ) :
    0 ≤ alternatingHarmonicRemainder n ∧ alternatingHarmonicRemainder n ≤ 1/(n+1:ℝ) := by
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact div_nonneg (pow_nonneg hx.1 n) (by linarith [hx.1])
  · have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      (remainder_integrable n) ((continuous_pow n).intervalIntegrable 0 1)
      (fun x hx => div_le_self (pow_nonneg hx.1 n) (by linarith [hx.1]))
    simpa only [alternatingHarmonicRemainder,integral_pow,one_pow,
      zero_pow (Nat.succ_ne_zero n),sub_zero] using h

/-- Adjacent remainders sum to the reciprocal integer. -/
theorem alternatingHarmonicRemainder_add_succ (n : ℕ) :
    alternatingHarmonicRemainder n + alternatingHarmonicRemainder (n+1) = 1/(n+1:ℝ) := by
  rw [alternatingHarmonicRemainder,alternatingHarmonicRemainder,
    ← intervalIntegral.integral_add (remainder_integrable n) (remainder_integrable (n+1))]
  have he : (∫ x in (0:ℝ)..1, x^n/(1+x)+x^(n+1)/(1+x)) = ∫ x in (0:ℝ)..1, x^n := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 ≤ x := (uIcc_of_le (by norm_num : (0:ℝ) ≤ 1) ▸ hx).1
    dsimp only
    rw [pow_succ]
    field_simp [show 1+x ≠ 0 by linarith]
  rw [he,integral_pow]
  simp

/-- A decaying bilateral factor whose neighboring values recover the Hilbert kernel. -/
def hilbertKernelFactor : ℤ → ℂ
  | .ofNat n => -(alternatingHarmonicRemainder n : ℂ)
  | .negSucc n => (alternatingHarmonicRemainder n : ℂ)

/-- A summable-power envelope for the factor. -/
theorem norm_hilbertKernelFactor_le (n : ℤ) :
    ‖hilbertKernelFactor n‖ ≤ 2*(1+|(n:ℝ)|)⁻¹ := by
  cases n with
  | ofNat n =>
    simp only [hilbertKernelFactor,norm_neg,Complex.norm_of_nonneg (alternatingHarmonicRemainder_bounds n).1,
      Int.ofNat_eq_natCast,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    have h := (alternatingHarmonicRemainder_bounds n).2
    have hp : 0 < (n:ℝ)+1 := by positivity
    rw [show (1+(n:ℝ)) = n+1 by ring,← div_eq_mul_inv]
    exact h.trans (by gcongr; norm_num)
  | negSucc n =>
    simp only [hilbertKernelFactor,Complex.norm_of_nonneg (alternatingHarmonicRemainder_bounds n).1,
      Int.cast_negSucc,Nat.cast_add,Nat.cast_one,abs_neg,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)+1)]
    apply (alternatingHarmonicRemainder_bounds n).2.trans
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The factor belongs to every finite-power sequence space above one. -/
theorem hilbertKernelFactor_memlp {p : ℝ≥0∞} (hp : 1 < p) : Memℓp hilbertKernelFactor p := by
  apply ((Weight.inverse_sobolev_one_memlp hp).norm.const_mul (2:ℝ)).mono
  intro n
  simpa only [norm_inv,Complex.norm_real,Real.norm_eq_abs,Weight.sobolev_apply,
    Real.rpow_one,abs_of_pos (by positivity : 0 < 1+|(n:ℝ)|)] using norm_hilbertKernelFactor_le n

/-- The factorization includes the zero diagonal. -/
theorem hilbertKernel_factorization (n : ℤ) :
    hilbertKernel n = hilbertKernelFactor n + hilbertKernelFactor (n-1) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      norm_num only [Int.ofNat_zero, zero_sub, hilbertKernel, Int.cast_zero, inv_zero, neg_zero]
      change (0:ℂ) = -(alternatingHarmonicRemainder 0:ℂ)+(alternatingHarmonicRemainder 0:ℂ)
      ring
    | succ n =>
      have he : Int.ofNat (n+1)-1 = Int.ofNat n := by simp only [Int.ofNat_eq_natCast]; omega
      rw [he]
      simp only [hilbertKernelFactor,hilbertKernel,Int.ofNat_eq_natCast,Nat.cast_add,Nat.cast_one,Int.cast_add,Int.cast_natCast,Int.cast_one]
      have h := congrArg Complex.ofReal (alternatingHarmonicRemainder_add_succ n)
      push_cast at h
      rw [one_div] at h
      linear_combination h
  | negSucc n =>
    have he : Int.negSucc n-1 = Int.negSucc (n+1) := by omega
    rw [he]
    simp only [hilbertKernelFactor,hilbertKernel,Int.cast_negSucc,Nat.cast_add,Nat.cast_one,inv_neg,neg_neg]
    have h := congrArg Complex.ofReal (alternatingHarmonicRemainder_add_succ n)
    push_cast at h
    simpa only [one_div] using h.symm

end NLS.Fourier
