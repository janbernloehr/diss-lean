import NLS.KdV.PseudomeasureWideWeightedErrors
import NLS.SequenceSpaces.WeightedFourierTail

/-! Sharp comparison of source mode and double-mode weights, and the
literal closed Fourier tail needed in Lemma 2.12. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

theorem negativeSobolev_mode_le_sqrt_two_double (w : SpectralWeight) (r : ℝ)
    (hr : 0≤r) (hr1 : r<1/2) (n : ℕ) :
    w.negativeSobolev r n≤Real.sqrt 2*w.negativeSobolev r (2*(n:ℤ)) := by
  have hw : w n≤w (2*(n:ℤ)) := w.mono_abs (by
    rw [abs_of_nonneg (Int.natCast_nonneg n),abs_of_nonneg (by positivity : (0:ℤ)≤2*(n:ℤ))]
    omega)
  have hS : Weight.sobolev r (2*(n:ℤ))≤Real.sqrt 2*Weight.sobolev r n := by
    have hn0 : (0:ℝ)≤n := by positivity
    have htwo : (2:ℝ)^r≤Real.sqrt 2 := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hr1.le
    calc
      _ = (1+2*(n:ℝ))^r := by simp only [Weight.sobolev_apply,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,abs_of_nonneg (by positivity : (0:ℝ)≤2*(n:ℝ))]
      _ ≤ (2*(1+(n:ℝ)))^r := Real.rpow_le_rpow (by positivity) (by linarith) hr
      _ = (2:ℝ)^r*Weight.sobolev r n := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity : (0:ℝ)≤1+(n:ℝ))]
        simp only [Weight.sobolev_apply,Int.cast_natCast,abs_of_nonneg hn0]
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo ((Weight.sobolev r).positive _).le
  simp only [SpectralWeight.negativeSobolev_apply]
  apply (div_le_iff₀ ((Weight.sobolev r).positive (n:ℤ))).mpr
  have hprod := mul_le_mul hw hS ((Weight.sobolev r).positive _).le (w.positive _).le
  have hden := ((Weight.sobolev r).positive (2*(n:ℤ))).ne'
  apply (mul_le_mul_iff_right₀ ((Weight.sobolev r).positive (2*(n:ℤ)))).mp
  calc
    _ = w n*Weight.sobolev r (2*(n:ℤ)) := mul_comm _ _
    _ ≤ w (2*(n:ℤ))*(Real.sqrt 2*Weight.sobolev r n) := hprod
    _ = _ := by field_simp [hden]

theorem negativeSobolev_fourierTail_coefficient (w : SpectralWeight) (r : ℝ)
    (N : ℕ) (q : WeightedCoeff (w.negativeSobolev r) ⊤) (k : ℤ) (hk : N≤k.natAbs) :
    w.negativeSobolev r k*‖q.val k‖≤‖WeightedCoeff.fourierTail (w.negativeSobolev r) N q‖ := by
  have h := WeightedCoeff.norm_apply_le (w.negativeSobolev r) ⊤
    (WeightedCoeff.fourierTail (w.negativeSobolev r) N q) k
  rw [WeightedCoeff.fourierTail_apply,if_pos hk] at h
  simpa only [mul_comm] using (le_div_iff₀ ((w.negativeSobolev r).positive k)).mp h

end NLS.KdV
