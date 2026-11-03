import NLS.KdV.HillHminusOneAllGapSquares
import NLS.ComplexAnalysis.CoshSquareRegularity

/-! # Noncritical squared-cosh coordinate on every actual H^-1 gap disc

The coordinate is regular on the real cut by its nonnegative profile.
Away from the cut, a critical value would force a characteristic zero,
which is excluded by the intrinsic gap-disc geometry.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem deriv_coshSquareCoordinate_hillHminusRealGapPrimitiveSquare_ne_zero
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ ball (hillHminusRealGapCenter q hr n : ℂ)
      (hillHminusRealGapHalfLength q hr n + 2 * hillHminusRealGapCollar q hr n)) :
    deriv coshSquareCoordinate (hillHminusRealGapPrimitiveSquare q n z) ≠ 0 := by
  by_cases hk : z ∈ segment ℝ (hillHminusRealLabels q hr (2*n-1) : ℂ)
      (hillHminusRealLabels q hr (2*n))
  · have hab := monotone_hillHminusRealLabels q hr (show 2*n-1 ≤ 2*n by omega)
    have hx := re_mem_Icc_of_mem_real_segment _ _ hab z hk
    have hi := im_eq_zero_of_mem_real_segment _ _ z hk
    have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    rw [hzC,hillHminusRealGapPrimitiveSquare_on_gap q hr n hn z.re hx]
    exact deriv_coshSquareCoordinate_sq_ne_zero _ (hillHminusRealGapProfile_nonneg q hr n hn z.re hx)
  · obtain ⟨_,_,_,_,hsub⟩ := hillHminusRealGapContour_geometry q hr n hn
    have hreg := hillHminusRadicand_ne_zero_on_realCutDomain q hr z (hsub ⟨hz,hk⟩)
    apply deriv_coshSquareCoordinate_ne_zero_of_value_sq_ne_one
    rw [hillHminusRealGapPrimitiveSquare_cosh q hr n z]
    intro hzero
    have hs : ((-1 : ℂ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul,Nat.mul_comm n 2,pow_mul]
      norm_num
    rw [div_pow,mul_pow,hs,one_mul] at hzero
    apply hreg
    change hillHminusDiscriminant q z ^ 2 - 4 = 0
    linear_combination 4 * hzero

end NLS.KdV
