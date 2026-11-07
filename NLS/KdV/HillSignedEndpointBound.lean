import NLS.KdV.HillNativeComplexCoordinates
import NLS.SequenceSpaces.SignedEndpointSquareRootBound

/-! Native signed endpoint bounds from the actual two action-angle factors. -/
noncomputable section
open Set Complex
namespace NLS.KdV

theorem norm_div_sqrt_two_le (z : ℂ) : ‖z/(Real.sqrt 2:ℂ)‖ ≤ ‖z‖ := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_self (norm_nonneg _) (by norm_num)

theorem hillHminusNativeComplexMap_positive_endpoint_bound
    (r : ℝ) (hr : 0 ≤ r) (q : PeriodOneHminusOne)
    (hnative : q ∈ hillHminusActionAngleNativeDomain) (C A : ℝ) (hC : 0 ≤ C) (n : ℕ+)
    (hF : ‖hillHminusActionAngleFactorMinus n q‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n q)
    (hW : Weight.sobolev (-r) (n:ℤ)*hillHminusCanonicalCartesianWeight n q ≤ A) :
      ‖(Weight.signedSobolev (1/2-r) (n:ℤ):ℂ)*
        (hillHminusNativeComplexMap q).val (n:ℤ)‖ ≤ ((2:ℝ)^r*C*A) := by
  rw [hillHminusNativeComplexMap_positive _ hnative]
  exact Weight.signed_endpoint_mul_le r hr n _ C _ A hC
      (hillHminusCanonicalCartesianWeight_nonneg _ _)
      ((norm_div_sqrt_two_le _).trans hF) hW

theorem hillHminusNativeComplexMap_negative_endpoint_bound
    (r : ℝ) (hr : 0 ≤ r) (q : PeriodOneHminusOne)
    (hnative : q ∈ hillHminusActionAngleNativeDomain) (C A : ℝ) (hC : 0 ≤ C) (n : ℕ+)
    (hF : ‖hillHminusActionAngleFactorPlus n q‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n q)
    (hW : Weight.sobolev (-r) (n:ℤ)*hillHminusCanonicalCartesianWeight n q ≤ A) :
      ‖(Weight.signedSobolev (1/2-r) (-(n:ℤ)):ℂ)*
        (hillHminusNativeComplexMap q).val (-(n:ℤ))‖ ≤ ((2:ℝ)^r*C*A) := by
  rw [Weight.signedSobolev_neg,hillHminusNativeComplexMap_negative _ hnative]
  exact Weight.signed_endpoint_mul_le r hr n _ C _ A hC
      (hillHminusCanonicalCartesianWeight_nonneg _ _)
      ((norm_div_sqrt_two_le _).trans hF) hW

theorem hillHminusNativeComplexMap_signed_endpoint_bound
    (r : ℝ) (hr : 0 ≤ r) (q : PeriodOneHminusOne)
    (hnative : q ∈ hillHminusActionAngleNativeDomain) (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hF : ∀ n : ℕ+, ‖hillHminusActionAngleFactorPlus n q‖ ≤
      (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n q ∧
      ‖hillHminusActionAngleFactorMinus n q‖ ≤
      (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n q)
    (hW : ∀ n : ℕ+, Weight.sobolev (-r) (n:ℤ)*hillHminusCanonicalCartesianWeight n q ≤ A)
    (k : ℤ) : ‖(Weight.signedSobolev (1/2-r) k:ℂ)*(hillHminusNativeComplexMap q).val k‖ ≤ (2:ℝ)^r*C*A := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (ne_of_lt hk)⟩
    have he : -(n:ℤ)=k := by
      change -((k.natAbs:ℕ):ℤ)=k
      rw [Int.natCast_natAbs,abs_of_neg hk,neg_neg]
    simpa only [he] using hillHminusNativeComplexMap_negative_endpoint_bound r hr q hnative C A hC n (hF n).1 (hW n)
  · rw [hillHminusNativeComplexMap_zero_mode,mul_zero,norm_zero]
    positivity
  · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (ne_of_gt hk)⟩
    have he : (n:ℤ)=k := by
      change ((k.natAbs:ℕ):ℤ)=k
      rw [Int.natCast_natAbs,abs_of_pos hk]
    simpa only [he] using hillHminusNativeComplexMap_positive_endpoint_bound r hr q hnative C A hC n (hF n).2 (hW n)

end NLS.KdV
