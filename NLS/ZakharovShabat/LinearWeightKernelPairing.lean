import NLS.ZakharovShabat.LinearWeightKernel
import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.MeanInequalities

/-! # Cauchy–Schwarz for the Section 25 double kernel

The full coefficient product on the two-dimensional lattice has exactly the
product of the two Hilbert norms. This gives absolute convergence and the
constant four for the actual complementary-symbol kernel.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem coeff_sq_summable (a : Coeff 2) : Summable (fun k : ℤ => ‖a k‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (lp.memℓp a).summable (by norm_num)

private theorem coeff_sq_tsum (a : Coeff 2) : (∑' k : ℤ, ‖a k‖^2) = ‖a‖^2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) a).symm

/-- The two coefficient factors have a summable square on the full lattice. -/
theorem summable_convolution_coeff_product_sq (a b : Coeff 2) :
    Summable (fun p : ℤ × ℤ => (‖a (p.2+p.1)‖*‖b p.1‖)^2) := by
  apply (summable_prod_of_nonneg (f := fun p : ℤ × ℤ => (‖a (p.2+p.1)‖*‖b p.1‖)^2)
    (fun _ => sq_nonneg _)).mpr
  constructor
  · intro l
    simp only [mul_pow]
    exact ((coeff_sq_summable a).comp_injective (Equiv.addRight l).injective).mul_right (‖b l‖^2)
  · have he (l : ℤ) : (∑' k : ℤ, (‖a (k+l)‖*‖b l‖)^2) = ‖a‖^2*‖b l‖^2 := by
      simp only [mul_pow, tsum_mul_right]
      rw [show (∑' k : ℤ, ‖a (k+l)‖^2) = ∑' k : ℤ, ‖a k‖^2 from
        (Equiv.addRight l).tsum_eq (fun k => ‖a k‖^2), coeff_sq_tsum]
    simp only [he]
    exact (coeff_sq_summable b).mul_left _

/-- Translation in the first index leaves the exact product of squared norms. -/
theorem tsum_convolution_coeff_product_sq (a b : Coeff 2) :
    (∑' p : ℤ × ℤ, (‖a (p.2+p.1)‖*‖b p.1‖)^2) = (‖a‖*‖b‖)^2 := by
  rw [(summable_convolution_coeff_product_sq a b).tsum_prod]
  have he (l : ℤ) : (∑' k : ℤ, (‖a (k+l)‖*‖b l‖)^2) = ‖a‖^2*‖b l‖^2 := by
    simp only [mul_pow, tsum_mul_right]
    rw [show (∑' k : ℤ, ‖a (k+l)‖^2) = ∑' k : ℤ, ‖a k‖^2 from
      (Equiv.addRight l).tsum_eq (fun k => ‖a k‖^2), coeff_sq_tsum]
  simp only [he, tsum_mul_left, coeff_sq_tsum]
  rw [mul_pow]

/-- Absolute convergence and the precise 4/⟨n⟩ bound for the coefficient pairing. -/
theorem summable_and_linearWeightKernel_pairing_le {n : ℤ} {z : ℂ}
    (hz : z ∈ resonantStrip n) (a b : Coeff 2) :
    (Summable (fun p : ℤ × ℤ => linearWeightKernel n z p.2 p.1 *
      (‖a (p.2+p.1)‖*‖b p.1‖))) ∧
    (∑' p : ℤ × ℤ, linearWeightKernel n z p.2 p.1 * (‖a (p.2+p.1)‖*‖b p.1‖)) ≤
      (4/(1+|(n:ℝ)|))*‖a‖*‖b‖ := by
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two
    (fun p : ℤ × ℤ => linearWeightKernel_nonneg n z p.2 p.1)
    (fun p : ℤ × ℤ => mul_nonneg (norm_nonneg (a (p.2+p.1))) (norm_nonneg (b p.1)))
    (by simpa only [Real.rpow_two] using summable_linearWeightKernel_sq hz)
    (by simpa only [Real.rpow_two] using summable_convolution_coeff_product_sq a b)
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow,
    tsum_convolution_coeff_product_sq, Real.sqrt_sq (mul_nonneg (norm_nonneg a) (norm_nonneg b))]
  have hK : Real.sqrt (∑' p : ℤ × ℤ, linearWeightKernel n z p.2 p.1 ^ 2) ≤ 4/(1+|(n:ℝ)|) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · simpa only [div_pow, show (4:ℝ)^2=16 by norm_num] using tsum_linearWeightKernel_sq_le hz
  have hprod := mul_le_mul_of_nonneg_right hK (mul_nonneg (norm_nonneg a) (norm_nonneg b))
  simpa only [mul_assoc] using hprod

end NLS.ZakharovShabat
