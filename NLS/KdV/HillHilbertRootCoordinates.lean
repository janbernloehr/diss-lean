import NLS.KdV.HillComplexNumeratorZeros

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



def hillAbelianHilbertRootEnergy (a : Coeff 2) (m : ℕ) : ℂ :=
  (freeHillValue m : ℂ)+(m : ℂ)*a (m : ℤ)

theorem norm_hillAbelianHilbertRootEnergy_sub_free_le (a : Coeff 2) (m : ℕ) :
    ‖hillAbelianHilbertRootEnergy a m-(freeHillValue m : ℂ)‖ ≤ (m : ℝ)*‖a‖ := by
  rw [hillAbelianHilbertRootEnergy,add_sub_cancel_left,norm_mul,Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num) a (m : ℤ))
    (Nat.cast_nonneg m)

theorem hillAbelianHilbertRootEnergy_im_eq_zero (a : Coeff 2) (ha : star a = a) (m : ℕ) :
    (hillAbelianHilbertRootEnergy a m).im = 0 := by
  have hc : conj (a (m : ℤ)) = a (m : ℤ) := by
    simpa only [lp.star_apply,Complex.star_def] using congrArg (fun b : Coeff 2 => b (m : ℤ)) ha
  have hi : (a (m : ℤ)).im = 0 := by
    have h := congrArg Complex.im hc
    simp only [Complex.conj_im] at h
    linarith
  simp only [hillAbelianHilbertRootEnergy,Complex.add_im,Complex.ofReal_im,
    Complex.mul_im,Complex.natCast_re,Complex.natCast_im,hi,mul_zero,zero_mul,add_zero]

end NLS.KdV
