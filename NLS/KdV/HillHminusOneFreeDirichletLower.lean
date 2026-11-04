import NLS.KdV.HillHminusOneFreeDirichlet
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! # The free normalized Dirichlet characteristic has no nonpositive zero -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

theorem hillHminusDirichlet_free_ne_zero_of_nonpos (x : ℝ) (hx : x ≤ 0) :
    hillHminusDirichlet 0 x ≠ 0 := by
  intro hz
  by_cases hx0 : x = 0
  · subst x
    simp only [Complex.ofReal_zero, hillHminusDirichlet_free_zero] at hz
    exact one_ne_zero hz
  have hneg : x < 0 := lt_of_le_of_ne hx hx0
  obtain ⟨z,hzsq⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) (by norm_num : 0 < 2)
  have hzn : z ≠ 0 := by
    intro h
    rw [h,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hzsq
    exact hx0 (Complex.ofReal_injective hzsq.symm)
  rw [← hzsq,hillHminusDirichlet_free_sq z hzn] at hz
  have hsin : Complex.sin z = 0 := by
    have he := (div_eq_iff hzn).mp hz
    simpa only [zero_mul] using he
  obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hsin
  have he := congrArg Complex.re hzsq
  rw [hk] at he
  have hxEq : ((k : ℝ)*Real.pi)^2 = x := by
    simpa only [pow_two,mul_re,mul_im,Complex.intCast_re,Complex.intCast_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_mul,sub_zero,add_zero] using he
  nlinarith [sq_nonneg ((k : ℝ)*Real.pi)]

end NLS.KdV
