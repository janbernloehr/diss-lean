import NLS.ComplexAnalysis.ShiftedSquareRootBounds

/-! # Fixed energy shifts preserve separated square roots on the exterior

Either root sign is allowed, which also covers the negative real axis.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.ComplexAnalysis

theorem close_to_one_square_root (w z c : ℂ) (hsq : w^2=z^2+c)
    (δ : ℝ) (hz : 0 < ‖z‖) (hsmall : ‖c‖ ≤ δ*‖z‖) :
    ‖w-z‖ ≤ δ ∨ ‖w+z‖ ≤ δ := by
  have hprod : ‖w-z‖*‖w+z‖ = ‖c‖ := by
    rw [← norm_mul,show (w-z)*(w+z)=c by linear_combination hsq]
  have hsum : 2*‖z‖ ≤ ‖w-z‖+‖w+z‖ := by
    have ht := norm_sub_le (w+z) (w-z)
    rw [show (w+z)-(w-z)=2*z by ring,norm_mul] at ht
    norm_num at ht
    linarith
  by_cases h : ‖z‖ ≤ ‖w+z‖
  · left
    have hh := mul_le_mul_of_nonneg_left h (norm_nonneg (w-z))
    nlinarith
  · right
    have hh := mul_le_mul_of_nonneg_right
      (show ‖z‖ ≤ ‖w-z‖ by linarith) (norm_nonneg (w+z))
    nlinarith

theorem shifted_square_root_separation (w z c : ℂ) (hsq : w^2=z^2+c)
    (r δ : ℝ) (hz : 0 < ‖z‖) (hsmall : ‖c‖ ≤ δ*‖z‖)
    (hsep : ∀ m : ℤ, r+δ ≤ ‖z-(Real.pi : ℂ)*m‖) :
    ‖z‖-δ ≤ ‖w‖ ∧ ∀ m : ℤ, r ≤ ‖w-(Real.pi : ℂ)*m‖ := by
  rcases close_to_one_square_root w z c hsq δ hz hsmall with h | h
  · constructor
    · have ht := norm_sub_norm_le z w
      rw [norm_sub_rev] at ht
      linarith
    · intro m
      have ht := norm_sub_le_norm_sub_add_norm_sub z w ((Real.pi : ℂ)*m)
      rw [norm_sub_rev z w] at ht
      linarith [hsep m]
  · have he : ‖w-(-z)‖ ≤ δ := by simpa only [sub_neg_eq_add] using h
    constructor
    · have ht := norm_sub_norm_le (-z) w
      rw [norm_neg,norm_sub_rev] at ht
      linarith
    · intro m
      have hzm : r+δ ≤ ‖(-z)-(Real.pi : ℂ)*m‖ := by
        simpa only [Int.cast_neg,mul_neg,sub_neg_eq_add,neg_sub_left,norm_neg,add_comm] using hsep (-m)
      have ht := norm_sub_le_norm_sub_add_norm_sub (-z) w ((Real.pi : ℂ)*m)
      rw [norm_sub_rev (-z) w] at ht
      linarith
end NLS.ComplexAnalysis
