import NLS.ComplexAnalysis.EntireEvenSquareDescent
import Mathlib.Tactic

/-! # Bounds for symmetric root data inside a common disc -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

theorem norm_two_root_midpoint_sub_le (a b c : ℂ) {r : ℝ}
    (ha : ‖a-c‖ ≤ r) (hb : ‖b-c‖ ≤ r) : ‖(a+b)/2-c‖ ≤ r := by
  rw [show (a+b)/2-c=((a-c)+(b-c))/2 by ring,norm_div,norm_ofNat]
  have h := norm_add_le (a-c) (b-c)
  linarith

theorem norm_two_root_halfGap_sqrt_le (a b c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (ha : ‖a-c‖ ≤ r) (hb : ‖b-c‖ ≤ r) : ‖sqrt ((b-a)^2/4)‖ ≤ r := by
  have hd : ‖b-a‖ ≤ 2*r := by
    have h := norm_sub_le_norm_sub_add_norm_sub b c a
    rw [norm_sub_rev c a] at h
    linarith
  have he := congrArg norm (complex_sqrt_sq ((b-a)^2/4))
  rw [norm_pow,norm_div,norm_pow,norm_ofNat] at he
  have hs := (sq_le_sq₀ (norm_nonneg (b-a)) (by positivity : 0 ≤ 2*r)).mpr hd
  nlinarith [norm_nonneg (sqrt ((b-a)^2/4))]

end NLS.ComplexAnalysis
