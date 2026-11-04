import NLS.ComplexAnalysis.TwoRootQuotientDiscBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



theorem norm_two_root_factor_div_center_sq_sub_one_le
    (a b c z : ℂ) (R ρ : ℝ) (hR : 0 < R) (hρ : 0 ≤ ρ)
    (ha : ‖a-c‖ ≤ ρ*R) (hb : ‖b-c‖ ≤ ρ*R) (hz : ‖z-c‖=R) :
    ‖((z-a)*(z-b))/(z-c)^2-1‖ ≤ 2*ρ+ρ^2 := by
  have hzc : z-c ≠ 0 := norm_pos_iff.mp (hz.symm ▸ hR)
  have he : ((z-a)*(z-b))/(z-c)^2-1 =
      ((z-a)*(z-b)-(z-c)^2)/(z-c)^2 := by field_simp
  rw [he,norm_div,norm_pow,hz]
  calc
    _ ≤ (2*R*(ρ*R)+(ρ*R)^2)/R^2 := div_le_div_of_nonneg_right
      (norm_two_root_factor_sub_center_sq_le a b c z R (ρ*R) (by positivity) ha hb hz) (sq_nonneg R)
    _ = _ := by field_simp

end NLS.ComplexAnalysis
