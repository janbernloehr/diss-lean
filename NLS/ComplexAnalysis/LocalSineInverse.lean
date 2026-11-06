import NLS.ComplexAnalysis.LocalSinhLinearization

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.ComplexAnalysis



/-- An explicit local sine inverse bound on the complex half-unit disc. -/
theorem norm_le_two_mul_norm_sin_of_half (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    ‖z‖ ≤ 2*‖Complex.sin z‖ := by
  have hrem := norm_sinh_sub_self_le_sq (z*I) (by
    simpa only [norm_mul,norm_I,mul_one] using (hz.trans (by norm_num : (1/2 : ℝ) ≤ 1)))
  rw [Complex.sinh_mul_I,← sub_mul,norm_mul,norm_I,mul_one,norm_mul,norm_I,mul_one] at hrem
  have h := norm_le_norm_sub_add z (Complex.sin z)
  rw [norm_sub_rev] at h
  nlinarith [norm_nonneg z]

end NLS.ComplexAnalysis
