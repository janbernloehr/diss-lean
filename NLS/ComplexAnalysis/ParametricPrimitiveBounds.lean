import NLS.ComplexAnalysis.ParametricConvexPrimitive

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



/-- A bounded spectral numerator gives the exact segment-length bound
for its normalized affine primitive. -/
theorem norm_parametricConvexPrimitive_le
    {A : Type} (F : ℂ × A → ℂ) (c z : ℂ) (a : A) (Ω : Set ℂ) (B : ℝ)
    (hconv : Convex ℝ Ω) (hc : c∈Ω) (hz : z∈Ω)
    (hF : ∀ w∈Ω, ‖F (w,a)‖≤B) :
    ‖parametricConvexPrimitive F c (z,a)‖≤‖z-c‖*B := by
  unfold parametricConvexPrimitive
  have hb (t : ℝ) (ht : t∈Set.uIoc (0 : ℝ) 1) :
      ‖(z-c)*F (c+(t : ℂ)*(z-c),a)‖≤‖z-c‖*B := by
    have ht' : t∈Icc (0 : ℝ) 1 := by
      have hh : t∈Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
      exact ⟨hh.1.le,hh.2⟩
    have hw : c+(t : ℂ)*(z-c)∈Ω := by
      have hh := hconv.lineMap_mem hc hz ht'
      simpa only [AffineMap.lineMap_apply_module',Complex.real_smul,add_comm] using hh
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hF _ hw) (norm_nonneg _)
  simpa only [sub_zero,abs_one,mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb

end NLS.ComplexAnalysis
