import NLS.ComplexAnalysis.DenseSegmentComplement

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem dense_complex_nonreal : Dense {z : ℂ | z.im ≠ 0} := by
  intro z
  by_cases hz : z.im ≠ 0
  · exact subset_closure hz
  · have hz0 : z.im = 0 := not_ne_iff.mp hz
    let ray : ℝ → ℂ := fun y => z+(y : ℂ)*I
    have hray : Tendsto ray (𝓝[>] (0 : ℝ)) (𝓝 z) := by
      have hc : ContinuousAt ray 0 := by dsimp only [ray];fun_prop
      have h0 : ray 0 = z := by simp only [ray,ofReal_zero,zero_mul,add_zero]
      simpa only [h0] using hc.tendsto.mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto hray
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [ray,add_im,mul_im,ofReal_re,ofReal_im,I_im,I_re,mul_one,mul_zero,zero_add,add_zero,hz0]
    exact ne_of_gt hy

end NLS.ComplexAnalysis
