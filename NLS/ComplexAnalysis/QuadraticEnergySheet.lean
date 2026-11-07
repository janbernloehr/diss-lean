import NLS.ComplexAnalysis.PrincipalSquareRootSheet
import NLS.ComplexAnalysis.DenseSegmentComplement

/-! The right frequency half-plane fixes the actual principal quadratic
energy sheet. Nonreal energies are dense, so continuous sheet identities
there determine their real-band extensions. -/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem sq_mem_slitPlane_of_re_pos (z : ℂ) (hz : 0 < z.re) : z^2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hi : z.im = 0
  · left
    simp only [pow_two,mul_re,hi,mul_zero,sub_zero]
    positivity
  · right
    simp only [pow_two,mul_im]
    have hp := mul_ne_zero hz.ne' hi
    intro he
    apply hp
    linear_combination he/2

theorem sqrt_sq_of_re_pos (z : ℂ) (hz : 0 < z.re) : Complex.sqrt (z^2) = z :=
  (eq_principalSqrt_of_sq_of_re_pos z (z^2) rfl hz).symm

theorem quadraticEnergyMap_injOn_right (c : ℂ) :
    InjOn (fun z : ℂ => z^2-c) {z : ℂ | 0 < z.re} := by
  intro z hz w hw he
  change 0 < z.re at hz
  change 0 < w.re at hw
  have hs : z^2 = w^2 := by
    have h := congrArg (fun v : ℂ => v+c) he
    simpa only [sub_add_cancel] using h
  rcases eq_or_eq_neg_of_sq_eq_sq z w hs with h | h
  · exact h
  · have hr := congrArg Complex.re h
    simp only [neg_re] at hr
    linarith

theorem dense_complex_nonreal : Dense {z : ℂ | z.im ≠ 0} := by
  intro z
  by_cases hz : z.im = 0
  · let ray : ℝ → ℂ := fun y => z+(y:ℂ)*I
    have ht : Tendsto ray (𝓝[>] (0:ℝ)) (𝓝 z) := by
      have hc : ContinuousAt ray 0 := by dsimp only [ray]; fun_prop
      simpa only [ray,ofReal_zero,zero_mul,add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with y hy
    change (z+(y:ℂ)*I).im ≠ 0
    simpa only [add_im,mul_im,ofReal_re,ofReal_im,I_im,I_re,mul_one,mul_zero,
      add_zero,hz,zero_add] using ne_of_gt hy
  · exact subset_closure hz

end NLS.ComplexAnalysis
