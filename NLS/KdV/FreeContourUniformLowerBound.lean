import NLS.KdV.FreeHighContourPeriods

/-! # Uniform nonvanishing of the free root on every positive contour

Translation by the free lattice preserves the sine norm. A positive
minimum on one compact circle therefore works for the entire family.
-/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
namespace NLS.KdV

theorem norm_sin_sub_free_center (k : ℕ) (z : ℂ) :
    ‖sin (z-(Real.pi : ℂ)*k)‖ = ‖sin z‖ := by
  have hs : sin ((Real.pi : ℂ)*k) = 0 := by
    rw [mul_comm]
    exact Complex.sin_nat_mul_pi k
  have hc : ‖cos ((Real.pi : ℂ)*k)‖ = 1 := by
    have he := sin_sq_add_cos_sq ((Real.pi : ℂ)*k)
    rw [hs,zero_pow (by decide : 2 ≠ 0),zero_add] at he
    have hn := congrArg norm he
    rw [norm_pow,norm_one] at hn
    nlinarith [norm_nonneg (cos ((Real.pi : ℂ)*k))]
  have he : sin z = sin (z-(Real.pi : ℂ)*k)*cos ((Real.pi : ℂ)*k) := by
    conv_lhs => rw [← sub_add_cancel z ((Real.pi : ℂ)*k),sin_add]
    rw [hs,mul_zero,add_zero]
  rw [he,norm_mul,hc,mul_one]

theorem exists_uniform_freeContour_sin_lower_bound :
    ∃ b : ℝ, 0 < b ∧ ∀ k : ℕ+, ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      b ≤ ‖sin z‖ := by
  have hR : 0 < Real.pi/4 := by positivity
  have hne : (sphere (0 : ℂ) (Real.pi/4)).Nonempty := by
    refine ⟨((Real.pi/4 : ℝ) : ℂ),?_⟩
    simp only [mem_sphere,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
  obtain ⟨w,hw,hmin⟩ := (isCompact_sphere (0 : ℂ) (Real.pi/4)).exists_isMinOn hne
    Complex.continuous_sin.norm.continuousOn
  have hsw : sin w ≠ 0 := by
    intro hs
    have he := free_derivative_zero_eq_center (by linarith [Real.pi_pos] : Real.pi/4 < Real.pi)
      0 (by simpa only [Int.cast_zero,mul_zero] using sphere_subset_closedBall hw)
      (by rw [hs,mul_zero])
    have hn := mem_sphere_iff_norm.mp hw
    simp only [Int.cast_zero,mul_zero] at he
    rw [he,sub_zero,norm_zero] at hn
    linarith
  refine ⟨‖sin w‖,norm_pos_iff.mpr hsw,?_⟩
  intro k z hz
  rw [← norm_sin_sub_free_center (k : ℕ) z]
  apply hmin
  simpa only [mem_sphere,dist_zero_right] using mem_sphere_iff_norm.mp hz

theorem exists_uniform_freeContour_radicand_lower_bound :
    ∃ b : ℝ, 0 < b ∧ ∀ k : ℕ+, ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      b ≤ ‖classicalHillRadicand (z^2,0)‖ := by
  obtain ⟨b,hb,hbound⟩ := exists_uniform_freeContour_sin_lower_bound
  refine ⟨4*b^2,by positivity,?_⟩
  intro k z hz
  rw [← classicalHillFreeRoot_sq,norm_pow,classicalHillFreeRoot_sq_on_frequency_circle k z hz,
    norm_mul,norm_mul,norm_I,mul_one]
  norm_num only [norm_neg,norm_ofNat]
  have h := hbound k z hz
  nlinarith [sq_nonneg (‖sin z‖-b)]

end NLS.KdV
