import NLS.ZakharovShabat.ResonantCauchyGap

/-! # A real double resonant root satisfies the closing equations

Small spectral derivatives and equal off-diagonal norms force both
coefficients to vanish at a double determinant zero. Reality supplies
the equal norms when this criterion is applied to the actual operator.
-/

noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- The off-diagonal strip bound gives a quarter bound on its derivative. -/
theorem norm_deriv_offDiagonal_le_on_refined_disk (n : ℤ) (b : ℂ → ℂ)
    (hb : AnalyticOnNhd ℂ b (resonantStrip n))
    (hbound : ∀ z ∈ resonantStrip n, ‖b z‖ ≤ Real.pi/16)
    (x : ℂ) (hx : x ∈ refinedResonantDisk n) : ‖deriv b x‖ ≤ 1/4 := by
  have hball := closedBall_refined_point_subset_strip n x hx
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < Real.pi/4)
    (hb.differentiableOn.diffContOnCl_ball hball)
    (fun z hz => hbound z (hball (Metric.sphere_subset_closedBall hz)))
  have he : (Real.pi/16)/(Real.pi/4) = (1/4 : ℝ) := by field_simp; ring
  exact h.trans_eq he

/-- The double-zero criterion uses norm equality, so no differentiation
of complex conjugation is required. -/
theorem resonant_double_zero_closing (c z : ℂ) (a b d : ℂ → ℂ)
    (ha : DifferentiableAt ℂ a z) (hb : DifferentiableAt ℂ b z) (hd : DifferentiableAt ℂ d z)
    (ha' : ‖deriv a z‖ ≤ 1/8) (hb' : ‖deriv b z‖ ≤ 1/4) (hd' : ‖deriv d z‖ ≤ 1/4)
    (hnorm : ‖b z‖ = ‖d z‖)
    (hzero : (z-c-a z)^2-b z*d z = 0)
    (hderiv : deriv (fun x => (x-c-a x)^2-b x*d x) z = 0) :
    z = c+a z ∧ b z = 0 ∧ d z = 0 := by
  have hsq : ‖z-c-a z‖^2 = ‖b z‖^2 := by
    rw [← norm_pow, sub_eq_zero.mp hzero, norm_mul, ← hnorm, pow_two]
  have hnormr : ‖z-c-a z‖ = ‖b z‖ := by nlinarith [norm_nonneg (z-c-a z), norm_nonneg (b z)]
  have hdiff := ((((hasDerivAt_id z).sub_const c).sub ha.hasDerivAt).pow 2).sub
    (hb.hasDerivAt.mul hd.hasDerivAt)
  have he : 2*(z-c-a z)*(1-deriv a z) = deriv b z*d z+b z*deriv d z := by
    have h := hdiff.deriv
    change deriv (fun x => (x-c-a x)^2-b x*d x) z = _ at h
    rw [hderiv] at h
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.sub_apply, id_eq] using (sub_eq_zero.mp h.symm)
  have hlo : 1-‖deriv a z‖ ≤ ‖1-deriv a z‖ := by
    simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) (deriv a z)
  have hbound : 2*‖b z‖*(1-‖deriv a z‖) ≤ ‖deriv b z‖*‖b z‖+‖b z‖*‖deriv d z‖ := by
    calc
      _ ≤ 2*‖b z‖*‖1-deriv a z‖ := mul_le_mul_of_nonneg_left hlo (by positivity)
      _ = ‖2*(z-c-a z)*(1-deriv a z)‖ := by rw [norm_mul,norm_mul,hnormr]; norm_num
      _ = ‖deriv b z*d z+b z*deriv d z‖ := congrArg norm he
      _ ≤ _ := by simpa only [norm_mul, ← hnorm] using norm_add_le (deriv b z*d z) (b z*deriv d z)
  have hb0 : ‖b z‖ = 0 := by
    nlinarith [norm_nonneg (b z), mul_le_mul_of_nonneg_right ha' (norm_nonneg (b z)),
      mul_le_mul_of_nonneg_right hb' (norm_nonneg (b z)),
      mul_le_mul_of_nonneg_left hd' (norm_nonneg (b z))]
  have hr : z-c-a z = 0 := norm_eq_zero.mp (hnormr.trans hb0)
  exact ⟨by linear_combination hr, norm_eq_zero.mp hb0, norm_eq_zero.mp (hnorm.symm.trans hb0)⟩

/-- Uniform strip bounds instantiate all small-derivative premises. -/
theorem resonant_double_zero_closing_on_refined_disk (n : ℤ) (a b d : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : AnalyticOnNhd ℂ b (resonantStrip n))
    (hd : AnalyticOnNhd ℂ d (resonantStrip n))
    (hbound : ∀ z ∈ resonantStrip n,
      ‖a z‖ ≤ Real.pi/32 ∧ ‖b z‖ ≤ Real.pi/16 ∧ ‖d z‖ ≤ Real.pi/16)
    (z : ℂ) (hz : z ∈ refinedResonantDisk n)
    (hnorm : ‖b z‖ = ‖d z‖)
    (hzero : (z-(Real.pi : ℂ)*n-a z)^2-b z*d z = 0)
    (hderiv : deriv (fun x => (x-(Real.pi : ℂ)*n-a x)^2-b x*d x) z = 0) :
    z = (Real.pi : ℂ)*n+a z ∧ b z = 0 ∧ d z = 0 :=
  resonant_double_zero_closing _ z a b d
    (ha z (refinedResonantDisk_subset_strip n hz)).differentiableAt
    (hb z (refinedResonantDisk_subset_strip n hz)).differentiableAt
    (hd z (refinedResonantDisk_subset_strip n hz)).differentiableAt
    (norm_deriv_le_on_refined_disk n a ha (fun z hz => (hbound z hz).1) z hz)
    (norm_deriv_offDiagonal_le_on_refined_disk n b hb (fun z hz => (hbound z hz).2.1) z hz)
    (norm_deriv_offDiagonal_le_on_refined_disk n d hd (fun z hz => (hbound z hz).2.2) z hz)
    hnorm hzero hderiv

end NLS.ZakharovShabat
