import Mathlib.Analysis.Complex.RemovableSingularity
import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive

/-! # Circle coefficients of an analytic function evaluated at inverse frequency

Two divided differences give an analytic quadratic remainder. Its primitive
composed with inversion has zero period, leaving exactly the linear Taylor
coefficient in the unweighted exterior integral.
-/
noncomputable section
open Set Complex Metric
namespace NLS.ComplexAnalysis

/-- The regularized divided difference of an analytic function is analytic
on the same disc about its base point. -/
theorem analyticOnNhd_dslope_zero (g : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (ball 0 r)) : AnalyticOnNhd ℂ (dslope g 0) (ball 0 r) :=
  ((differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hr))).mpr
    hg.differentiableOn).analyticOnNhd isOpen_ball

/-- The exact second-order divided-difference decomposition, valid even at zero. -/
theorem eq_second_dslope_expansion (g : ℂ → ℂ) (w : ℂ) :
    g w = g 0 + w * deriv g 0 + w^2 * dslope (dslope g 0) 0 w := by
  have h₁ := sub_smul_dslope g 0 w
  have h₂ := sub_smul_dslope (dslope g 0) 0 w
  simp only [sub_zero, smul_eq_mul, dslope_same] at h₁ h₂
  linear_combination -h₁ - w*h₂

/-- The exterior circle integral is exactly the first Taylor coefficient. -/
theorem circleIntegral_comp_inv_eq (g : ℂ → ℂ) (r R : ℝ) (hr : 0 < r)
    (hR : 0 < R) (hRr : R⁻¹ < r) (hg : AnalyticOnNhd ℂ g (ball 0 r)) :
    (∮ z in C(0,R), g z⁻¹) = (2*Real.pi*I : ℂ) * deriv g 0 := by
  let k := dslope (dslope g 0) 0
  have hk := analyticOnNhd_dslope_zero (dslope g 0) r hr (analyticOnNhd_dslope_zero g r hr hg)
  obtain ⟨H, hH⟩ := exists_primitive_on_convex k (ball 0 r) (convex_ball _ _) isOpen_ball hk.differentiableOn
  have hz0 (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : z ≠ 0 := by
    have hn : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
    exact norm_pos_iff.mp (hn.symm ▸ hR)
  have hzball (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : z⁻¹ ∈ ball (0 : ℂ) r := by
    have hn : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
    simpa only [mem_ball, dist_zero_right, norm_inv, hn] using hRr
  have hzero : (∮ z in C(0,R), g z⁻¹ - deriv g 0 * z⁻¹) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR.le
      (f := fun z => g 0 * z - H z⁻¹)
    intro z hz
    have hd := ((hasDerivAt_id z).const_mul (g 0)).sub
      ((hH z⁻¹ (hzball z hz)).comp z (hasDerivAt_inv (hz0 z hz)))
    have he := eq_second_dslope_expansion g z⁻¹
    have hd' : HasDerivAt (fun z => g 0*z - H z⁻¹)
        (g z⁻¹ - deriv g 0*z⁻¹) z := by
      convert! hd using 1
      dsimp only [k] at *
      rw [he]
      simp only [inv_pow]
      ring
    exact hd'.hasDerivWithinAt
  have hgi : CircleIntegrable (fun z => g z⁻¹) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact ((hg z⁻¹ (hzball z hz)).continuousAt.comp
      (continuousAt_inv₀ (hz0 z hz))).continuousWithinAt
  have hai : CircleIntegrable (fun z => deriv g 0*z⁻¹) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact (continuousAt_const.mul (continuousAt_inv₀ (hz0 z hz))).continuousWithinAt
  rw [circleIntegral.integral_sub hgi hai, circleIntegral.integral_const_mul] at hzero
  have hi : (∮ z in C(0,R), z⁻¹) = (2*Real.pi*I : ℂ) := by
    simpa only [sub_zero] using circleIntegral.integral_sub_center_inv (0 : ℂ) hR.ne'
  rw [hi] at hzero
  exact (sub_eq_zero.mp hzero).trans (mul_comm _ _)

/-- Weighting by the spectral parameter extracts the next Taylor coefficient. -/
theorem circleIntegral_mul_comp_inv_eq (g : ℂ → ℂ) (r R : ℝ) (hr : 0 < r)
    (hR : 0 < R) (hRr : R⁻¹ < r) (hg : AnalyticOnNhd ℂ g (ball 0 r)) :
    (∮ z in C(0,R), z * g z⁻¹) = (2*Real.pi*I : ℂ) * deriv (dslope g 0) 0 := by
  have hds := analyticOnNhd_dslope_zero g r hr hg
  have he (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) :
      z * g z⁻¹ = g 0 * z + dslope g 0 z⁻¹ := by
    have hn : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hn.symm ▸ hR)
    have h := sub_smul_dslope g 0 z⁻¹
    simp only [sub_zero, smul_eq_mul] at h
    calc
      _ = z * (g 0 + z⁻¹ * dslope g 0 z⁻¹) := by rw [h]; ring
      _ = _ := by field_simp
  have hci : CircleIntegrable (fun z => dslope g 0 z⁻¹) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hn : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hn.symm ▸ hR)
    have hzin : z⁻¹ ∈ ball (0 : ℂ) r := by
      simpa only [mem_ball, dist_zero_right, norm_inv, hn] using hRr
    exact ((hds z⁻¹ hzin).continuousAt.comp (continuousAt_inv₀ hz0)).continuousWithinAt
  calc
    _ = ∮ z in C(0,R), g 0*z + dslope g 0 z⁻¹ := circleIntegral.integral_congr hR.le he
    _ = (∮ z in C(0,R), g 0*z) + (∮ z in C(0,R), dslope g 0 z⁻¹) :=
      circleIntegral.integral_add ((continuous_const.mul continuous_id).continuousOn.circleIntegrable hR.le) hci
    _ = _ := by
      have hz : (∮ z in C(0,R), g 0*z) = 0 := by
        apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR.le
          (f := fun z => (g 0/2)*z^2)
        intro z _
        convert! ((hasDerivAt_id z).pow 2).const_mul (g 0/2) |>.hasDerivWithinAt using 1
        norm_num
        ring
      rw [hz, zero_add, circleIntegral_comp_inv_eq (dslope g 0) r R hr hR hRr hds]

end NLS.ComplexAnalysis
