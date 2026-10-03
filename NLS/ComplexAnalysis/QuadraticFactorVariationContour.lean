import NLS.ComplexAnalysis.SimplePoleCauchyInterpolation

/-! # Contour recovery of a quadratic factor's midpoint variation

Both enclosed poles contribute equally to the midpoint variation. The
squared-gap variation has zero contour integral, including when the two
roots coincide. An analytic nonvanishing factor contributes no integral.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

/-- The two-pole integral is zero also when the enclosed poles coincide. -/
theorem circleIntegral_two_enclosed_poles_including_double
    (c a b : ℂ) (r : ℝ) (hr : 0 < r) (ha : a ∈ ball c r) (hb : b ∈ ball c r) :
    (∮ z in C(c,r), 1/(z-a)/(z-b)) = 0 := by
  by_cases hab : a = b
  · subst b
    convert circleIntegral.integral_sub_zpow_of_ne (by decide : (-2 : ℤ) ≠ -1) c a r using 1
    congr 1
    funext z
    simp [zpow_neg,div_eq_mul_inv,pow_two]
  · exact circleIntegral_two_enclosed_poles hr ha hb hab

/-- The rational part of a quadratic-factor variation has exactly the midpoint residue. -/
theorem circleIntegral_quadratic_factor_variation
    (c a b u v : ℂ) (r : ℝ) (hr : 0 < r) (ha : a ∈ ball c r) (hb : b ∈ ball c r) :
    (∮ z in C(c,r), (-2*(z-(a+b)/2)*u-v/4)/((z-(a+b)/2)^2-(b-a)^2/4)) =
      -(4*Real.pi*I)*u := by
  have hne (w : ℂ) (hw : w ∈ ball c r) (z : ℂ) (hz : z ∈ sphere c r) : z-w ≠ 0 :=
    sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz hw)
  have hi (w : ℂ) (hw : w ∈ ball c r) : CircleIntegrable (fun z => (z-w)⁻¹) c r := by
    exact ((continuousOn_id.sub continuousOn_const).inv₀ (hne w hw)).circleIntegrable hr.le
  have hiab : CircleIntegrable (fun z => 1/(z-a)/(z-b)) c r := by
    exact ((continuousOn_const.div (continuousOn_id.sub continuousOn_const) (hne a ha)).div
      (continuousOn_id.sub continuousOn_const) (hne b hb)).circleIntegrable hr.le
  have his : CircleIntegrable (fun z => -u*((z-a)⁻¹+(z-b)⁻¹)) c r :=
    ((hi a ha).add (hi b hb)).const_mul (-u)
  have hiv : CircleIntegrable (fun z => (v/4)*(1/(z-a)/(z-b))) c r := hiab.const_mul (v/4)
  calc
    _ = ∮ z in C(c,r), -u*((z-a)⁻¹+(z-b)⁻¹)-(v/4)*(1/(z-a)/(z-b)) := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      have hq : (z-(a+b)/2)^2-(b-a)^2/4 = (z-a)*(z-b) := by ring
      dsimp only
      rw [hq]
      field_simp [hne a ha z hz,hne b hb z hz]
      ring
    _ = -(4*Real.pi*I)*u := by
      rw [circleIntegral.integral_sub his hiv,circleIntegral.integral_const_mul,circleIntegral.integral_const_mul,
        circleIntegral.integral_add (hi a ha) (hi b hb),
        circleIntegral.integral_sub_inv_of_mem_ball ha,circleIntegral.integral_sub_inv_of_mem_ball hb,
        circleIntegral_two_enclosed_poles_including_double c a b r hr ha hb]
      ring

/-- A nonvanishing analytic factor leaves the normalized midpoint contour formula unchanged.
The two identities are the quadratic factorization and its linearized form. -/
theorem midpoint_variation_eq_discriminant_contour
    (Δ D P A : ℂ → ℂ) (c a b u v : ℂ) (r : ℝ) (hr : 0 < r)
    (ha : a ∈ ball c r) (hb : b ∈ ball c r)
    (hP : AnalyticOnNhd ℂ P (closedBall c r)) (hA : AnalyticOnNhd ℂ A (closedBall c r))
    (hPne : ∀ z ∈ closedBall c r, P z ≠ 0)
    (hsq : ∀ z ∈ sphere c r, (Δ z)^2-4 = -4*((z-(a+b)/2)^2-(b-a)^2/4)*P z)
    (hvar : ∀ z ∈ sphere c r,
      2*Δ z*D z = -4*((-2*(z-(a+b)/2)*u-v/4)*P z+
        ((z-(a+b)/2)^2-(b-a)^2/4)*A z)) :
    u = -(2*Real.pi*I : ℂ)⁻¹ * (∮ z in C(c,r), Δ z*D z/((Δ z)^2-4)) := by
  let q := fun z : ℂ => (z-(a+b)/2)^2-(b-a)^2/4
  let dq := fun z : ℂ => -2*(z-(a+b)/2)*u-v/4
  have hq (z : ℂ) (hz : z ∈ sphere c r) : q z ≠ 0 := by
    have he : q z = (z-a)*(z-b) := by dsimp [q]; ring
    rw [he]
    exact mul_ne_zero (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz ha))
      (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz hb))
  have hiq : CircleIntegrable (fun z => dq z/q z) c r := by
    apply ContinuousOn.circleIntegrable hr.le
    apply ContinuousOn.div _ _ hq <;> dsimp [q,dq] <;> fun_prop
  have hAP : AnalyticOnNhd ℂ (fun z => A z/P z) (closedBall c r) := hA.div hP hPne
  have hiAP : CircleIntegrable (fun z => A z/P z) c r :=
    (hAP.continuousOn.mono sphere_subset_closedBall).circleIntegrable hr.le
  have hpoint (z : ℂ) (hz : z ∈ sphere c r) :
      Δ z*D z/((Δ z)^2-4) = (1/2 : ℂ)*(dq z/q z+A z/P z) := by
    rw [hsq z hz]
    have hv := hvar z hz
    change 2*Δ z*D z = -4*(dq z*P z+q z*A z) at hv
    change Δ z*D z/(-4*q z*P z) = _
    field_simp [hq z hz,hPne z (sphere_subset_closedBall hz)]
    dsimp [q,dq] at hv
    linear_combination -hv
  have hzero : (∮ z in C(c,r), A z/P z) = 0 := by
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty hAP.continuousOn
    intro z hz
    exact (hAP z (ball_subset_closedBall hz.1)).differentiableAt
  have hint : (∮ z in C(c,r), Δ z*D z/((Δ z)^2-4)) = -(2*Real.pi*I)*u := by
    rw [circleIntegral.integral_congr hr.le hpoint,circleIntegral.integral_const_mul,
      circleIntegral.integral_add hiq hiAP,hzero]
    have hrat := circleIntegral_quadratic_factor_variation c a b u v r hr ha hb
    change (∮ z in C(c,r), dq z/q z) = _ at hrat
    rw [hrat]
    ring
  rw [hint]
  have hπ : (2*Real.pi*I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  field_simp

end NLS.ComplexAnalysis
