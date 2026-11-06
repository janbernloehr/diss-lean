import NLS.KdV.FreeFrequencyPsi
import NLS.KdV.ClassicalContourCoverage
import NLS.ComplexAnalysis.RightHalfPlaneSquareRoot
import NLS.ZakharovShabat.FreeDerivativeZeroCounts

/-! # Exact free periods on all fixed positive frequency circles

The energy contour is the quadratic image of `C(k*pi,pi/4)`. Its exact
Jacobian `2z` yields the source normalization `2*pi*delta_nk` for every
positive output and contour index, with no contour hypothesis supplied.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem freeFrequencyCircle_sin_ne_zero (k : ℕ+) (z : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) : sin z ≠ 0 := by
  intro hs
  have hc := free_derivative_zero_eq_center (by linarith [Real.pi_pos] : Real.pi/4 < Real.pi)
    (k : ℤ) (by simpa only [Int.cast_natCast] using sphere_subset_closedBall hz)
    (by rw [hs,mul_zero])
  have hne : z ≠ (Real.pi : ℂ)*(k : ℕ) :=
    sphere_disjoint_ball.ne_of_mem hz (mem_ball_self (by positivity : 0 < Real.pi/4))
  exact hne (by simpa only [Int.cast_natCast] using hc)

theorem classicalHillFreeRoot_sq_on_frequency_circle (k : ℕ+) (z : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    classicalHillFreeRoot (z^2) = -2*I*sin z := by
  rw [classicalHillFreeRoot_eq_sin, sqrt_sq_of_re_pos z
    (re_pos_of_high_closedBall _ k.property z (sphere_subset_closedBall hz))]

theorem classicalHillFreeRoot_ne_zero_on_frequency_circle (k : ℕ+) (z : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    classicalHillFreeRoot (z^2) ≠ 0 := by
  rw [classicalHillFreeRoot_sq_on_frequency_circle k z hz]
  exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (freeFrequencyCircle_sin_ne_zero k z hz)

/-- The entire free differential pulls back to two simple rational poles;
the negative pole is outside every selected positive contour. -/
theorem classicalHillFreePsi_frequency_pullback (n k : ℕ+) (z : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    (classicalHillFreePsi n (z^2)/classicalHillFreeRoot (z^2))*(2*z) =
      -I*(z-(n : ℂ)*Real.pi)⁻¹+I*(z+(n : ℂ)*Real.pi)⁻¹ := by
  have hzr := re_pos_of_high_closedBall _ k.property z (sphere_subset_closedBall hz)
  have hz0 : z ≠ 0 := by intro h; simp only [h,zero_re,lt_self_iff_false] at hzr
  have hzne : z^2 ≠ freeHillEnergy n := by
    intro he
    have hs : (Complex.sqrt (z^2)) = (n : ℂ)*Real.pi := by rw [he,sqrt_freeHillEnergy]
    rw [sqrt_sq_of_re_pos z hzr] at hs
    have hsin : sin z = 0 := by rw [hs]; exact Complex.sin_nat_mul_pi (n : ℕ)
    exact freeFrequencyCircle_sin_ne_zero k z hz hsin
  have hroot := classicalHillFreeRoot_ne_zero_on_frequency_circle k z hz
  rw [classicalHillFreePsi_div_root n (z^2)
    (sq_mem_slitPlane_of_high_circle _ k.property z hz) hzne hroot,
    sqrt_sq_of_re_pos z hzr]
  have he : freeHillEnergy n = ((n : ℂ)*Real.pi)^2 := by
    dsimp only [freeHillEnergy]
    push_cast
    rfl
  have hfactor : z^2-freeHillEnergy n = (z-(n : ℂ)*Real.pi)*(z+(n : ℂ)*Real.pi) := by rw [he]; ring
  have hprod : (z-(n : ℂ)*Real.pi)*(z+(n : ℂ)*Real.pi) ≠ 0 := by
    rw [← hfactor]
    exact sub_ne_zero.mpr hzne
  rw [hfactor]
  field_simp [hz0,hprod,mul_ne_zero_iff.mp hprod |>.1,mul_ne_zero_iff.mp hprod |>.2]
  ring

private theorem positive_frequency_pole_outside (n k : ℕ+) (hnk : n ≠ k) :
    (n : ℂ)*Real.pi ∉ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
  intro h
  have he := free_derivative_zero_eq_center (by linarith [Real.pi_pos] : Real.pi/4 < Real.pi)
    (k : ℤ) (by simpa only [Int.cast_natCast] using h)
    (by rw [Complex.sin_nat_mul_pi,mul_zero])
  have hnreal : (n : ℝ)*Real.pi = Real.pi*(k : ℕ) := by simpa using congrArg re he
  have hnkreal : (n : ℝ) = k := mul_right_cancel₀ Real.pi_ne_zero (by nlinarith [hnreal])
  exact hnk (by exact_mod_cast hnkreal)

private theorem negative_frequency_pole_outside (n k : ℕ+) :
    -((n : ℂ)*Real.pi) ∉ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
  intro h
  have hp := re_pos_of_high_closedBall _ k.property _ h
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  simp only [neg_re,mul_re,natCast_re,ofReal_re,natCast_im,ofReal_im,mul_zero,sub_zero] at hp
  nlinarith [Real.pi_pos]

private theorem circleIntegral_inv_eq_zero_of_outside (c w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hw : w ∉ closedBall c R) : (∮ z in C(c,R), (z-w)⁻¹) = 0 := by
  have ha : AnalyticOnNhd ℂ (fun z : ℂ => (z-w)⁻¹) (closedBall c R) := by
    apply (analyticOnNhd_id.sub analyticOnNhd_const).inv
    intro z hz
    apply sub_ne_zero.mpr
    change z ≠ w
    intro h
    exact hw (h ▸ hz)
  exact circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
    ha.continuousOn (fun z hz => (ha z (ball_subset_closedBall hz.1)).differentiableAt)

/-- Exact normalization of every free energy differential on the entire
fixed frequency-contour family, with the positive orientation unchanged. -/
theorem circleIntegral_classicalHillFreePsi_frequency (n k : ℕ+) :
    (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      (classicalHillFreePsi n (z^2)/classicalHillFreeRoot (z^2))*(2*z)) =
        if n = k then (2*Real.pi : ℂ) else 0 := by
  have hR : 0 < Real.pi/4 := by positivity
  have hneg := negative_frequency_pole_outside n k
  have hiPos : CircleIntegrable (fun z : ℂ => (z-(n : ℂ)*Real.pi)⁻¹)
      ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hne : z ≠ (n : ℂ)*Real.pi := by
      intro he
      exact freeFrequencyCircle_sin_ne_zero k z hz (by rw [he]; exact Complex.sin_nat_mul_pi (n : ℕ))
    exact ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hne)).continuousWithinAt
  have hiNeg : CircleIntegrable (fun z : ℂ => (z+(n : ℂ)*Real.pi)⁻¹)
      ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hne : z+(n : ℂ)*Real.pi ≠ 0 := by
      intro he
      exact hneg ((eq_neg_of_add_eq_zero_left he) ▸ sphere_subset_closedBall hz)
    exact ((continuousAt_id.add continuousAt_const).inv₀ hne).continuousWithinAt
  have hi1 : CircleIntegrable (fun z : ℂ => -I*(z-(n : ℂ)*Real.pi)⁻¹)
      ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
    simpa only [Pi.smul_apply,smul_eq_mul] using! hiPos.const_smul (a := -I)
  have hi2 : CircleIntegrable (fun z : ℂ => I*(z+(n : ℂ)*Real.pi)⁻¹)
      ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
    simpa only [Pi.smul_apply,smul_eq_mul] using! hiNeg.const_smul (a := I)
  rw [circleIntegral.integral_congr hR.le (fun z hz => classicalHillFreePsi_frequency_pullback n k z hz),
    circleIntegral.integral_add hi1 hi2,circleIntegral.integral_const_mul,circleIntegral.integral_const_mul]
  have hnegInt : (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      (z+(n : ℂ)*Real.pi)⁻¹) = 0 := by
    simpa only [sub_neg_eq_add] using circleIntegral_inv_eq_zero_of_outside _ _ _ hR.le hneg
  rw [hnegInt,mul_zero,add_zero]
  by_cases hnk : n = k
  · subst n
    have hcenter : ((k : ℂ)*Real.pi) ∈ ball ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
      simpa only [mul_comm] using mem_ball_self (x := (Real.pi : ℂ)*(k : ℕ)) hR
    rw [circleIntegral.integral_sub_inv_of_mem_ball hcenter,if_pos rfl]
    ring_nf
    simp only [I_sq]
    ring
  · rw [circleIntegral_inv_eq_zero_of_outside _ _ _ hR.le (positive_frequency_pole_outside n k hnk),
      mul_zero,if_neg hnk]

end NLS.KdV
