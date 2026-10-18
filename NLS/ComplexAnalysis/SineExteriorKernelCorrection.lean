import NLS.ComplexAnalysis.SineCorrectedCubicIntegral

/-! # Positive correction moments for exterior cosine kernels

Pairing reflected cosine kernels gives a nonnegative remainder. Integration
proves the required linear moment inequality on both sides of a gap, and
finite positive mixtures satisfy the sharp cubic profile ratio.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ComplexAnalysis

/-- Pairing reflected cosine kernels gives an elementary nonnegative remainder. -/
theorem sine_correction_kernel_pair (s : ℝ) (hs : 1 < s) (x : ℝ) :
    (2*s/(2*s^2-1))*(1-2*(Real.cos x)^2) ≤
      (2*(Real.sin x)^4-(Real.sin x)^2)/(s-Real.cos x)+
      (2*(Real.sin x)^4-(Real.sin x)^2)/(s+Real.cos x) := by
  have hs0 : 0 < s := lt_trans (by norm_num) hs
  have hsm : 0 < s-Real.cos x := by linarith [Real.cos_le_one x]
  have hsp : 0 < s+Real.cos x := by linarith [Real.neg_one_le_cos x]
  have hsq : 1 < s^2 := by nlinarith
  have hd : 0 < 2*s^2-1 := by linarith
  have hden : 0 < s^2-(Real.cos x)^2 := by nlinarith [mul_pos hsm hsp]
  have hsin : (Real.sin x)^2 = 1-(Real.cos x)^2 := by nlinarith [Real.sin_sq_add_cos_sq x]
  have he : (2*(Real.sin x)^4-(Real.sin x)^2)/(s-Real.cos x)+
      (2*(Real.sin x)^4-(Real.sin x)^2)/(s+Real.cos x)-
      (2*s/(2*s^2-1))*(1-2*(Real.cos x)^2) =
        (2*s*(s^2-1)*(1-2*(Real.cos x)^2)^2)/((2*s^2-1)*(s^2-(Real.cos x)^2)) := by
    rw [show (Real.sin x)^4 = ((Real.sin x)^2)^2 by ring,hsin]
    field_simp
    ring
  rw [← sub_nonneg,he]
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _))
    (mul_pos hd hden).le

/-- The required linear correction moment is nonnegative for every exterior cosine kernel. -/
theorem sine_correction_kernel_integral_nonneg (s : ℝ) (hs : 1 < s) :
    0 ≤ ∫ x in (0:ℝ)..Real.pi, (2*(Real.sin x)^4-(Real.sin x)^2)/(s-Real.cos x) := by
  let w : ℝ → ℝ := fun x => 2*(Real.sin x)^4-(Real.sin x)^2
  have hw : Continuous w := by unfold w;fun_prop
  have hm : Continuous (fun x => w x/(s-Real.cos x)) := hw.div
    (continuous_const.sub Real.continuous_cos) (fun x => by linarith [Real.cos_le_one x])
  have hp : Continuous (fun x => w x/(s+Real.cos x)) := hw.div
    (continuous_const.add Real.continuous_cos) (fun x => by linarith [Real.neg_one_le_cos x])
  have ic : IntervalIntegrable (fun x : ℝ => (Real.cos x)^2) volume 0 Real.pi := by
    apply Continuous.intervalIntegrable;fun_prop
  have ip : IntervalIntegrable (fun x : ℝ => 1-2*(Real.cos x)^2) volume 0 Real.pi := by
    apply Continuous.intervalIntegrable;fun_prop
  have hz : (∫ x in (0:ℝ)..Real.pi, 1-2*(Real.cos x)^2) = 0 := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (ic.const_mul 2),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const,integral_cos_sq]
    simp
    ring
  have he : (∫ x in (0:ℝ)..Real.pi, w x/(s+Real.cos x)) =
      ∫ x in (0:ℝ)..Real.pi, w x/(s-Real.cos x) := by
    calc
      _ = ∫ x in (0:ℝ)..Real.pi, w (Real.pi-x)/(s-Real.cos (Real.pi-x)) := by
        apply intervalIntegral.integral_congr
        intro x _
        simp [w,Real.sin_pi_sub,Real.cos_pi_sub]
      _ = _ := by
        simpa only [sub_self,sub_zero] using
          (intervalIntegral.integral_comp_sub_left (f := fun x => w x/(s-Real.cos x))
            (a := (0:ℝ)) (b := Real.pi) Real.pi)
  have hi := intervalIntegral.integral_mono_on Real.pi_pos.le (ip.const_mul (2*s/(2*s^2-1)))
    ((hm.intervalIntegrable _ _).add (hp.intervalIntegrable _ _))
    (fun x _ => sine_correction_kernel_pair s hs x)
  rw [intervalIntegral.integral_const_mul,hz,mul_zero,
    intervalIntegral.integral_add (hm.intervalIntegrable _ _) (hp.intervalIntegrable _ _),he] at hi
  linarith

/-- A finite nonnegative mixture of exterior cosine kernels has the sharp cubic ratio. -/
theorem sine_finite_kernel_profile_cubic {ι : Type*} (S : Finset ι) (c s : ι → ℝ)
    (hc : ∀ i ∈ S, 0 ≤ c i) (hs : ∀ i ∈ S, 1 < s i) :
    let V : ℝ → ℝ := fun x => ∑ i ∈ S, c i/(s i-Real.cos x)
    3*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2*(1+V x))^2 ≤
      2*Real.pi*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^4*(1+V x)^3) := by
  dsimp only
  apply sine_corrected_profile_cubic
  · apply continuous_finsetSum
    intro i hi
    exact continuous_const.div (continuous_const.sub Real.continuous_cos)
      (fun x => by linarith [hs i hi,Real.cos_le_one x])
  · intro x _
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (hc i hi) (by linarith [hs i hi,Real.cos_le_one x])
  · have hint (i : ι) (hi : i ∈ S) : IntervalIntegrable
        (fun x : ℝ => c i*((2*(Real.sin x)^4-(Real.sin x)^2)/(s i-Real.cos x))) volume 0 Real.pi := by
      apply Continuous.intervalIntegrable
      exact continuous_const.mul (((continuous_const.mul (Real.continuous_sin.pow 4)).sub
        (Real.continuous_sin.pow 2)).div (continuous_const.sub Real.continuous_cos)
        (fun x => by linarith [hs i hi,Real.cos_le_one x]))
    have he : (fun x : ℝ => (2*(Real.sin x)^4-(Real.sin x)^2)*(∑ i ∈ S, c i/(s i-Real.cos x))) =
        (fun x => ∑ i ∈ S, c i*((2*(Real.sin x)^4-(Real.sin x)^2)/(s i-Real.cos x))) := by
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he,intervalIntegral.integral_finsetSum hint]
    apply Finset.sum_nonneg
    intro i hi
    rw [intervalIntegral.integral_const_mul]
    exact mul_nonneg (hc i hi) (sine_correction_kernel_integral_nonneg (s i) (hs i hi))

/-- The correction moment is nonnegative for kernels on either side of the gap. -/
theorem sine_correction_exterior_kernel_integral_nonneg (s : ℝ) (hs : 1 < |s|) :
    0 ≤ ∫ x in (0:ℝ)..Real.pi,
      (2*(Real.sin x)^4-(Real.sin x)^2)/|s-Real.cos x| := by
  rcases lt_abs.mp hs with hp | hm
  · have he : (fun x : ℝ => (2*(Real.sin x)^4-(Real.sin x)^2)/|s-Real.cos x|) =
        (fun x => (2*(Real.sin x)^4-(Real.sin x)^2)/(s-Real.cos x)) := by
      funext x
      rw [abs_of_pos (by linarith [Real.cos_le_one x])]
    rw [he]
    exact sine_correction_kernel_integral_nonneg s hp
  · have he : (∫ x in (0:ℝ)..Real.pi,
        (2*(Real.sin x)^4-(Real.sin x)^2)/|s-Real.cos x|) =
        ∫ x in (0:ℝ)..Real.pi,
          (2*(Real.sin x)^4-(Real.sin x)^2)/(-s-Real.cos x) := by
      calc
        _ = ∫ x in (0:ℝ)..Real.pi,
            (2*(Real.sin (Real.pi-x))^4-(Real.sin (Real.pi-x))^2)/
              (-s-Real.cos (Real.pi-x)) := by
          apply intervalIntegral.integral_congr
          intro x _
          dsimp only
          rw [abs_of_neg (show s-Real.cos x < 0 by linarith [Real.neg_one_le_cos x]),
            Real.sin_pi_sub,Real.cos_pi_sub]
          congr 1
          ring
        _ = _ := by
          simpa only [sub_self,sub_zero] using
            (intervalIntegral.integral_comp_sub_left
              (f := fun x => (2*(Real.sin x)^4-(Real.sin x)^2)/(-s-Real.cos x))
              (a := (0:ℝ)) (b := Real.pi) Real.pi)
    rw [he]
    exact sine_correction_kernel_integral_nonneg (-s) (by linarith)

/-- A finite nonnegative mixture of exterior cosine kernels has the sharp cubic ratio. -/
theorem sine_finite_exterior_kernel_profile_cubic {ι : Type*} (S : Finset ι) (c s : ι → ℝ)
    (hc : ∀ i ∈ S, 0 ≤ c i) (hs : ∀ i ∈ S, 1 < |s i|) :
    let V : ℝ → ℝ := fun x => ∑ i ∈ S, c i/|s i-Real.cos x|
    3*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2*(1+V x))^2 ≤
      2*Real.pi*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^4*(1+V x)^3) := by
  have hden (i : ι) (hi : i ∈ S) (x : ℝ) : 0 < |s i-Real.cos x| := by
    apply abs_pos.mpr
    intro hz
    have he := sub_eq_zero.mp hz
    have hi' := hs i hi
    rw [he] at hi'
    exact (not_lt_of_ge (abs_le.mpr ⟨Real.neg_one_le_cos x,Real.cos_le_one x⟩)) hi'
  dsimp only
  apply sine_corrected_profile_cubic
  · apply continuous_finsetSum
    intro i hi
    exact continuous_const.div ((continuous_const.sub Real.continuous_cos).abs)
      (fun x => ne_of_gt (hden i hi x))
  · intro x _
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (hc i hi) (hden i hi x).le
  · have hint (i : ι) (hi : i ∈ S) : IntervalIntegrable
        (fun x : ℝ => c i*((2*(Real.sin x)^4-(Real.sin x)^2)/|s i-Real.cos x|)) volume 0 Real.pi := by
      apply Continuous.intervalIntegrable
      exact continuous_const.mul (((continuous_const.mul (Real.continuous_sin.pow 4)).sub
        (Real.continuous_sin.pow 2)).div ((continuous_const.sub Real.continuous_cos).abs)
        (fun x => ne_of_gt (hden i hi x)))
    have he : (fun x : ℝ => (2*(Real.sin x)^4-(Real.sin x)^2)*(∑ i ∈ S, c i/|s i-Real.cos x|)) =
        (fun x => ∑ i ∈ S, c i*((2*(Real.sin x)^4-(Real.sin x)^2)/|s i-Real.cos x|)) := by
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he,intervalIntegral.integral_finsetSum hint]
    apply Finset.sum_nonneg
    intro i hi
    rw [intervalIntegral.integral_const_mul]
    exact mul_nonneg (hc i hi) (sine_correction_exterior_kernel_integral_nonneg (s i) (hs i hi))

end NLS.ComplexAnalysis
