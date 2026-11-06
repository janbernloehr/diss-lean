import NLS.ComplexAnalysis.RealCutCircleIntegral
import NLS.ComplexAnalysis.BoundedPuncturedCircleIntegral

/-! # Weighted odd powers of a physical real-cut primitive

The counterclockwise integral is minus twice the literal real profile
integral. A continuous filled square bounds all weighted powers near
both endpoints. A collapsed cut is handled by bounded removability.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
namespace NLS.ComplexAnalysis

theorem circleIntegral_weighted_odd_power_eq_real_profile
    (f g : ℂ → ℂ) (v : ℝ → ℝ) (c d r R : ℝ)
    (hd : 0 ≤ d) (hdr : d < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f
      (ball (c : ℂ) R \ segment ℝ ((c-d : ℝ) : ℂ) ((c+d : ℝ) : ℂ)))
    (hg : AnalyticOnNhd ℂ g (ball (c : ℂ) R))
    (hsq : ∀ z ∈ ball (c : ℂ) R \ segment ℝ ((c-d : ℝ) : ℂ) ((c+d : ℝ) : ℂ), f z^2 = g z)
    (hv : ContinuousOn v (Icc (c-d) (c+d)))
    (hlower : ∀ x ∈ Icc (c-d) (c+d),
      Tendsto f (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (-(v x : ℂ))))
    (hupper : ∀ x ∈ Icc (c-d) (c+d),
      Tendsto f (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (v x : ℂ)))
    (m k : ℕ) :
    (∮ z in C((c : ℂ),r), z^m*f z^(2*k+1)) =
      -2 * ((∫ x in (c-d)..(c+d), x^m*v x^(2*k+1) : ℝ) : ℂ) := by
  let C := segment ℝ ((c-d : ℝ) : ℂ) ((c+d : ℝ) : ℂ)
  let T := (r+R)/2
  have hr : 0 < r := hd.trans_lt hdr
  have hrT : r < T := by dsimp only [T]; linarith
  have hT : 0 < T := hr.trans hrT
  have hTR : T < R := by dsimp only [T]; linarith
  obtain ⟨B,hB,hbound⟩ := exists_norm_bound_of_continuous_square_on_compact f g
    (closedBall (c : ℂ) T) C (isCompact_closedBall _ _)
    ((hg.mono (closedBall_subset_ball hTR)).continuousOn)
    (fun z hz => hsq z ⟨closedBall_subset_ball hTR hz.1,hz.2⟩)
  let M := (|c|+T)^m*B^(2*k+1)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hweighted (z : ℂ) (hz : z ∈ closedBall (c : ℂ) T \ C) :
      ‖z^m*f z^(2*k+1)‖ ≤ M := by
    have hznorm : ‖z‖ ≤ |c|+T := by
      have htri := norm_add_le (z-(c : ℂ)) (c : ℂ)
      have hzt : ‖z-(c : ℂ)‖ ≤ T := by simpa only [mem_closedBall,dist_eq_norm] using hz.1
      have hc : ‖(c : ℂ)‖ = |c| := by simp only [norm_real,Real.norm_eq_abs]
      rw [sub_add_cancel,hc] at htri
      linarith
    rw [norm_mul,norm_pow,norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hznorm m)
      (pow_le_pow_left₀ (norm_nonneg _) (hbound z hz) (2*k+1))
      (by positivity) (by positivity)
  let F : ℂ → ℂ := fun z => z^m*f z^(2*k+1)
  have hFa : AnalyticOnNhd ℂ F (ball (c : ℂ) R \ C) :=
    (analyticOnNhd_id.pow m).mul (hf.pow (2*k+1))
  by_cases hd0 : d = 0
  · have hsmall : AnalyticOnNhd ℂ F (ball (c : ℂ) T \ {(c : ℂ)}) := by
      have h := hFa.mono (show ball (c : ℂ) T \ C ⊆ ball (c : ℂ) R \ C from
        fun z hz => ⟨ball_subset_ball hTR.le hz.1,hz.2⟩)
      simpa only [C,hd0,sub_zero,add_zero,segment_same] using h
    have hz := circleIntegral_eq_zero_of_bounded_puncture F c r T M hr hrT hsmall
      (fun z hz => hweighted z ⟨ball_subset_closedBall hz.1,by
        simpa only [C,hd0,sub_zero,add_zero,segment_same] using hz.2⟩)
    simpa only [F,hd0,sub_zero,add_zero,intervalIntegral.integral_same,ofReal_zero,mul_zero] using hz
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  let lower : ℝ → ℂ := fun x => (x : ℂ)^m * (-(v x : ℂ))^(2*k+1)
  let upper : ℝ → ℂ := fun x => (x : ℂ)^m * (v x : ℂ)^(2*k+1)
  have hvC : ContinuousOn (fun x => (v x : ℂ)) (Icc (c-d) (c+d)) :=
    Complex.continuous_ofReal.comp_continuousOn hv
  have hxl (x : ℝ) : Tendsto (fun z : ℂ => z^m)
      (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 ((x : ℂ)^m)) :=
    ((continuous_id.pow m).tendsto (x : ℂ)).mono_left nhdsWithin_le_nhds
  have hxu (x : ℝ) : Tendsto (fun z : ℂ => z^m)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 ((x : ℂ)^m)) :=
    ((continuous_id.pow m).tendsto (x : ℂ)).mono_left nhdsWithin_le_nhds
  have he := circleIntegral_eq_neg_real_cut_jump F lower upper c d r R M hdpos hdr hrR hM hFa
    (fun z hz => hweighted z ⟨closedBall_subset_closedBall hrT.le hz.1,hz.2⟩)
    ((Complex.continuous_ofReal.continuousOn.pow m).mul (hvC.neg.pow (2*k+1)))
    ((Complex.continuous_ofReal.continuousOn.pow m).mul (hvC.pow (2*k+1)))
    (fun x hx => (hxl x).mul ((hlower x hx).pow (2*k+1)))
    (fun x hx => (hxu x).mul ((hupper x hx).pow (2*k+1)))
  have hodd (w : ℂ) : (-w)^(2*k+1) = -(w^(2*k+1)) := by
    simp only [pow_add,pow_mul,pow_one,neg_sq]
    ring
  calc
    (∮ z in C((c : ℂ),r), z^m*f z^(2*k+1)) = -(∫ x in (c-d)..(c+d), upper x-lower x) := he
    _ = -(∫ x in (c-d)..(c+d), 2*((x^m*v x^(2*k+1) : ℝ) : ℂ)) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [upper,lower]
      rw [hodd,ofReal_mul,ofReal_pow,ofReal_pow]
      ring
    _ = -2*((∫ x in (c-d)..(c+d), x^m*v x^(2*k+1) : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal]
      ring

end NLS.ComplexAnalysis
