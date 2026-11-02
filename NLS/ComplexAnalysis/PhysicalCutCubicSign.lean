import NLS.ComplexAnalysis.SignedSquareBoundary
import NLS.ComplexAnalysis.RealCutCircleIntegral
import NLS.ComplexAnalysis.BoundedPuncturedCircleIntegral

/-! # The sign of a cubic period on a physical real cut

A filled analytic square and the expanding/contracting half-plane signs
fix the full boundary profiles. The counterclockwise contour has the
negative upper-minus-lower jump. Collapsed cuts use bounded removability.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
namespace NLS.ComplexAnalysis

theorem circleIntegral_cubic_re_nonpos_of_physical_cut_square
    (f g : ℂ → ℂ) (c d r R : ℝ) (hd : 0 ≤ d) (hdr : d < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f
      (ball (c : ℂ) R \ segment ℝ ((c-d : ℝ) : ℂ) ((c+d : ℝ) : ℂ)))
    (hg : AnalyticOnNhd ℂ g (ball (c : ℂ) R))
    (hsq : ∀ z ∈ ball (c : ℂ) R \ segment ℝ ((c-d : ℝ) : ℂ) ((c+d : ℝ) : ℂ), f z^2 = g z)
    (hreal : ∀ x ∈ Icc (c-d) (c+d), (g (x : ℂ)).im = 0)
    (hnonneg : ∀ x ∈ Icc (c-d) (c+d), 0 ≤ (g (x : ℂ)).re)
    (hupper : ∀ z ∈ ball (c : ℂ) R, 0 < z.im → 0 < (f z).re)
    (hlower : ∀ z ∈ ball (c : ℂ) R, z.im < 0 → (f z).re < 0) :
    (∮ z in C((c : ℂ),r), f z^3).re ≤ 0 ∧ (∮ z in C((c : ℂ),r), f z^3).im = 0 := by
  let K := segment ℝ ((c-d : ℝ) : ℂ) ((c+d : ℝ) : ℂ)
  let T : ℝ := (r+R)/2
  have hr : 0 < r := hd.trans_lt hdr
  have hrT : r < T := by dsimp [T]; linarith
  have hTR : T < R := by dsimp [T]; linarith
  obtain ⟨B,hB,hbound⟩ := exists_norm_bound_of_continuous_square_on_compact f g
    (closedBall (c : ℂ) T) K (isCompact_closedBall _ _)
    ((hg.mono (closedBall_subset_ball hTR)).continuousOn)
    (fun z hz => hsq z ⟨closedBall_subset_ball hTR hz.1,hz.2⟩)
  have hbound3 (z : ℂ) (hz : z ∈ closedBall (c : ℂ) T \ K) : ‖f z^3‖ ≤ B^3 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound z hz) 3
  by_cases hd0 : d = 0
  · have hf0 : AnalyticOnNhd ℂ (fun z => f z^3) (ball (c : ℂ) T \ {(c : ℂ)}) := by
      have hsub : ball (c : ℂ) T \ segment ℝ ((c-d : ℝ) : ℂ) ((c+d : ℝ) : ℂ) ⊆
          ball (c : ℂ) R \ segment ℝ ((c-d : ℝ) : ℂ) ((c+d : ℝ) : ℂ) :=
        fun z hz => ⟨ball_subset_ball hTR.le hz.1,hz.2⟩
      have hmono : AnalyticOnNhd ℂ (fun z => f z^3)
          (ball (c : ℂ) T \ segment ℝ ((c-d : ℝ) : ℂ) ((c+d : ℝ) : ℂ)) :=
        fun z hz => (hf z (hsub hz)).pow 3
      simpa only [hd0,sub_zero,add_zero,segment_same] using hmono
    have hi := circleIntegral_eq_zero_of_bounded_puncture (fun z => f z^3) c r T (B^3)
      hr hrT hf0 (fun z hz => hbound3 z ⟨ball_subset_closedBall hz.1,by
        simpa only [K,hd0,sub_zero,add_zero,segment_same] using hz.2⟩)
    simp only [hi,zero_re,zero_im,le_refl,and_self]
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  let φ : ℝ → ℝ := fun x => Real.sqrt (g (x : ℂ)).re
  have hxball (x : ℝ) (hx : x ∈ Icc (c-d) (c+d)) : (x : ℂ) ∈ ball (c : ℂ) R := by
    have hh : |x-c| ≤ d := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    exact hh.trans_lt (hdr.trans hrR)
  have hroot (x : ℝ) (hx : x ∈ Icc (c-d) (c+d)) : sqrt (g (x : ℂ)) = (φ x : ℂ) := by
    have he : g (x : ℂ) = ((g (x : ℂ)).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [ofReal_im] using hreal x hx
    rw [he,Complex.sqrt_of_nonneg (by exact_mod_cast hnonneg x hx)]
    rfl
  have hφ : ContinuousOn φ (Icc (c-d) (c+d)) := by
    intro x hx
    exact (Real.continuous_sqrt.continuousAt.comp
      (continuous_re.continuousAt.comp
        ((hg (x : ℂ) (hxball x hx)).continuousAt.comp
          (f := fun x : ℝ => (x : ℂ)) Complex.continuous_ofReal.continuousAt))).continuousWithinAt
  have hup (x : ℝ) (hx : x ∈ Icc (c-d) (c+d)) :
      Tendsto f (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (φ x : ℂ)) := by
    have hb : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ), z ∈ ball (c : ℂ) R :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds (hxball x hx))
    rw [← hroot x hx]
    apply tendsto_sqrt_of_sq_re_pos f g _ (hnonneg x hx)
      ((hg (x : ℂ) (hxball x hx)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    · filter_upwards [hb,self_mem_nhdsWithin] with z hz hi
      exact hsq z ⟨hz,not_mem_real_segment_of_im_ne_zero _ _ z hi.ne'⟩
    · filter_upwards [hb,self_mem_nhdsWithin] with z hz hi
      exact hupper z hz hi
  have hlo (x : ℝ) (hx : x ∈ Icc (c-d) (c+d)) :
      Tendsto f (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (-(φ x : ℂ))) := by
    have hb : ∀ᶠ z in 𝓝[{z : ℂ | z.im < 0}] (x : ℂ), z ∈ ball (c : ℂ) R :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds (hxball x hx))
    rw [← hroot x hx]
    apply tendsto_neg_sqrt_of_sq_re_neg f g _ (hnonneg x hx)
      ((hg (x : ℂ) (hxball x hx)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    · filter_upwards [hb,self_mem_nhdsWithin] with z hz hi
      exact hsq z ⟨hz,not_mem_real_segment_of_im_ne_zero _ _ z hi.ne⟩
    · filter_upwards [hb,self_mem_nhdsWithin] with z hz hi
      exact hlower z hz hi
  have he := circleIntegral_eq_neg_real_cut_jump (fun z => f z^3)
    (fun x => -(φ x : ℂ)^3) (fun x => (φ x : ℂ)^3) c d r R (B^3)
    hdpos hdr hrR (by positivity) (hf.pow 3)
    (fun z hz => hbound3 z ⟨closedBall_subset_closedBall hrT.le hz.1,hz.2⟩)
    ((Complex.continuous_ofReal.comp_continuousOn hφ).pow 3).neg
    ((Complex.continuous_ofReal.comp_continuousOn hφ).pow 3)
    (fun x hx => by simpa only [show (-(φ x : ℂ))^3 = -(φ x : ℂ)^3 by ring] using (hlo x hx).pow 3)
    (fun x hx => (hup x hx).pow 3)
  have hi : (∮ z in C((c : ℂ),r), f z^3) =
      -2*((∫ x in (c-d)..(c+d), φ x^3 : ℝ) : ℂ) := by
    rw [he]
    simp_rw [show ∀ x, (φ x : ℂ)^3-(-(φ x : ℂ)^3) = 2*(φ x : ℂ)^3 by intro x; ring]
    rw [intervalIntegral.integral_const_mul]
    simp_rw [← ofReal_pow]
    rw [intervalIntegral.integral_ofReal]
    ring
  have hnonnegI : 0 ≤ ∫ x in (c-d)..(c+d), φ x^3 :=
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => pow_nonneg (Real.sqrt_nonneg _) 3)
  rw [hi]
  constructor
  · norm_num [Complex.mul_re]
    nlinarith
  · norm_num [Complex.mul_im]

end NLS.ComplexAnalysis
