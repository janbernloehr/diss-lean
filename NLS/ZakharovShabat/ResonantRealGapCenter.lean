import NLS.ZakharovShabat.ResonantDoubleRootClosing
import NLS.ZakharovShabat.ResonantDiagonalCenter

/-! # Real gap bounds at the diagonal center

Real counted roots control both off-diagonal coefficients at the actual
diagonal fixed point. Distinct and collapsed gaps are both included.
-/

noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

private theorem real_residual_bound_of_abs_difference (g h δ : ℝ) (hδ : 0 < δ)
    (hlo : (7/8:ℝ)*δ ≤ |g-h|) (hhi : |g-h| ≤ (9/8:ℝ)*δ)
    (habs : abs (|g|-|h|) ≤ (1/4:ℝ)*δ) : |g| ≤ (9/8:ℝ)*δ := by
  rcases le_total 0 g with hg | hg <;> rcases le_total 0 h with hh | hh
  · simp only [abs_of_nonneg hg,abs_of_nonneg hh] at habs
    linarith
  · rw [abs_of_nonneg hg]
    have h := (abs_le.mp hhi).2
    linarith
  · rw [abs_of_nonpos hg]
    have h := (abs_le.mp hhi).1
    linarith
  · simp only [abs_of_nonpos hg,abs_of_nonpos hh] at habs
    have he : -g- -h = -(g-h) := by ring
    rw [he,abs_neg] at habs
    linarith

/-- The two off-diagonal center values are bounded by twice the real gap.
The repeated-root case uses its counted multiplicity, with no division by the gap. -/
theorem norm_resonant_offDiagonal_center_le_gap (n : ℤ) (a b d : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : AnalyticOnNhd ℂ b (resonantStrip n))
    (hd : AnalyticOnNhd ℂ d (resonantStrip n))
    (hbound : ∀ z ∈ resonantStrip n,
      ‖a z‖ ≤ Real.pi/32 ∧ ‖b z‖ ≤ Real.pi/16 ∧ ‖d z‖ ≤ Real.pi/16)
    (x y ζ : ℂ) (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n)
    (hζ : ζ ∈ refinedResonantDisk n) (hfix : ζ = (Real.pi:ℂ)*n+a ζ)
    (hxim : x.im = 0) (hyim : y.im = 0) (hax : (a x).im = 0) (hay : (a y).im = 0)
    (hnormx : ‖b x‖ = ‖d x‖) (hnormy : ‖b y‖ = ‖d y‖)
    (hx0 : (x-(Real.pi:ℂ)*n-a x)^2-b x*d x = 0)
    (hy0 : (y-(Real.pi:ℂ)*n-a y)^2-b y*d y = 0)
    (hdouble : x = y → deriv (fun z => (z-(Real.pi:ℂ)*n-a z)^2-b z*d z) x = 0) :
    ‖b ζ‖ ≤ 2*‖x-y‖ ∧ ‖d ζ‖ ≤ 2*‖x-y‖ := by
  let c : ℂ := (Real.pi:ℂ)*n
  let R := fun z => z-c-a z
  have hRnorm (z : ℂ) (hz : (z-c-a z)^2-b z*d z = 0) (hn : ‖b z‖ = ‖d z‖) :
      ‖R z‖ = ‖b z‖ := by
    have hs : ‖R z‖^2 = ‖b z‖^2 := by
      rw [← norm_pow, show R z^2 = b z*d z from sub_eq_zero.mp hz,norm_mul,← hn,pow_two]
    nlinarith [norm_nonneg (R z),norm_nonneg (b z)]
  have hbx : ‖b x‖ ≤ (9/8:ℝ)*‖x-y‖ := by
    by_cases he : x = y
    · have hz := (resonant_double_zero_closing_on_refined_disk n a b d ha hb hd hbound
        x hx hnormx hx0 (hdouble he)).2.1
      simp only [hz,norm_zero]
      positivity
    · have hδ : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
      have hex : R x = ((R x).re : ℂ) := by
        apply Complex.ext
        · rfl
        · simp [R,c,hxim,hax]
      have hey : R y = ((R y).re : ℂ) := by
        apply Complex.ext
        · rfl
        · simp [R,c,hyim,hay]
      have hxabs : ‖b x‖ = |(R x).re| := by
        rw [← hRnorm x hx0 hnormx,hex,Complex.norm_real,Real.norm_eq_abs]
        simp only [Complex.ofReal_re]
      have hyabs : ‖b y‖ = |(R y).re| := by
        rw [← hRnorm y hy0 hnormy,hey,Complex.norm_real,Real.norm_eq_abs]
        simp only [Complex.ofReal_re]
      have hsub : ‖R x-R y‖ = |(R x).re-(R y).re| := by
        rw [hex,hey,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
        simp only [Complex.ofReal_re]
      have haLip := norm_diagonal_sub_le_on_refined_disk n a ha (fun z hz => (hbound z hz).1) x y hx hy
      have heq : x-y = (R x-R y)+(a x-a y) := by dsimp [R]; ring
      have hlo : (7/8:ℝ)*‖x-y‖ ≤ |(R x).re-(R y).re| := by
        have h := norm_add_le (R x-R y) (a x-a y)
        rw [← heq,hsub] at h
        linarith
      have hhi : |(R x).re-(R y).re| ≤ (9/8:ℝ)*‖x-y‖ := by
        have heq' : R x-R y = (x-y)-(a x-a y) := by dsimp [R]; ring
        have h := norm_sub_le (x-y) (a x-a y)
        rw [← heq',hsub] at h
        linarith
      have hbLip : ‖b x-b y‖ ≤ (1/4:ℝ)*‖x-y‖ :=
        Convex.norm_image_sub_le_of_norm_deriv_le
          (fun z hz => (hb z (refinedResonantDisk_subset_strip n hz)).differentiableAt)
          (norm_deriv_offDiagonal_le_on_refined_disk n b hb (fun z hz => (hbound z hz).2.1))
          (convex_ball _ _) hy hx
      have habs := (abs_norm_sub_norm_le (b x) (b y)).trans hbLip
      rw [hxabs,hyabs] at habs
      rw [hxabs]
      exact real_residual_bound_of_abs_difference _ _ _ hδ hlo hhi habs
  have hzx : ‖ζ-x‖ ≤ (8/7:ℝ)*‖b x‖ := by
    have he : ζ-x = (a ζ-a x)-R x := by dsimp [R]; linear_combination hfix
    have ht := norm_sub_le (a ζ-a x) (R x)
    rw [← he,hRnorm x hx0 hnormx] at ht
    have hlip := norm_diagonal_sub_le_on_refined_disk n a ha (fun z hz => (hbound z hz).1) ζ x hζ hx
    linarith
  have hnorm (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (resonantStrip n))
      (hfb : ∀ z ∈ resonantStrip n, ‖f z‖ ≤ Real.pi/16) (he : ‖f x‖ = ‖b x‖) :
      ‖f ζ‖ ≤ 2*‖x-y‖ := by
    have hlip : ‖f ζ-f x‖ ≤ (1/4:ℝ)*‖ζ-x‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hf z (refinedResonantDisk_subset_strip n hz)).differentiableAt)
        (norm_deriv_offDiagonal_le_on_refined_disk n f hf hfb) (convex_ball _ _) hx hζ
    have ht := norm_le_norm_sub_add (f ζ) (f x)
    rw [he] at ht
    linarith [norm_nonneg (x-y)]
  exact ⟨hnorm b hb (fun z hz => (hbound z hz).2.1) rfl,
    hnorm d hd (fun z hz => (hbound z hz).2.2) hnormx.symm⟩
end NLS.ZakharovShabat
