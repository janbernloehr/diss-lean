import NLS.ZakharovShabat.LinearWeightDeterminantBounds
import NLS.ZakharovShabat.ResonantRootGap

/-! # The factor-six gap estimate at the explicit quadratic threshold -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Cauchy's estimate at this threshold gives a diagonal derivative at most one sixth. -/
theorem norm_deriv_le_sixth_on_refined_disk (n : ℤ) (a : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ 1/8) (x : ℂ) (hx : x ∈ refinedResonantDisk n) :
    ‖deriv a x‖ ≤ 1/6 := by
  have hball := closedBall_refined_point_subset_strip n x hx
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < Real.pi/4)
    (ha.differentiableOn.diffContOnCl_ball hball)
    (fun z hz => hb z (hball (Metric.sphere_subset_closedBall hz)))
  apply h.trans
  apply (div_le_iff₀ (by positivity : 0 < Real.pi/4)).mpr
  linarith [Real.pi_gt_three]

/-- The weaker one-sixth Lipschitz bound still gives the source factor six. -/
theorem norm_gap_sq_le_of_sixth_residual_bounds (c x y : ℂ) (a : ℂ → ℂ) (M : ℝ)
    (ha : ‖a x-a y‖ ≤ (1/6 : ℝ)*‖x-y‖)
    (hx : ‖x-c-a x‖^2 ≤ M) (hy : ‖y-c-a y‖^2 ≤ M) : ‖x-y‖^2 ≤ 6*M := by
  have he : x-y = (a x-a y) + ((x-c-a x)-(y-c-a y)) := by ring
  have ht : ‖x-y‖ ≤ (1/6 : ℝ)*‖x-y‖ + (‖x-c-a x‖ + ‖y-c-a y‖) := by
    calc
      _ = ‖(a x-a y) + ((x-c-a x)-(y-c-a y))‖ := congrArg norm he
      _ ≤ ‖a x-a y‖ + (‖x-c-a x‖ + ‖y-c-a y‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
      _ ≤ _ := add_le_add ha le_rfl
  have hlin : (5/6 : ℝ)*‖x-y‖ ≤ ‖x-c-a x‖+‖y-c-a y‖ := by linarith
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ (5/6 : ℝ)*‖x-y‖) hlin
  have hM : 0 ≤ M := (sq_nonneg _).trans hx
  nlinarith [sq_nonneg (‖x-c-a x‖-‖y-c-a y‖)]

/-- The actual full-strip product supremum is finite with the explicit bracket bound. -/
theorem linearWeight_BProductSup_bounds (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    0 ≤ resonantBProductSup (by simp) w φ n ∧
    resonantBProductSup (by simp) w φ n ≤ 2*‖φ‖^2/(1+|((2*n:ℤ):ℝ)|)^2 ∧
    ∀ z ∈ resonantStrip n,
      ‖weightedResonantBPlusExtension (by simp) w φ n z *
        weightedResonantBMinusExtension (by simp) w φ n z‖ ≤ resonantBProductSup (by simp) w φ n := by
  have hpoint (z : ℂ) (hz : z ∈ resonantStrip n) :
      SpectralWeight.one (2*n)*‖weightedResonantBPlusExtension (by simp) w φ n z *
        weightedResonantBMinusExtension (by simp) w φ n z‖ ≤ 2*‖φ‖^2/(1+|((2*n:ℤ):ℝ)|)^2 := by
    simpa only [SpectralWeight.one_apply, one_mul] using
      linearWeight_offDiagonal_product_bracket_le w hw φ n hn z hz
  simpa only [resonantBProductSup, SpectralWeight.one_apply, one_mul] using
    weightedStripSup_bounds SpectralWeight.one n _ _ hpoint

/-- Any two determinant zeros obey the factor-six estimate at the same explicit threshold. -/
theorem linearWeight_determinant_root_gap_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (x y : ℂ) (hx : x ∈ resonantStrip n) (hy : y ∈ resonantStrip n)
    (hx0 : resonantDeterminantExtension (by simp) w φ n x = 0)
    (hy0 : resonantDeterminantExtension (by simp) w φ n y = 0) :
    ‖x-y‖^2 ≤ 6*resonantBProductSup (by simp) w φ n := by
  have ha := (linearWeight_resonantCoefficients w hw φ n hn).1
  have hb (z : ℂ) (hz : z ∈ resonantStrip n) :=
    (((linearWeight_resonantCoefficients w hw φ n hn).2.2.2 z hz).1).trans
      (quadratic_threshold_diagonal_le n hn)
  have hdisk := linearWeight_determinant_root_localization w hw φ n hn
  have hlip : ‖weightedResonantAExtension (by simp) w φ n x-
      weightedResonantAExtension (by simp) w φ n y‖ ≤ (1/6:ℝ)*‖x-y‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (ha z (refinedResonantDisk_subset_strip n hz)).differentiableAt)
      (norm_deriv_le_sixth_on_refined_disk n _ ha hb) (convex_ball _ _)
      (hdisk y hy hy0).2 (hdisk x hx hx0).2
  have hsup := linearWeight_BProductSup_bounds w hw φ n hn
  have hresidual (z : ℂ) (hz : z ∈ resonantStrip n)
      (hz0 : resonantDeterminantExtension (by simp) w φ n z = 0) :
      ‖z-(Real.pi:ℂ)*n-weightedResonantAExtension (by simp) w φ n z‖^2 ≤
        resonantBProductSup (by simp) w φ n := by
    have he : ‖z-(Real.pi:ℂ)*n-weightedResonantAExtension (by simp) w φ n z‖^2 =
        ‖weightedResonantBPlusExtension (by simp) w φ n z *
          weightedResonantBMinusExtension (by simp) w φ n z‖ := by
      rw [← norm_pow]
      exact congrArg norm (sub_eq_zero.mp hz0)
    exact he.trans_le (hsup.2.2 z hz)
  exact norm_gap_sq_le_of_sixth_residual_bounds ((Real.pi:ℂ)*n) x y _ _ hlip
    (hresidual x hx hx0) (hresidual y hy hy0)

end NLS.ZakharovShabat
