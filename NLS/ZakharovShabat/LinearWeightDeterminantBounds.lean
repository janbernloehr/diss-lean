import NLS.ZakharovShabat.LinearWeightCoefficientAnalytic
import NLS.ZakharovShabat.QuadraticLocalizationRadius
import NLS.ZakharovShabat.ResonantDeterminantBounds

/-! # Quantitative determinant bounds at the quadratic threshold

These estimates retain the Hilbert pair norm and work for complex potentials.
They concern the actual analytic determinant, without a qualitative cutoff.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- The leading Fourier terms and Lemma 25.3 bound each weighted off-diagonal. -/
theorem linearWeight_offDiagonal_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    w (2*n)*‖weightedResonantBPlusExtension (by simp) w φ n z‖ ≤ 2*‖φ.snd‖ ∧
    w (2*n)*‖weightedResonantBMinusExtension (by simp) w φ n z‖ ≤ 2*‖φ.fst‖ := by
  have hb := (linearWeight_resonantCoefficients w hw φ n hn).2.2.2 z hz
  have ht : (8/(1+|(n:ℝ)|))*‖φ‖^2 ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    simpa using hn
  have hlead (a : WeightedCoeff w.toWeight 2) (k : ℤ) : w k*‖a.val k‖ ≤ ‖a‖ := by
    have h := (le_div_iff₀ (w.toWeight.positive k)).mp (WeightedCoeff.norm_apply_le w.toWeight 2 a k)
    simpa only [SpectralWeight.toWeight, mul_comm] using! h
  constructor
  · have htriangle := mul_le_mul_of_nonneg_left
      (norm_le_norm_sub_add (weightedResonantBPlusExtension (by simp) w φ n z) (φ.snd.val (2*n)))
      (w.toWeight.positive (2*n)).le
    have hrem := hb.2.1.trans (mul_le_mul_of_nonneg_right ht (norm_nonneg φ.snd))
    have hc := hlead φ.snd (2*n)
    nlinarith
  · have htriangle := mul_le_mul_of_nonneg_left
      (norm_le_norm_sub_add (weightedResonantBMinusExtension (by simp) w φ n z) (φ.fst.val (-(2*n))))
      (w.toWeight.positive (2*n)).le
    have hrem := hb.2.2.trans (mul_le_mul_of_nonneg_right ht (norm_nonneg φ.fst))
    have hc := hlead φ.fst (-(2*n))
    rw [SpectralWeight.apply_neg] at hc
    nlinarith

/-- The product gains the square of the doubled-frequency weight. -/
theorem linearWeight_offDiagonal_product_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedResonantBPlusExtension (by simp) w φ n z *
      weightedResonantBMinusExtension (by simp) w φ n z‖ ≤ 2*‖φ‖^2/(w (2*n))^2 := by
  obtain ⟨hp,hm⟩ := linearWeight_offDiagonal_le w hw φ n hn z hz
  have hmul := mul_le_mul hp hm (mul_nonneg (w.toWeight.positive (2*n)).le (norm_nonneg _)) (by positivity)
  rw [norm_mul, le_div_iff₀ (sq_pos_of_pos (w.toWeight.positive (2*n))),
    WithLp.prod_norm_sq_eq_of_L2]
  nlinarith [sq_nonneg (‖φ.fst‖-‖φ.snd‖)]

/-- The M₁ factorization turns the product estimate into explicit bracket decay. -/
theorem linearWeight_offDiagonal_product_bracket_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedResonantBPlusExtension (by simp) w φ n z *
      weightedResonantBMinusExtension (by simp) w φ n z‖ ≤ 2*‖φ‖^2/(1+|((2*n:ℤ):ℝ)|)^2 := by
  apply (linearWeight_offDiagonal_product_le w hw φ n hn z hz).trans
  gcongr
  exact SpectralWeight.bracket_le_of_hasLinearFactor hw (2*n)

/-- Every actual determinant zero lies in the explicit source disc. -/
theorem linearWeight_determinant_root_localization (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ resonantStrip n)
    (hz0 : resonantDeterminantExtension (by simp) w φ n z = 0) :
    ‖z-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧ z ∈ refinedResonantDisk n := by
  have he : ‖z-(Real.pi:ℂ)*n-weightedResonantAExtension (by simp) w φ n z‖^2 =
      ‖weightedResonantBPlusExtension (by simp) w φ n z *
        weightedResonantBMinusExtension (by simp) w φ n z‖ := by
    rw [← norm_pow]
    exact congrArg norm (sub_eq_zero.mp hz0)
  have hsq := he.trans_le (linearWeight_offDiagonal_product_bracket_le w hw φ n hn z hz)
  have hrad : (Real.sqrt 2*‖φ‖/(1+|((2*n:ℤ):ℝ)|))^2 =
      2*‖φ‖^2/(1+|((2*n:ℤ):ℝ)|)^2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [← hrad] at hsq
  have hres := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
  have ha := ((linearWeight_resonantCoefficients w hw φ n hn).2.2.2 z hz).1
  have hloc : ‖z-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n := by
    have ht := norm_le_norm_sub_add (z-(Real.pi:ℂ)*n) (weightedResonantAExtension (by simp) w φ n z)
    unfold quadraticLocalizationRadius
    linarith
  refine ⟨hloc, ?_⟩
  change dist z ((Real.pi:ℂ)*n) < Real.pi/4
  rw [dist_eq_norm]
  exact hloc.trans_lt ((quadraticLocalizationRadius_lt_pi_div_five (norm_nonneg _) n hn).trans
    (by linarith [Real.pi_pos]))

/-- Rouché's strict comparison holds on the quarter-spacing circle at the explicit threshold. -/
theorem linearWeight_determinant_boundary_lt (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ Metric.sphere ((Real.pi:ℂ)*n) (Real.pi/4)) :
    ‖resonantDeterminantExtension (by simp) w φ n z-(z-(Real.pi:ℂ)*n)^2‖ <
      ‖(z-(Real.pi:ℂ)*n)^2‖ := by
  have hs : z ∈ resonantStrip n := closedBall_subset_resonantStrip n
    (by linarith [Real.pi_pos]) (Metric.sphere_subset_closedBall hz)
  have hq : ‖z-(Real.pi:ℂ)*n‖ = Real.pi/4 := by simpa only [dist_eq_norm] using Metric.mem_sphere.mp hz
  have ha := (((linearWeight_resonantCoefficients w hw φ n hn).2.2.2 z hs).1).trans
    (quadratic_threshold_diagonal_le n hn)
  have hb := (linearWeight_offDiagonal_product_bracket_le w hw φ n hn z hs).trans
    (quadratic_threshold_product_le n hn)
  rw [norm_mul] at hb
  apply (norm_resonant_quadratic_error_le _ _ _ _).trans_lt
  calc
    _ ≤ 2*(Real.pi/4)*(1/8)+(1/8:ℝ)^2+1/4 := by
      rw [hq]
      exact add_le_add (add_le_add (by gcongr) (by gcongr)) hb
    _ < ‖(z-(Real.pi:ℂ)*n)^2‖ := by
      rw [norm_pow, hq]
      nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi-3)]

end NLS.ZakharovShabat
