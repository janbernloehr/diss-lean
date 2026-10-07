import NLS.SequenceSpaces.SpectralConvolution

/-! # Tame weighted convolution estimates

An additive bound on the weight puts the high norm on only one factor of a
convolution. Sobolev weights satisfy this bound at every nonnegative real order.
-/
noncomputable section
namespace NLS.SpectralWeight

/-- Raw coefficient magnitudes sum to the unweighted norm. -/
theorem hasSum_unweighted_norm (w : SpectralWeight) (a : WeightedCoeff w.toWeight 1) :
    HasSum (fun n : ℤ => ‖a.val n‖) ‖w.toCoeff a‖ := by
  simpa only [ENNReal.toReal_one, Real.rpow_one, toCoeff_apply] using
    lp.hasSum_norm (p := 1) (by simp) (w.toCoeff a)

/-- Sobolev weights have an additive bound, with explicit order-dependent constant. -/
theorem sobolev_add_le (s : ℝ) (hs : 0 ≤ s) (n k : ℤ) :
    sobolev s hs (n+k) ≤ (2 : ℝ)^s * (sobolev s hs n + sobolev s hs k) := by
  simp only [sobolev_apply, Weight.sobolev_apply, Int.cast_add]
  have ht := abs_add_le (n : ℝ) (k : ℝ)
  rcases le_total |(n : ℝ)| |(k : ℝ)| with h | h
  · calc
      _ ≤ (2 * (1 + |(k : ℝ)|))^s :=
        Real.rpow_le_rpow (by positivity) (by linarith) hs
      _ = (2 : ℝ)^s * (1 + |(k : ℝ)|)^s := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_add_of_nonneg_left (by positivity)
  · calc
      _ ≤ (2 * (1 + |(n : ℝ)|))^s :=
        Real.rpow_le_rpow (by positivity) (by linarith) hs
      _ = (2 : ℝ)^s * (1 + |(n : ℝ)|)^s := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_add_of_nonneg_right (by positivity)

/-- An additive weight estimate separates the high norm of a translated sequence. -/
theorem norm_modulation_le_tame (w : SpectralWeight) (C : ℝ)
    (hadd : ∀ n k : ℤ, w (n+k) ≤ C*(w n+w k))
    (k : ℤ) (a : WeightedCoeff w.toWeight 1) :
    ‖w.modulation k a‖ ≤ C*(‖a‖ + w k*‖w.toCoeff a‖) := by
  have hsum : Summable (fun n : ℤ => w (n+k)*‖a.val n‖) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      w.summable_shiftedNorm_terms (p := 1) (by simp) k a
  have hmajor := ((w.hasSum_weighted_norm a).add
    ((w.hasSum_unweighted_norm a).mul_left (w k))).mul_left C
  calc
    _ = ∑' n : ℤ, w (n+k)*‖a.val n‖ := by
      rw [norm_modulation]
      simpa only [ENNReal.toReal_one, Real.rpow_one] using
        w.shiftedNorm_rpow_eq_tsum (p := 1) (by simp) k a
    _ ≤ ∑' n : ℤ, C*(w n*‖a.val n‖ + w k*‖a.val n‖) := by
      apply Summable.tsum_le_tsum _ hsum hmajor.summable
      intro n
      nlinarith [mul_le_mul_of_nonneg_right (hadd n k) (norm_nonneg (a.val n))]
    _ = _ := hmajor.tsum_eq

/-- The high convolution norm is linear in the high norm of each factor. -/
theorem norm_convolution_le_tame (w : SpectralWeight) (C : ℝ)
    (hadd : ∀ n k : ℤ, w (n+k) ≤ C*(w n+w k))
    (a b : WeightedCoeff w.toWeight 1) :
    ‖w.convolution a b‖ ≤ C*(‖a‖*‖w.toCoeff b‖ + ‖w.toCoeff a‖*‖b‖) := by
  have hmajor := (((w.hasSum_unweighted_norm b).mul_left ‖a‖).add
    ((w.hasSum_weighted_norm b).mul_left ‖w.toCoeff a‖)).mul_left C
  calc
    _ ≤ ∑' k : ℤ, ‖b.val k • w.modulation k a‖ :=
      norm_tsum_le_tsum_norm (w.summable_norm_convolution_terms a b)
    _ ≤ ∑' k : ℤ, C*(‖a‖*‖b.val k‖ + ‖w.toCoeff a‖*(w k*‖b.val k‖)) := by
      apply Summable.tsum_le_tsum _ (w.summable_norm_convolution_terms a b) hmajor.summable
      intro k
      rw [norm_smul]
      nlinarith [mul_le_mul_of_nonneg_left (w.norm_modulation_le_tame C hadd k a)
        (norm_nonneg (b.val k))]
    _ = _ := hmajor.tsum_eq

/-- Tame Young inequality for every nonnegative real Sobolev order. -/
theorem norm_sobolev_convolution_le (s : ℝ) (hs : 0 ≤ s)
    (a b : WeightedCoeff (sobolev s hs).toWeight 1) :
    ‖(sobolev s hs).convolution a b‖ ≤ (2 : ℝ)^s *
      (‖a‖*‖(sobolev s hs).toCoeff b‖ + ‖(sobolev s hs).toCoeff a‖*‖b‖) :=
  (sobolev s hs).norm_convolution_le_tame _ (sobolev_add_le s hs) a b

end NLS.SpectralWeight
