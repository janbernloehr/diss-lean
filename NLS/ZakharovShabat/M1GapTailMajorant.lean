import NLS.ZakharovShabat.M1CanonicalGap
import NLS.SequenceSpaces.BracketSquareTail

/-! # The exact Hilbert gap majorant for Proposition 25.5 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Splitting both off-diagonal coefficients retains the source constant six. -/
theorem gap_sq_le_six_leading_remainder (d l m r s : ℝ)
    (h : d^2 ≤ 6*(l+r)*(m+s)) : d^2 ≤ 6*(l^2+m^2+r^2+s^2) := by
  nlinarith [sq_nonneg ((l+r)-(m+s)),sq_nonneg (l-r),sq_nonneg (m-s)]

/-- The pointwise majorant retains the signed leading coefficients and the precise quadratic remainder. -/
theorem M1_canonicalGap_tail_majorant (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2 ≤
      6*resonantLeadingPower w φ n+384*‖φ‖^6*ReciprocalSeries.bracketInverseSq n := by
  let L := w (2*n)*‖φ.fst.val (-(2*n))‖
  let M := w (2*n)*‖φ.snd.val (2*n)‖
  let R := (8/(1+|(n:ℝ)|))*‖φ‖^2*‖φ.fst‖
  let S := (8/(1+|(n:ℝ)|))*‖φ‖^2*‖φ.snd‖
  have hfull := weighted_resonantBProductSup_le (by simp) w φ n (L+R) (M+S)
    (add_nonneg (mul_nonneg (w.positive (2*n)).le (norm_nonneg _)) (by dsimp [R]; positivity))
    (fun z hz => by
      have hb := (linearWeight_resonantCoefficients w hw φ n hn).2.2.2 z hz
      have hminus := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add
        (weightedResonantBMinusExtension (by simp) w φ n z) (φ.fst.val (-(2*n)))) (w.positive (2*n)).le
      have hplus := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add
        (weightedResonantBPlusExtension (by simp) w φ n z) (φ.snd.val (2*n))) (w.positive (2*n)).le
      dsimp [L,M,R,S]
      constructor <;> nlinarith [hb.2.1,hb.2.2])
  have hg := mul_le_mul_of_nonneg_left (M1_canonicalEndpoints_localization w hw φ heven n hn).2.2
    (sq_nonneg (w (2*n)))
  have h := gap_sq_le_six_leading_remainder
    (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)
    L M R S (by rw [mul_pow]; nlinarith)
  have hlead : L^2+M^2 = resonantLeadingPower w φ n := by
    simp only [resonantLeadingPower,ENNReal.toReal_ofNat,Real.rpow_two,L,M]
  have hrem : R^2+S^2 = 64*‖φ‖^6*ReciprocalSeries.bracketInverseSq n := by
    dsimp [R,S,ReciprocalSeries.bracketInverseSq]
    have he : ‖φ‖^6 = (‖φ‖^2)^3 := by ring
    rw [he,WithLp.prod_norm_sq_eq_of_L2]
    simp only [div_eq_mul_inv,← inv_pow]
    ring
  calc
    _ ≤ 6*(L^2+M^2+(R^2+S^2)) := by simpa only [add_assoc] using h
    _ = _ := by rw [hlead,hrem]; ring

end NLS.ZakharovShabat
