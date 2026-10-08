import NLS.ZakharovShabat.LinearWeightDiagonalRow
import NLS.ZakharovShabat.LinearWeightSquareEstimate
import NLS.ZakharovShabat.ResonantDiagonalEstimate
import NLS.ZakharovShabat.ResonantEvenBounds

/-! # Lemma 25.3: the actual resonant coefficient bounds

The explicit quadratic threshold gives the diagonal constant one and the
off-diagonal constant eight, with each component's norm and Fourier sign
retained. The potential may be an arbitrary complex Hilbert pair.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The first scalar shifted norm is controlled by the actual Hilbert pair norm. -/
theorem shiftedNorm_fst_le_pair (w : SpectralWeight) (n : ℤ) (f : WeightedCoeffPair w.toWeight 2) :
    w.shiftedNorm (-n) f.fst ≤ w.shiftedPairNorm n f := by
  rw [← SpectralWeight.norm_modulation]
  exact WithLp.norm_fst_le _ (w.pairModulation n f)

/-- Evaluating either resonant coordinate gains the exact weight w(2n). -/
theorem weighted_resonant_coordinate_le (w : SpectralWeight) (n : ℤ)
    (f : WeightedCoeffPair w.toWeight 2) (i : Fin 2) :
    w (2*n)*‖resonantCoordinates w.toWeight n f i‖ ≤ w.shiftedPairNorm n f := by
  fin_cases i
  · change w (2*n)*‖resonantCoordinates w.toWeight n f 0‖ ≤ w.shiftedPairNorm n f
    rw [resonantCoordinates_zero]
    have h := WeightedCoeff.norm_apply_le (w.toWeight.shift (-n)) 2 (w.toShift (-n) f.fst) (-n)
    have he : w (-n+ -n) = w (2*n) := by rw [show -n+ -n=-(2*n) by ring, w.apply_neg]
    simp only [SpectralWeight.toShift_apply, Weight.shift_apply, he] at h
    have h' := (le_div_iff₀ (w.positive (2*n))).mp h
    exact le_trans (by simpa only [mul_comm, SpectralWeight.shiftedNorm] using! h') (shiftedNorm_fst_le_pair w n f)
  · change w (2*n)*‖resonantCoordinates w.toWeight n f 1‖ ≤ w.shiftedPairNorm n f
    rw [resonantCoordinates_one]
    have h := WeightedCoeff.norm_apply_le (w.toWeight.shift n) 2 (w.toShift n f.snd) n
    simp only [SpectralWeight.toShift_apply, Weight.shift_apply, ← two_mul] at h
    have h' := (le_div_iff₀ (w.positive (2*n))).mp h
    have hpair : w.shiftedNorm n f.snd ≤ w.shiftedPairNorm n f := by
      rw [← SpectralWeight.norm_modulation]
      exact WithLp.norm_snd_le _ (w.pairModulation n f)
    exact le_trans (by simpa only [mul_comm, SpectralWeight.shiftedNorm] using! h') hpair

/-- The diagonal estimate of Lemma 25.3, retaining the actual common diagonal. -/
theorem norm_weightedResonantA_linear (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift (by simp) w φ n z hz‖ < 1)
    (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    ‖weightedResonantA (by simp) w φ n z hz h‖ ≤ ‖φ‖^2/(1+|(n:ℝ)|) := by
  have hh := norm_weightedPotentialSquareInShift_le_half w hw φ n z hz hn
  rw [weightedResonantA_eq_tsum]
  have hr := (summable_and_diagonalRow_linear w hw φ.snd
    (weightedResonantEvenVector (by simp) w φ n z hz h 1).fst hz).2
  have hu := (shiftedNorm_fst_le_pair w n _).trans
    (shiftedPairNorm_evenVector_one_le (by simp) w φ n z hz h hh)
  apply hr.trans
  calc
    _ ≤ (1/(1+|(n:ℝ)|))*‖φ.snd‖*(2*‖φ.fst‖) := by gcongr
    _ ≤ _ := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      have hp : 0 < 1+|(n:ℝ)| := by positivity
      apply (le_div_iff₀ hp).mpr
      field_simp
      nlinarith [sq_nonneg (‖φ.fst‖-‖φ.snd‖)]

/-- The positive off-diagonal remainder uses the second component at +2n. -/
theorem weightedResonantBPlus_remainder_linear (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift (by simp) w φ n z hz‖ < 1)
    (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    w (2*n)*‖weightedResonantBPlus (by simp) w φ n z hz h-φ.snd.val (2*n)‖ ≤
      (8/(1+|(n:ℝ)|))*‖φ‖^2*‖φ.snd‖ := by
  have hh := norm_weightedPotentialSquareInShift_le_half w hw φ n z hz hn
  rw [weightedResonantBPlus_remainder]
  apply (weighted_resonant_coordinate_le w n _ 1).trans
  apply (shiftedPairNorm_weightedPotentialInverse_sq_linear w hw φ n z hz _).trans
  have hu := shiftedPairNorm_evenVector_zero_le (by simp) w φ n z hz h hh
  calc
    _ ≤ (4/(1+|(n:ℝ)|))*‖φ‖^2*(2*‖φ.snd‖) := by gcongr
    _ = _ := by ring

/-- The negative off-diagonal remainder uses the first component at -2n. -/
theorem weightedResonantBMinus_remainder_linear (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift (by simp) w φ n z hz‖ < 1)
    (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    w (2*n)*‖weightedResonantBMinus (by simp) w φ n z hz h-φ.fst.val (-(2*n))‖ ≤
      (8/(1+|(n:ℝ)|))*‖φ‖^2*‖φ.fst‖ := by
  have hh := norm_weightedPotentialSquareInShift_le_half w hw φ n z hz hn
  rw [weightedResonantBMinus_remainder]
  apply (weighted_resonant_coordinate_le w n _ 0).trans
  apply (shiftedPairNorm_weightedPotentialInverse_sq_linear w hw φ n z hz _).trans
  have hu := shiftedPairNorm_evenVector_one_le (by simp) w φ n z hz h hh
  calc
    _ ≤ (4/(1+|(n:ℝ)|))*‖φ‖^2*(2*‖φ.fst‖) := by gcongr
    _ = _ := by ring

end NLS.ZakharovShabat
