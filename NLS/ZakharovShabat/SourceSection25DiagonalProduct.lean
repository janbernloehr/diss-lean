import NLS.ZakharovShabat.SourceSection25Coefficients

/-! # The component-product diagonal bound in the proof of Lemma 25.3 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- The common diagonal is bounded by the product of the two component norms. -/
theorem norm_weightedResonantA_le_component_product
    (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift (by simp) w φ n z hz‖ < 1)
    (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    ‖weightedResonantA (by simp) w φ n z hz h‖ ≤
      (2/(1+|(n:ℝ)|))*‖φ.fst‖*‖φ.snd‖ := by
  have hh := norm_weightedPotentialSquareInShift_le_half w hw φ n z hz hn
  rw [weightedResonantA_eq_tsum]
  have hr := (summable_and_diagonalRow_linear w hw φ.snd
    (weightedResonantEvenVector (by simp) w φ n z hz h 1).fst hz).2
  have hu := (shiftedNorm_fst_le_pair w n _).trans
    (shiftedPairNorm_evenVector_one_le (by simp) w φ n z hz h hh)
  apply hr.trans
  calc
    _ ≤ (1/(1+|(n:ℝ)|))*‖φ.snd‖*(2*‖φ.fst‖) := by gcongr
    _ = _ := by ring

/-- The original source retains the product bound on the entire closed strip. -/
theorem sourceM1_diagonal_component_bound (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : CoeffPair 2) (n : ℤ) (hn : 8*‖a‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedResonantAExtension (by simp) w (normalizedWeightedPeriodOne w a) n z‖ ≤
      (2/(1+|(n:ℝ)|))*‖a.fst‖*‖a.snd‖ := by
  have hn' : 8*‖normalizedWeightedPeriodOne w a‖^2 ≤ 1+|(n:ℝ)| := by
    simpa only [norm_normalizedWeightedPeriodOne] using hn
  have h := (norm_weightedPotentialSquareInShift_le_half w hw
    (normalizedWeightedPeriodOne w a) n z hz hn').trans_lt (by norm_num : (1/2:ℝ) < 1)
  rw [weightedResonantAExtension_eq (by simp) w _ n z hz h]
  have hf : ‖(normalizedWeightedPeriodOne w a).fst‖ = ‖a.fst‖ := by
    change ‖(WeightedCoeff.weightIsometry w.toWeight 2).symm (Coeff.periodDouble a.fst)‖ = _
    rw [(WeightedCoeff.weightIsometry w.toWeight 2).symm.norm_map,Coeff.norm_periodDouble]
  have hg : ‖(normalizedWeightedPeriodOne w a).snd‖ = ‖a.snd‖ := by
    change ‖(WeightedCoeff.weightIsometry w.toWeight 2).symm (Coeff.periodDouble a.snd)‖ = _
    rw [(WeightedCoeff.weightIsometry w.toWeight 2).symm.norm_map,Coeff.norm_periodDouble]
  simpa only [hf,hg] using
    norm_weightedResonantA_le_component_product w hw (normalizedWeightedPeriodOne w a) n z hz h hn'

end NLS.ZakharovShabat
