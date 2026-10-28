import NLS.ZakharovShabat.OffDiagonalProofBounds
import NLS.ZakharovShabat.SourceLemma6_8ProofSeries
import NLS.ZakharovShabat.SourceCoefficientFullCutoffs

/-! # The literal off-diagonal proof of Lemma 6.8

The original analytic coefficients and genuine full-strip suprema inherit
bounds from the exact regional Holder tests and summable power moments.
The full weighted pair norm and both component tails retain the source scope.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The negative coefficient retains the tails of both potential components. -/
theorem weightedResonantBMinus_remainder_proof_le (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ resonantStrip n) (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) :
    w (2*n) * ‖weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n))‖ ≤
      offDiagonalProofBound hp w (w.reflection φ.fst) φ.snd N n := by
  have hf : w.shiftedNorm n (w.reflection (weightedResonantEvenVector hp w φ n z hz h 1).fst) ≤
      2 * ‖w.reflection φ.fst‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact (shiftedNorm_reflected_fst_le_pair w n _).trans
      (shiftedPairNorm_evenVector_one_le hp w φ n z hz h hh)
  have ht := weighted_norm_tsum_offDiagonal_proof_le hp hp1 w (w.reflection φ.fst) φ.snd
    (w.reflection (weightedResonantEvenVector hp w φ n z hz h 1).fst) N n hn z hz hf
  rw [weightedResonantBMinus_remainder_eq_tsum]
  simpa only [SpectralWeight.reflection_apply] using ht

/-- The positive coefficient has the matching refined bound with the components exchanged. -/
theorem weightedResonantBPlus_remainder_proof_le (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ resonantStrip n) (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) :
    w (2*n) * ‖weightedResonantBPlus hp w φ n z hz h - φ.snd.val (2*n)‖ ≤
      offDiagonalProofBound hp w φ.snd (w.reflection φ.fst) N n := by
  have hf := (shiftedNorm_snd_le_pair w n (weightedResonantEvenVector hp w φ n z hz h 0)).trans
    (shiftedPairNorm_evenVector_zero_le hp w φ n z hz h hh)
  have ht := weighted_norm_tsum_offDiagonal_proof_le hp hp1 w φ.snd (w.reflection φ.fst)
    (weightedResonantEvenVector hp w φ n z hz h 0).snd N n hn z hz hf
  rw [weightedResonantBPlus_remainder_eq_tsum]
  simpa only [SpectralWeight.reflection_apply] using ht

/-- One neighborhood controls the original full-strip suprema by the exact regional bounds at every larger cutoff. -/
theorem exists_uniform_sourceOffDiagonalProofBound (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℤ, N ≤ n.natAbs →
        let η := sourceWeightedPeriodTwoInput w ψ
        BddAbove ((fun z : ℂ => w (2*n)*‖sourceResonantBMinusFunction hp η n z-η.fst (-(2*n))‖) '' resonantStrip n) ∧
        BddAbove ((fun z : ℂ => w (2*n)*‖sourceResonantBPlusFunction hp η n z-η.snd (2*n)‖) '' resonantStrip n) ∧
        (0 ≤ sourceResonantBMinusSup hp w η n ∧ sourceResonantBMinusSup hp w η n ≤
          offDiagonalProofBound hp w (w.reflection ψ.fst) ψ.snd N n) ∧
        (0 ≤ sourceResonantBPlusSup hp w η n ∧ sourceResonantBPlusSup hp w η n ≤
          offDiagonalProofBound hp w ψ.snd (w.reflection ψ.fst) N n) := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,_,hb⟩ := exists_uniform_complementarySquare_half hp w φ
  obtain ⟨N₂,hN₂,U₂,ho₂,hc₂,hφ₂,h0₂,heq⟩ := exists_uniform_sourceResonantFunctions_weightedInput hp w φ
  refine ⟨max N₁ N₂,by omega,U₁ ∩ U₂,ho₁.inter ho₂,hc₁.inter hc₂,⟨hφ₁,hφ₂⟩,⟨h0₁,h0₂⟩,?_⟩
  intro ψ hψ N hN n hn
  dsimp only
  let η := sourceWeightedPeriodTwoInput w ψ
  let M := offDiagonalProofBound hp w (w.reflection ψ.fst) ψ.snd N n
  let P := offDiagonalProofBound hp w ψ.snd (w.reflection ψ.fst) N n
  have hpoint (z : ℂ) (hz : z ∈ resonantStrip n) :
      w (2*n)*‖sourceResonantBMinusFunction hp η n z-η.fst (-(2*n))‖ ≤ M ∧
      w (2*n)*‖sourceResonantBPlusFunction hp η n z-η.snd (2*n)‖ ≤ P := by
    have hh := (hb ψ hψ.1 n (by omega) z hz).1
    have h := hh.trans_lt (by norm_num : (1/2:ℝ) < 1)
    have he := heq ψ hψ.2 n (by omega) z hz
    dsimp [η,M,P]
    rw [he.2.2,he.2.1,sourceWeightedPeriodTwoInput_fst,sourceWeightedPeriodTwoInput_snd,
      weightedResonantBMinusExtension_eq hp w ψ n z hz h,weightedResonantBPlusExtension_eq hp w ψ n z hz h]
    exact ⟨weightedResonantBMinus_remainder_proof_le hp hp1 w ψ N n hn z hz h hh,
      weightedResonantBPlus_remainder_proof_le hp hp1 w ψ N n hn z hz h hh⟩
  have hm := weightedStripSup_bounds w n (fun z => sourceResonantBMinusFunction hp η n z-η.fst (-(2*n))) M
    (fun z hz => (hpoint z hz).1)
  have hp' := weightedStripSup_bounds w n (fun z => sourceResonantBPlusFunction hp η n z-η.snd (2*n)) P
    (fun z hz => (hpoint z hz).2)
  refine ⟨⟨M,?_⟩,⟨P,?_⟩,⟨hm.1,hm.2.1⟩,⟨hp'.1,hp'.2.1⟩⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact (hpoint z hz).1
  · rintro _ ⟨z,hz,rfl⟩
    exact (hpoint z hz).2

/-- A genuine nonnegative supremum tail dominated by the literal majorant has a convergent p-power sum. -/
theorem summable_offDiagonalProof_dominated_tail (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (d a : WeightedCoeff w.toWeight p) (N : ℕ) (hN : 0 < N) (S : ℤ → ℝ)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ S n ∧ S n ≤ offDiagonalProofBound hp w d a N n) :
    Summable (sourceCoefficientPowerTail p N S) ∧
    (∑' n : ℤ, sourceCoefficientPowerTail p N S n) ≤ ∑' n : ℤ, (offDiagonalProofBound hp w d a N n)^p.toReal := by
  have hs := (offDiagonalProofBound_summable_and_le hp hp1 w d a N hN).1
  have hnon (n : ℤ) : 0 ≤ sourceCoefficientPowerTail p N S n := by
    unfold sourceCoefficientPowerTail
    split_ifs with hn
    · exact Real.rpow_nonneg (hb n hn).1 _
    · exact le_rfl
  have hdom (n : ℤ) : sourceCoefficientPowerTail p N S n ≤ (offDiagonalProofBound hp w d a N n)^p.toReal := by
    unfold sourceCoefficientPowerTail
    split_ifs with hn
    · exact Real.rpow_le_rpow (hb n hn).1 (hb n hn).2 ENNReal.toReal_nonneg
    · exact Real.rpow_nonneg (offDiagonalProofBound_nonneg hp w d a N n) _
  have hsum := hs.of_nonneg_of_le hnon hdom
  exact ⟨hsum,hsum.tsum_le_tsum hdom hs⟩

/-- Negative majorant budget in the original weighted pair norm with its full Fourier cutoff. -/
theorem offDiagonalProofBound_minus_sum_le_pair (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 0 < N) :
    (∑' n : ℤ, (offDiagonalProofBound hp w (w.reflection φ.fst) φ.snd N n)^p.toReal) ≤
      offDiagonalProofConstant p*‖φ.fst‖^p.toReal*
        (‖φ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight N φ‖^(2*p.toReal)) := by
  have hd : ‖w.reflection φ.fst‖ ≤ ‖φ‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact WithLp.norm_fst_le _ φ
  have htd : ‖WeightedCoeff.fourierTail w.toWeight N (w.reflection φ.fst)‖ ≤ ‖weightedPairFourierTail w.toWeight N φ‖ := by
    rw [w.norm_fourierTail_reflection]
    exact (norm_offDiagonal_componentTails_le_fullCutoff w φ N).1
  simpa only [LinearIsometryEquiv.norm_map] using
    offDiagonalProofBound_sum_le_of_norm_bounds hp hp1 w (w.reflection φ.fst) φ.snd N hN
      ‖φ‖ ‖weightedPairFourierTail w.toWeight N φ‖ (norm_nonneg _) (norm_nonneg _)
      hd (WithLp.norm_snd_le _ φ) htd (norm_offDiagonal_componentTails_le_fullCutoff w φ N).2

/-- Positive majorant budget with the distinguished component exchanged. -/
theorem offDiagonalProofBound_plus_sum_le_pair (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 0 < N) :
    (∑' n : ℤ, (offDiagonalProofBound hp w φ.snd (w.reflection φ.fst) N n)^p.toReal) ≤
      offDiagonalProofConstant p*‖φ.snd‖^p.toReal*
        (‖φ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight N φ‖^(2*p.toReal)) := by
  have ha : ‖w.reflection φ.fst‖ ≤ ‖φ‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact WithLp.norm_fst_le _ φ
  have hta : ‖WeightedCoeff.fourierTail w.toWeight N (w.reflection φ.fst)‖ ≤ ‖weightedPairFourierTail w.toWeight N φ‖ := by
    rw [w.norm_fourierTail_reflection]
    exact (norm_offDiagonal_componentTails_le_fullCutoff w φ N).1
  exact offDiagonalProofBound_sum_le_of_norm_bounds hp hp1 w φ.snd (w.reflection φ.fst) N hN
    ‖φ‖ ‖weightedPairFourierTail w.toWeight N φ‖ (norm_nonneg _) (norm_nonneg _)
    (WithLp.norm_snd_le _ φ) ha (norm_offDiagonal_componentTails_le_fullCutoff w φ N).2 hta
/-- The proof-consistent Lemma 6.8(ii), obtained from its literal regions and actual weighted Holder tests. -/
theorem sourceLemma6_8_offDiagonal_proof (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        let η := sourceWeightedPeriodTwoInput w ψ
        (Summable (sourceCoefficientPowerTail p N (sourceResonantBMinusSup hp w η)) ∧
          (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantBMinusSup hp w η) n) ≤
            offDiagonalProofConstant p*‖ψ.fst‖^p.toReal*
              (‖ψ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) +
                ‖weightedPairFourierTail w.toWeight N ψ‖^(2*p.toReal))) ∧
        (Summable (sourceCoefficientPowerTail p N (sourceResonantBPlusSup hp w η)) ∧
          (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantBPlusSup hp w η) n) ≤
            offDiagonalProofConstant p*‖ψ.snd‖^p.toReal*
              (‖ψ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) +
                ‖weightedPairFourierTail w.toWeight N ψ‖^(2*p.toReal))) := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,hb⟩ := exists_uniform_sourceOffDiagonalProofBound hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ N hN
  obtain ⟨hsm,hm⟩ := summable_offDiagonalProof_dominated_tail hp hp1 w (w.reflection ψ.fst) ψ.snd N
    (by omega) _ (fun n hn => (hb ψ hψ N hN n hn).2.2.1)
  obtain ⟨hsp,hp'⟩ := summable_offDiagonalProof_dominated_tail hp hp1 w ψ.snd (w.reflection ψ.fst) N
    (by omega) _ (fun n hn => (hb ψ hψ N hN n hn).2.2.2)
  exact ⟨⟨hsm,hm.trans (offDiagonalProofBound_minus_sum_le_pair hp hp1 w ψ N (by omega))⟩,
    ⟨hsp,hp'.trans (offDiagonalProofBound_plus_sum_le_pair hp hp1 w ψ N (by omega))⟩⟩

end NLS.ZakharovShabat
