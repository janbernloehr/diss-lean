import NLS.ZakharovShabat.SourceSection25Localization
import NLS.ZakharovShabat.SourceLemma6_4
import NLS.ZakharovShabat.LinearWeightCoefficientAnalytic
import NLS.ZakharovShabat.M1ComplexGlobalGapEstimate

/-! # Article Section 3: literal source norms and spectral estimates

All source H^1 norms use the physical frequency 2n*pi, and all endpoint
labels are those of the original periodic operator. Shifted Hilbert spaces
use the physical sign of the two Fourier components from the paper.
-/
noncomputable section
open Set NLS.ZakharovShabat
namespace NLS.Articles.DNLSEstimates

/-- Theorem 5: both canonically indexed eigenvalues obey the explicit radius
at the quadratic threshold; the remaining indexed endpoints are in the
printed central box. `quadraticLocalizationRadius` is the literal displayed
P^2/(1+|n|)+sqrt(2)P/(1+|2n|). -/
theorem theorem_five (a : SobolevSource 1) :
    let ψ := higherSobolevSourceInclusion 1 a
    let P := ‖sourcePiSobolevCoordinates 1 1 le_rfl a‖
    (∀ n : ℤ, 8*P^2 ≤ 1+|(n : ℝ)| →
      ‖canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n-(Real.pi : ℂ)*n‖ ≤
          quadraticLocalizationRadius P n ∧
      ‖canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n-(Real.pi : ℂ)*n‖ ≤
          quadraticLocalizationRadius P n ∧
      quadraticLocalizationRadius P n < Real.pi/5) ∧
    (∀ n : ℤ, 1+|(n : ℝ)| < 8*P^2 →
      canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈ quadraticSpectralBox P ∧
      canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈ quadraticSpectralBox P) :=
  sourceH1_uniform_localization a

/-- Theorem 5 exhausts the entire physical periodic spectrum. -/
theorem theorem_five_spectrum (a : SobolevSource 1) (z : ℂ)
    (hz : z ∈ periodicSpectrum (by simp)
      (periodOnePotential (higherSobolevSourceInclusion 1 a))) :
    z ∈ quadraticSpectralBox ‖sourcePiSobolevCoordinates 1 1 le_rfl a‖ ∨
      ∃ n : ℤ, 8*‖sourcePiSobolevCoordinates 1 1 le_rfl a‖^2 ≤ 1+|(n : ℝ)| ∧
        ‖z-(Real.pi : ℂ)*n‖ ≤
          quadraticLocalizationRadius ‖sourcePiSobolevCoordinates 1 1 le_rfl a‖ n :=
  sourceH1_spectrum_subset a z hz

/-- Lemma 5, including the opposite input/output shifts and the constant two.
The operator is the actual potential times complementary free inverse. -/
theorem lemma_five (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 2)
    (i n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight 2) :
    w.shiftedPairNorm i (weightedPotentialInverse (by norm_num) w φ n z hz f) ≤
      (2*‖φ‖)*w.shiftedPairNorm (-i) f :=
  sourceLemma6_4_two w φ i n z hz f

/-- Lemma 6, at every signed frequency and every point of the full strip.
The norm is the induced shifted operator norm, not an unshifted replacement. -/
theorem lemma_six (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift (by simp) w φ n z hz‖ ≤
      (4/(1+|(n : ℝ)|))*‖φ‖^2 :=
  norm_weightedPotentialSquareInShift_linear w hw φ n z hz

/-- Lemma 7 in the original H^1 source realization. The quadratic threshold
is explicit; no additional qualitative cutoff is assumed. -/
theorem lemma_seven (a : SobolevSource 1) (n : ℤ)
    (hn : 8*‖sourcePiSobolevCoordinates 1 1 le_rfl a‖^2 ≤ 1+|(n : ℝ)|)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    z ∈ periodicSpectrum (by simp) (periodOnePotential (higherSobolevSourceInclusion 1 a)) ↔
      resonantDeterminantExtension (by simp) (SpectralWeight.piSobolev 1 (by norm_num))
        (normalizedWeightedPeriodOne _ (sourcePiSobolevCoordinates 1 1 le_rfl a)) n z = 0 := by
  have h := mem_periodicSpectrum_iff_H1_determinant_zero
    (normalizedWeightedPeriodOne _ (sourcePiSobolevCoordinates 1 1 le_rfl a)) n
    (by simpa only [norm_normalizedWeightedPeriodOne] using hn) z hz
  simpa only [weightedBaseToPair_sourcePiSobolevOne] using h

/-- Lemma 9: analyticity near the entire closed strip and all three uniform
coefficient bounds. The first physical coefficient is sampled at -2n. -/
theorem lemma_nine (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n : ℝ)|) :
    AnalyticOnNhd ℂ (weightedResonantAExtension (by simp) w φ n) (resonantStrip n) ∧
    AnalyticOnNhd ℂ (weightedResonantBPlusExtension (by simp) w φ n) (resonantStrip n) ∧
    AnalyticOnNhd ℂ (weightedResonantBMinusExtension (by simp) w φ n) (resonantStrip n) ∧
    ∀ z ∈ resonantStrip n,
      ‖weightedResonantAExtension (by simp) w φ n z‖ ≤ ‖φ‖^2/(1+|(n : ℝ)|) ∧
      w (2*n)*‖weightedResonantBPlusExtension (by simp) w φ n z-φ.snd.val (2*n)‖ ≤
        (8/(1+|(n : ℝ)|))*‖φ‖^2*‖φ.snd‖ ∧
      w (2*n)*‖weightedResonantBMinusExtension (by simp) w φ n z-φ.fst.val (-(2*n))‖ ≤
        (8/(1+|(n : ℝ)|))*‖φ‖^2*‖φ.fst‖ :=
  linearWeight_resonantCoefficients w hw φ n hn

/-- Lemma 10: the original canonical pair supplies all determinant roots,
with their actual multiplicities and the factor-six separation estimate. -/
theorem lemma_ten (a : SobolevSource 1) (n : ℤ)
    (hn : 8*‖sourcePiSobolevCoordinates 1 1 le_rfl a‖^2 ≤ 1+|(n : ℝ)|) :
    let ψ := higherSobolevSourceInclusion 1 a
    let w := SpectralWeight.piSobolev 1 (by norm_num)
    let φ := normalizedWeightedPeriodOne w (sourcePiSobolevCoordinates 1 1 le_rfl a)
    let x := canonicalPeriodicLeft (by simp) (by norm_num)
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    let y := canonicalPeriodicRight (by simp) (by norm_num)
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    PeriodicEndpointPair (by simp) (periodOnePotential ψ) n x y ∧
    (∀ z ∈ resonantStrip n, resonantDeterminantExtension (by simp) w φ n z = 0 ↔ z = x ∨ z = y) ∧
    (∀ z ∈ resonantStrip n,
      analyticOrderNatAt (resonantDeterminantExtension (by simp) w φ n) z =
        ({x,y} : Multiset ℂ).count z) ∧
    ‖y-x‖^2 ≤ 6*resonantBProductSup (by simp) w φ n :=
  sourceH1_canonical_pair a n hn

/-- Lemma 8: the two correction diagonals coincide for arbitrary complex
potentials. The inverse exists by the explicit quadratic threshold. -/
theorem lemma_eight (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ)
    (hn : 8*‖φ‖^2 ≤ 1+|(n : ℝ)|) (z : ℂ) (hz : z ∈ resonantStrip n) :
    let h : ‖weightedPotentialSquareInShift (by simp) w φ n z hz‖ < 1 :=
      (norm_weightedPotentialSquareInShift_le_half w hw φ n z hz hn).trans_lt (by norm_num)
    weightedCorrectionMatrix (by simp) w φ n z hz h 0 0 =
      weightedCorrectionMatrix (by simp) w φ n z hz h 1 1 :=
  weightedCorrectionMatrix_diagonal_eq (by simp) w φ n z hz
    ((norm_weightedPotentialSquareInShift_le_half w hw φ n z hz hn).trans_lt (by norm_num))

/-- Proposition 11's tail estimate, with absolute convergence and the literal
signed physical Fourier cutoff. Original period-one inputs are embedded by
`normalizedWeightedPeriodOne`, so the period-two cutoff is 2N. -/
theorem proposition_eleven_tail (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2)
    (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N : ℝ)) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num)
        (weightedBaseToPair w φ) heven n‖)^2 else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num)
        (weightedBaseToPair w φ) heven n‖)^2 else 0) ≤
      6*‖weightedPairFourierTail w.toWeight (2*N) φ‖^2 +
        1152/(1+(N : ℝ))*‖φ‖^6 :=
  M1_canonicalGap_tail_summable_and_le w hw φ heven N hN

/-- Proposition 11's global bound on the chosen complex neighborhood of the
real source form, with constant 265*pi^2 and the source's actual gap labels. -/
theorem proposition_eleven_global (ψ : CoeffPair 2)
    (hψ : ψ ∈ sourceSpectralStripNeighborhood (by simp))
    (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2)
    (hφ : weightedBaseToPair w φ = periodOnePotential ψ) :
    Summable (fun n : ℤ =>
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖)^2) ∧
    (∑' n : ℤ, (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖)^2) ≤
      265*Real.pi^2*(w.realExtension (16*‖φ‖^2))^2*(1+‖φ‖^2)*‖φ‖^2 :=
  M1_source_canonicalGap_global_summable_and_le ψ hψ w hw φ hφ

end NLS.Articles.DNLSEstimates
