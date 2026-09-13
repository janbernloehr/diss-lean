import NLS.ZakharovShabat.ResonantParityExpansion

/-!
# The actual off-diagonal double Fourier series

The two components retain their physical frequency signs. Reindexing uses
only integer equivalences and extracts the scalar factors from each sum.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The first component of the actual second iterate, in physical Fourier indices. -/
theorem weightedPotentialInverse_sq_fst_apply (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (m : ℤ) :
    (weightedPotentialInverse hp w φ n z hz (weightedPotentialInverse hp w φ n z hz f)).fst.val m =
      ∑' l : ℤ, ∑' k : ℤ, φ.fst.val (m-l) * φ.snd.val (l-k) *
        complementarySymbol n z l * complementarySymbol n z (-k) * f.fst.val k := by
  rw [weightedPotentialInverse_fst, SpectralWeight.convolution_apply]
  apply tsum_congr
  intro l
  rw [complementaryScalarL1_apply, weightedPotentialInverse_snd, SpectralWeight.convolution_apply,
    ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [complementaryScalarL1_apply]
  change φ.fst.val (m-l) * (complementarySymbol n z l *
    (φ.snd.val (l-k) * (complementarySymbol n z (-k) * f.fst.val k))) = _
  ring

/-- The second component of the actual second iterate has the opposite physical signs. -/
theorem weightedPotentialInverse_sq_snd_apply (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (m : ℤ) :
    (weightedPotentialInverse hp w φ n z hz (weightedPotentialInverse hp w φ n z hz f)).snd.val m =
      ∑' l : ℤ, ∑' k : ℤ, φ.snd.val (m-l) * φ.fst.val (l-k) *
        complementarySymbol n z (-l) * complementarySymbol n z k * f.snd.val k := by
  rw [weightedPotentialInverse_snd, SpectralWeight.convolution_apply]
  apply tsum_congr
  intro l
  rw [complementaryScalarL1_apply, weightedPotentialInverse_fst, SpectralWeight.convolution_apply,
    ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [complementaryScalarL1_apply]
  change φ.snd.val (m-l) * (complementarySymbol n z (-l) *
    (φ.fst.val (l-k) * (complementarySymbol n z k * f.snd.val k))) = _
  ring

/-- The source negative off-diagonal remainder, with its reflected physical first component. -/
theorem weightedResonantBMinus_remainder_eq_tsum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n)) =
      ∑' l : ℤ, ∑' k : ℤ, φ.fst.val (-(n+l)) * φ.snd.val (l+k) *
        complementarySymbol n z l * complementarySymbol n z k *
        (weightedResonantEvenVector hp w φ n z hz h 1).fst.val (-k) := by
  rw [weightedResonantBMinus_remainder, resonantCoordinates_zero,
    weightedPotentialInverse_sq_fst_apply]
  apply tsum_congr
  intro l
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply, neg_neg, sub_neg_eq_add]
  rw [show -n-l = -(n+l) by ring]

/-- The source positive off-diagonal remainder has the matching reflected inner potential. -/
theorem weightedResonantBPlus_remainder_eq_tsum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedResonantBPlus hp w φ n z hz h - φ.snd.val (2*n) =
      ∑' l : ℤ, ∑' k : ℤ, φ.snd.val (n+l) * φ.fst.val (-(l+k)) *
        complementarySymbol n z l * complementarySymbol n z k *
        (weightedResonantEvenVector hp w φ n z hz h 0).snd.val k := by
  rw [weightedResonantBPlus_remainder, resonantCoordinates_one,
    weightedPotentialInverse_sq_snd_apply, ← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply, neg_neg, sub_neg_eq_add]
  rw [show -l-k = -(l+k) by ring]

end NLS.ZakharovShabat
