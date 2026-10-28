import NLS.ZakharovShabat.ResonantSeriesApproximation
import NLS.ZakharovShabat.OffDiagonalProofBounds

/-! # The remainder after the cubic resonant coefficient

The actual even-vector error retains the norm of the shifted square. The
literal regional Holder estimate then bounds each coefficient after its
leading and cubic terms by that small factor times a summable majorant.
These estimates are ingredients for the unresolved final p.44 sum.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- Retain the small norm of T squared, rather than replacing it by one half. -/
theorem resonantCubic_evenVector_error (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) (j : Fin 2) :
    w.shiftedPairNorm n (weightedResonantEvenVector hp w φ n z hz h j -
      weightedResonantSource hp w φ n j) ≤
      ‖weightedPotentialSquareInShift hp w φ n z hz‖ *
        (2*w.shiftedPairNorm n (weightedResonantSource hp w φ n j)) := by
  rw [weightedResonantEvenVector_sub_source]
  apply (shiftedPairNorm_square_le_opNorm hp w φ n z hz _).trans
  exact mul_le_mul_of_nonneg_left
    (shiftedPairNorm_evenCorrection_le_two hp w φ n z hz h hh _) (norm_nonneg _)

/-- The regional summation preserves any additional factor in the input bound. -/
theorem resonantCubic_scaled_series_bound (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ resonantStrip n) (C : ℝ)
    (hf : w.shiftedNorm n f ≤ C*(2*‖d‖)) :
    w (2*n)*‖∑' l : ℤ, ∑' k : ℤ, d.val (n+l)*a.val (l+k)*
      complementarySymbol n z l*complementarySymbol n z k*f.val k‖ ≤
        C*offDiagonalProofBound hp w d a N n := by
  have hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hbound := norm_tsum_offDiagonal_proof_regions_le hq w d a f N n hn z hz
  rw [(summable_norm_weightedOffDiagonalTerm hq w d a f n z hz).of_norm.tsum_prod,
    tsum_weightedOffDiagonalTerm_eq,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (w.positive _).le,offDiagonalProofFarRow_norm_eq hp hp1] at hbound
  apply hbound.trans
  change _ ≤ C*((2*‖d‖)*(2*‖d‖*offDiagonalProofRowTail hp .farL
    (WeightedCoeff.weightEquiv w.toWeight p a) N n +
      ‖WeightedCoeff.fourierTail w.toWeight N d‖*offDiagonalProofRowTail hp .near
        (WeightedCoeff.weightEquiv w.toWeight p a) N n))
  simp only [offDiagonalProofRowTail,if_pos hn]
  calc
    _ ≤ (C*(2*‖d‖))*
        (‖d‖*(‖offDiagonalProofRow hq .farL (WeightedCoeff.weightEquiv w.toWeight p a) n‖+
          ‖offDiagonalProofRow hq .farL (WeightedCoeff.weightEquiv w.toWeight p a) n‖)+
          ‖WeightedCoeff.fourierTail w.toWeight N d‖*
            ‖offDiagonalProofRow hq .near (WeightedCoeff.weightEquiv w.toWeight p a) n‖) :=
      mul_le_mul_of_nonneg_right hf (by positivity)
    _ = _ := by ring

/-- The full coefficient minus its leading and cubic terms retains an extra square norm. -/
theorem resonantCubic_positive_error (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ resonantStrip n) (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2)
    (Q : ℝ) (hQ : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ Q) :
    w (2*n) * ‖(weightedResonantBPlus hp w φ n z hz h - φ.snd.val (2*n)) -
      resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
        (weightedPotentialInverse hp w φ n z hz (weightedResonantSource hp w φ n 0))) 1‖ ≤
      Q*offDiagonalProofBound hp w φ.snd (w.reflection φ.fst) N n := by
  let f := weightedResonantEvenVector hp w φ n z hz h 0 - weightedResonantSource hp w φ n 0
  have he : (weightedResonantBPlus hp w φ n z hz h - φ.snd.val (2*n)) -
      resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
        (weightedPotentialInverse hp w φ n z hz (weightedResonantSource hp w φ n 0))) 1 =
      resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
        (weightedPotentialInverse hp w φ n z hz f)) 1 := by
    rw [weightedResonantBPlus_remainder]
    simp only [f,map_sub,Pi.sub_apply]
  rw [he]
  have hf := (shiftedNorm_snd_le_pair w n f).trans
    (resonantCubic_evenVector_error hp w φ n z hz h hh 0)
  simp only [shiftedPairNorm_source_zero] at hf
  have hfQ := hf.trans (mul_le_mul_of_nonneg_right hQ (by positivity))
  have ht := resonantCubic_scaled_series_bound hp hp1 w φ.snd (w.reflection φ.fst) f.snd
    N n hn z hz Q hfQ
  have hs : resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
      (weightedPotentialInverse hp w φ n z hz f)) 1 =
      ∑' l : ℤ, ∑' k : ℤ, φ.snd.val (n+l) * φ.fst.val (-(l+k)) *
        complementarySymbol n z l * complementarySymbol n z k * f.snd.val k := by
    rw [resonantCoordinates_one,weightedPotentialInverse_sq_snd_apply, ← (Equiv.neg ℤ).tsum_eq]
    apply tsum_congr
    intro l
    apply tsum_congr
    intro k
    simp only [Equiv.neg_apply,neg_neg,sub_neg_eq_add]
    rw [show -l-k = -(l+k) by ring]
  rw [hs]
  simpa only [SpectralWeight.reflection_apply] using ht

/-- The negative coefficient has the same cubic-remainder estimate with reflected inputs. -/
theorem resonantCubic_negative_error (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ resonantStrip n) (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2)
    (Q : ℝ) (hQ : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ Q) :
    w (2*n) * ‖(weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n))) -
      resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
        (weightedPotentialInverse hp w φ n z hz (weightedResonantSource hp w φ n 1))) 0‖ ≤
      Q*offDiagonalProofBound hp w (w.reflection φ.fst) φ.snd N n := by
  let f := weightedResonantEvenVector hp w φ n z hz h 1 - weightedResonantSource hp w φ n 1
  have he : (weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n))) -
      resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
        (weightedPotentialInverse hp w φ n z hz (weightedResonantSource hp w φ n 1))) 0 =
      resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
        (weightedPotentialInverse hp w φ n z hz f)) 0 := by
    rw [weightedResonantBMinus_remainder]
    simp only [f,map_sub,Pi.sub_apply]
  rw [he]
  have hf := (shiftedNorm_reflected_fst_le_pair w n f).trans
    (resonantCubic_evenVector_error hp w φ n z hz h hh 1)
  simp only [shiftedPairNorm_source_one] at hf
  have hfQ : w.shiftedNorm n (w.reflection f.fst) ≤ Q*(2*‖w.reflection φ.fst‖) := by
    rw [LinearIsometryEquiv.norm_map]
    exact hf.trans (mul_le_mul_of_nonneg_right hQ (by positivity))
  have ht := resonantCubic_scaled_series_bound hp hp1 w (w.reflection φ.fst) φ.snd
    (w.reflection f.fst) N n hn z hz Q hfQ
  have hs : resonantCoordinates w.toWeight n (weightedPotentialInverse hp w φ n z hz
      (weightedPotentialInverse hp w φ n z hz f)) 0 =
      ∑' l : ℤ, ∑' k : ℤ, φ.fst.val (-(n+l)) * φ.snd.val (l+k) *
        complementarySymbol n z l * complementarySymbol n z k * f.fst.val (-k) := by
    rw [resonantCoordinates_zero,weightedPotentialInverse_sq_fst_apply]
    apply tsum_congr
    intro l
    rw [← (Equiv.neg ℤ).tsum_eq]
    apply tsum_congr
    intro k
    simp only [Equiv.neg_apply,neg_neg,sub_neg_eq_add]
    rw [show -n-l = -(n+l) by ring]
  rw [hs]
  simpa only [SpectralWeight.reflection_apply] using ht

/-- A small potential gives a common square bound on every full strip. -/
theorem resonantCubic_square_bound (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤
      2*weightedDoubleConstant (p := p) hp*‖φ‖^2 := by
  have hD := weightedDoubleConstant_nonneg (p := p) hp
  have hpow : 1 ≤ (1+|(n : ℝ)|)^(1/p.toReal) :=
    Real.one_le_rpow (by linarith [abs_nonneg (n : ℝ)]) (by positivity)
  have htail := norm_weightedPairFourierTail_le hp w.toWeight n.natAbs φ
  apply (norm_weightedPotentialSquareInShift_le_source hp w φ n z hz).trans
  calc
    _ ≤ weightedDoubleConstant (p := p) hp*‖φ‖*(‖φ‖+‖φ‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (div_le_self (norm_nonneg _) hpow)
        ((div_le_self (norm_nonneg _) (w.one_le n)).trans htail)
    _ = _ := by ring

end NLS.ZakharovShabat
