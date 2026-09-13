import NLS.ZakharovShabat.WeightedDoubleRow
import NLS.SequenceSpaces.WeightedFourierTail
import NLS.SequenceSpaces.DoubleSeriesRegions
import NLS.SequenceSpaces.DominatedDoubleTesting

/-!
# Regional weighted Hölder estimates

The disjoint far regions use one reciprocal tail each. In the near region,
both potential factors retain their actual Fourier tails at the output cutoff.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The first far region has one reciprocal-tail factor and full potential norms. -/
theorem norm_offDiagonal_farLeft_le (hq : 1 < q) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (M : ℕ) :
    ‖∑' jk : ℤ × ℤ, Coeff.doubleFarLeft M (fun jk => weightedOffDiagonalTerm w d a f n z jk.1 jk.2) jk‖ ≤
      ‖d‖ * w.shiftedNorm n f * ‖doubleReciprocalFarRow hq (WeightedCoeff.weightEquiv w.toWeight p a) M n‖ := by
  have h := (Coeff.dominated_double_test (WeightedCoeff.weightEquiv w.toWeight p a)
    (w.doubleOuterCoeffs n d) (w.doubleInputCoeffs n f)
    (Coeff.fourierTail M (Coeff.puncturedLattice q hq)) (Coeff.puncturedLattice q hq) (2*n)
    (Coeff.doubleFarLeft M (fun jk => weightedOffDiagonalTerm w d a f n z jk.1 jk.2)) ?_).2
  · simpa only [w.norm_doubleOuterCoeffs, w.norm_doubleInputCoeffs, doubleReciprocalFarRow] using h
  · intro jk
    by_cases hj : M ≤ jk.1.natAbs
    · simp only [Coeff.doubleFarLeft, if_pos hj, Coeff.fourierTail_apply]
      exact norm_weightedOffDiagonalTerm_le hq w d a f n z hz jk.1 jk.2
    · simp only [Coeff.doubleFarLeft, if_neg hj, norm_zero]
      exact norm_nonneg _

/-- The second disjoint far region has the same reciprocal-row bound. -/
theorem norm_offDiagonal_farRight_le (hq : 1 < q) (hqt : q ≠ ⊤) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (M : ℕ) :
    ‖∑' jk : ℤ × ℤ, Coeff.doubleFarRight M (fun jk => weightedOffDiagonalTerm w d a f n z jk.1 jk.2) jk‖ ≤
      ‖d‖ * w.shiftedNorm n f * ‖doubleReciprocalFarRow hq (WeightedCoeff.weightEquiv w.toWeight p a) M n‖ := by
  have h := (Coeff.dominated_double_test (WeightedCoeff.weightEquiv w.toWeight p a)
    (w.doubleOuterCoeffs n d) (w.doubleInputCoeffs n f)
    (Coeff.puncturedLattice q hq) (Coeff.fourierTail M (Coeff.puncturedLattice q hq)) (2*n)
    (Coeff.doubleFarRight M (fun jk => weightedOffDiagonalTerm w d a f n z jk.1 jk.2)) ?_).2
  · rw [w.norm_doubleOuterCoeffs, w.norm_doubleInputCoeffs, doubleReciprocalFarRow_swap hq hqt] at h
    exact h
  · intro jk
    by_cases h : jk.1.natAbs < M ∧ M ≤ jk.2.natAbs
    · simp only [Coeff.doubleFarRight, if_pos h, Coeff.fourierTail_apply, if_pos h.2]
      exact norm_weightedOffDiagonalTerm_le hq w d a f n z hz jk.1 jk.2
    · simp only [Coeff.doubleFarRight, if_neg h, norm_zero]
      exact norm_nonneg _

/-- Two near reciprocal indices force both potential coefficients into their tails. -/
theorem offDiagonal_near_tail_indices (N : ℕ) (n j k : ℤ) (hn : N ≤ n.natAbs)
    (hj : j.natAbs < N/2) (hk : k.natAbs < N/2) :
    N ≤ (2*n-j).natAbs ∧ N ≤ (2*n-j-k).natAbs := by omega

/-- The near region retains both actual potential tails, with no loss from the input shift. -/
theorem norm_offDiagonal_near_le (hq : 1 < q) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖∑' jk : ℤ × ℤ, Coeff.doubleNear (N/2) (fun jk => weightedOffDiagonalTerm w d a f n z jk.1 jk.2) jk‖ ≤
      ‖WeightedCoeff.fourierTail w.toWeight N d‖ * w.shiftedNorm n f *
        ‖doubleReciprocalNearRow hq (WeightedCoeff.weightEquiv w.toWeight p a) N n‖ := by
  have h := (Coeff.dominated_double_test
    (WeightedCoeff.weightEquiv w.toWeight p (WeightedCoeff.fourierTail w.toWeight N a))
    (w.doubleOuterCoeffs n (WeightedCoeff.fourierTail w.toWeight N d)) (w.doubleInputCoeffs n f)
    (Coeff.puncturedLattice q hq) (Coeff.puncturedLattice q hq) (2*n)
    (Coeff.doubleNear (N/2) (fun jk => weightedOffDiagonalTerm w d a f n z jk.1 jk.2)) ?_).2
  · simpa only [w.norm_doubleOuterCoeffs, w.norm_doubleInputCoeffs, WeightedCoeff.weightEquiv_fourierTail,
      doubleReciprocalNearRow, doubleReciprocalRow] using h
  · intro jk
    by_cases hnear : jk.1.natAbs < N/2 ∧ jk.2.natAbs < N/2
    · simp only [Coeff.doubleNear, if_pos hnear]
      obtain ⟨hd, ha⟩ := offDiagonal_near_tail_indices N n jk.1 jk.2 hn hnear.1 hnear.2
      have he : weightedOffDiagonalTerm w d a f n z jk.1 jk.2 =
          weightedOffDiagonalTerm w (WeightedCoeff.fourierTail w.toWeight N d)
            (WeightedCoeff.fourierTail w.toWeight N a) f n z jk.1 jk.2 := by
        simp only [weightedOffDiagonalTerm, WeightedCoeff.fourierTail_apply, if_pos hd, if_pos ha]
      rw [he]
      exact norm_weightedOffDiagonalTerm_le hq w _ _ f n z hz jk.1 jk.2
    · simp only [Coeff.doubleNear, if_neg hnear, norm_zero]
      exact norm_nonneg _

/-- The weighted series has the two far contributions and a product of two potential tails. -/
theorem norm_tsum_offDiagonal_regions_le (hq : 1 < q) (hqt : q ≠ ⊤) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖∑' jk : ℤ × ℤ, weightedOffDiagonalTerm w d a f n z jk.1 jk.2‖ ≤
      w.shiftedNorm n f *
        (2 * ‖d‖ * ‖doubleReciprocalFarRow hq (WeightedCoeff.weightEquiv w.toWeight p a) (N/2) n‖ +
          ‖WeightedCoeff.fourierTail w.toWeight N d‖ *
            ‖doubleReciprocalNearRow hq (WeightedCoeff.weightEquiv w.toWeight p a) N n‖) := by
  apply (Coeff.norm_tsum_double_regions_le (N/2) (summable_norm_weightedOffDiagonalTerm hq w d a f n z hz)).trans
  calc
    _ ≤ (‖d‖ * w.shiftedNorm n f * ‖doubleReciprocalFarRow hq (WeightedCoeff.weightEquiv w.toWeight p a) (N/2) n‖) +
        (‖d‖ * w.shiftedNorm n f * ‖doubleReciprocalFarRow hq (WeightedCoeff.weightEquiv w.toWeight p a) (N/2) n‖) +
        (‖WeightedCoeff.fourierTail w.toWeight N d‖ * w.shiftedNorm n f *
          ‖doubleReciprocalNearRow hq (WeightedCoeff.weightEquiv w.toWeight p a) N n‖) :=
      add_le_add (add_le_add (norm_offDiagonal_farLeft_le hq w d a f n z hz (N/2))
        (norm_offDiagonal_farRight_le hq hqt w d a f n z hz (N/2)))
        (norm_offDiagonal_near_le hq w d a f N n hn z hz)
    _ = _ := by ring

end NLS.ZakharovShabat
