import NLS.SequenceSpaces.IteratedConvolutionRows
import NLS.SequenceSpaces.ConvolutionRowTails

/-!
# The three-region split for iterated convolution rows

The two reciprocal tails and the near-near potential tail give three genuine
outer `lp` majorants. Near windows use `N/2` and retain the potential tail at `N`.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- The first kernel enters linearly after taking the inner row norm. -/
theorem iteratedConvolutionRow_add_left (a : Coeff p) (b b' c : Coeff r) (m : ℤ) :
    iteratedConvolutionRow a (b+b') c m = iteratedConvolutionRow a b c m + iteratedConvolutionRow a b' c m := by
  ext j
  simp [mul_add]

/-- Splitting the inner kernel gives a triangle inequality for the entire nested norm. -/
theorem norm_iteratedConvolutionRow_add_right_le (a : Coeff p) (b c c' : Coeff r) (m : ℤ) :
    ‖iteratedConvolutionRow a b (c+c') m‖ ≤
      ‖iteratedConvolutionRow a b c m‖ + ‖iteratedConvolutionRow a b c' m‖ := by
  have hrow (t : ℤ) : convolutionRow a (c+c') t = convolutionRow a c t + convolutionRow a c' t := by
    ext k
    simp [mul_add]
  apply le_trans _ (norm_add_le (iteratedConvolutionRow a b c m) (iteratedConvolutionRow a b c' m))
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ r)).ne'
  intro j
  simp only [iteratedConvolutionRow_apply, lp.coeFn_add, Pi.add_apply, ← add_mul,
    ← Complex.ofReal_add, norm_mul, Complex.norm_real, norm_norm,
    Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [hrow]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)

/-- Truncating the first kernel cannot increase a nested row norm. -/
theorem norm_iteratedConvolutionRow_truncate_left_le (a : Coeff p) (b c : Coeff r) (S : Finset ℤ) (m : ℤ) :
    ‖iteratedConvolutionRow a (truncate S b) c m‖ ≤ ‖iteratedConvolutionRow a b c m‖ :=
  norm_convolutionRow_truncate_le (convolutionRowNormBounded a c) b S m

/-- Truncating the second kernel cannot increase a nested row norm. -/
theorem norm_iteratedConvolutionRow_truncate_right_le (a : Coeff p) (b c : Coeff r) (S : Finset ℤ) (m : ℤ) :
    ‖iteratedConvolutionRow a b (truncate S c) m‖ ≤ ‖iteratedConvolutionRow a b c m‖ := by
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ r)).ne'
  intro j
  simp only [iteratedConvolutionRow_apply, norm_mul, Complex.norm_real, norm_norm]
  exact mul_le_mul_of_nonneg_right (norm_convolutionRow_truncate_le a c S (m-j)) (norm_nonneg _)

/-- When both kernels are near zero, every surviving potential coefficient lies in the distant tail. -/
theorem iteratedConvolutionRow_near_eq_tail (a : Coeff p) (b c : Coeff r) (N : ℕ)
    (n : ℤ) (hn : N ≤ n.natAbs) :
    iteratedConvolutionRow a (truncate (lowFrequencies (N/2)) b) (truncate (lowFrequencies (N/2)) c) (2*n) =
      iteratedConvolutionRow (fourierTail N a) (truncate (lowFrequencies (N/2)) b)
        (truncate (lowFrequencies (N/2)) c) (2*n) := by
  ext j
  simp only [iteratedConvolutionRow_apply]
  by_cases hj : j ∈ lowFrequencies (N/2)
  · have he : convolutionRow a (truncate (lowFrequencies (N/2)) c) (2*n-j) =
        convolutionRow (fourierTail N a) (truncate (lowFrequencies (N/2)) c) (2*n-j) := by
      ext k
      by_cases hk : k ∈ lowFrequencies (N/2)
      · have h : N ≤ (2*n-j-k).natAbs := by
          simp only [mem_lowFrequencies] at hj hk
          omega
        simp only [convolutionRow_apply, fourierTail_apply, if_pos h]
      · simp [hk]
    rw [he]
  · simp [hj]

/-- The source's three regions bound the nested row at every distant signed frequency. -/
theorem norm_iteratedConvolutionRow_tail_le (a : Coeff p) (b c : Coeff r) (N : ℕ)
    (n : ℤ) (hn : N ≤ n.natAbs) :
    ‖iteratedConvolutionRow a b c (2*n)‖ ≤
      ‖iteratedConvolutionRow a (fourierTail (N/2) b) c (2*n)‖ +
      ‖iteratedConvolutionRow a b (fourierTail (N/2) c) (2*n)‖ +
      ‖iteratedConvolutionRow (fourierTail N a) b c (2*n)‖ := by
  let S := lowFrequencies (N/2)
  have hb : b = fourierTail (N/2) b + truncate S b := by dsimp [fourierTail]; abel
  have hc : c = fourierTail (N/2) c + truncate S c := by dsimp [fourierTail]; abel
  calc
    _ ≤ ‖iteratedConvolutionRow a (fourierTail (N/2) b) c (2*n)‖ +
        ‖iteratedConvolutionRow a (truncate S b) c (2*n)‖ := by
      conv_lhs => rw [hb, iteratedConvolutionRow_add_left]
      exact norm_add_le _ _
    _ ≤ ‖iteratedConvolutionRow a (fourierTail (N/2) b) c (2*n)‖ +
        (‖iteratedConvolutionRow a (truncate S b) (fourierTail (N/2) c) (2*n)‖ +
          ‖iteratedConvolutionRow a (truncate S b) (truncate S c) (2*n)‖) := by
      apply add_le_add le_rfl
      conv_lhs => rw [hc]
      exact norm_iteratedConvolutionRow_add_right_le a _ _ _ _
    _ = ‖iteratedConvolutionRow a (fourierTail (N/2) b) c (2*n)‖ +
        ‖iteratedConvolutionRow a (truncate S b) (fourierTail (N/2) c) (2*n)‖ +
        ‖iteratedConvolutionRow (fourierTail N a) (truncate S b) (truncate S c) (2*n)‖ := by
      rw [iteratedConvolutionRow_near_eq_tail a b c N n hn, add_assoc]
    _ ≤ _ := add_le_add
      (add_le_add le_rfl (norm_iteratedConvolutionRow_truncate_left_le (p := p) (r := r)
        a b (fourierTail (N/2) c) S (2*n)))
      ((norm_iteratedConvolutionRow_truncate_left_le (p := p) (r := r)
        (fourierTail N a) b (truncate S c) S (2*n)).trans
        (norm_iteratedConvolutionRow_truncate_right_le (p := p) (r := r)
          (fourierTail N a) b c S (2*n)))

end NLS.Coeff
