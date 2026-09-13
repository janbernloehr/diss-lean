import NLS.SequenceSpaces.ConvolutionRows
import NLS.SequenceSpaces.FourierTail

/-!
# Tail bounds for convolution rows sampled at twice the frequency

For `|n|≥N`, a product at `2n` contains either a kernel frequency of magnitude
at least `N` or a potential frequency of magnitude at least `N`. Powered
Young turns that exact support split into an outer sequence-norm estimate.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

omit [Fact (1 ≤ r)] in
/-- At twice a distant frequency, the low-kernel part only sees the potential tail. -/
theorem convolutionRow_tail_split (a : Coeff p) (b : Coeff r) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs) :
    convolutionRow a b (2*n) = convolutionRow a (fourierTail N b) (2*n) +
      convolutionRow (fourierTail N a) (truncate (lowFrequencies N) b) (2*n) := by
  ext k
  by_cases hk : N ≤ k.natAbs
  · simp [convolutionRow_apply, fourierTail_apply, truncate_apply, mem_lowFrequencies, hk, Nat.not_lt.mpr hk]
  · have ha : N ≤ (2*n-k).natAbs := by omega
    simp [convolutionRow_apply, fourierTail_apply, truncate_apply, mem_lowFrequencies, hk, Nat.lt_of_not_ge hk, ha]

/-- Discarding kernel coefficients can only decrease an individual row norm. -/
theorem norm_convolutionRow_truncate_le (a : Coeff p) (b : Coeff r) (S : Finset ℤ) (m : ℤ) :
    ‖convolutionRow a (truncate S b) m‖ ≤ ‖convolutionRow a b m‖ := by
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ r)).ne'
  intro k
  by_cases hk : k ∈ S
  · simp [convolutionRow_apply, truncate_apply, hk]
  · simp only [convolutionRow_apply, truncate_apply, if_neg hk, mul_zero, norm_zero]
    exact norm_nonneg _

/-- The high-frequency row norm splits into a kernel tail and a potential tail. -/
theorem norm_convolutionRow_tail_le (a : Coeff p) (b : Coeff r) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs) :
    ‖convolutionRow a b (2*n)‖ ≤ ‖convolutionRow a (fourierTail N b) (2*n)‖ +
      ‖convolutionRow (fourierTail N a) b (2*n)‖ := by
  calc
    _ = ‖convolutionRow a (fourierTail N b) (2*n) +
        convolutionRow (fourierTail N a) (truncate (lowFrequencies N) b) (2*n)‖ :=
      congrArg norm (convolutionRow_tail_split a b N n hn)
    _ ≤ ‖convolutionRow a (fourierTail N b) (2*n)‖ +
        ‖convolutionRow (fourierTail N a) (truncate (lowFrequencies N) b) (2*n)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl (norm_convolutionRow_truncate_le (p := p) (r := r)
      (fourierTail N a) b (lowFrequencies N) (2*n))

/-- A genuine outer `ℓ^p` majorant for all distant row norms, with both tails explicit. -/
theorem exists_evenConvolutionRowTailMajorant (hp : p ≠ ⊤) (hrp : r ≤ p)
    (a : Coeff p) (b : Coeff r) (N : ℕ) :
    ∃ d : Coeff p,
      (∀ n : ℤ, N ≤ n.natAbs → ‖convolutionRow a b (2*n)‖ ≤ ‖d n‖) ∧
      ‖d‖ ≤ ‖a‖ * ‖fourierTail N b‖ + ‖fourierTail N a‖ * ‖b‖ := by
  obtain ⟨d₁, h₁, hn₁⟩ := exists_evenConvolutionRowNorm hp hrp a (fourierTail N b)
  obtain ⟨d₂, h₂, hn₂⟩ := exists_evenConvolutionRowNorm hp hrp (fourierTail N a) b
  refine ⟨d₁+d₂, ?_, (norm_add_le _ _).trans (add_le_add hn₁ hn₂)⟩
  intro n hn
  have he : ‖(d₁+d₂) n‖ = ‖convolutionRow a (fourierTail N b) (2*n)‖ +
      ‖convolutionRow (fourierTail N a) b (2*n)‖ := by
    simp only [lp.coeFn_add, Pi.add_apply, h₁, h₂, ← Complex.ofReal_add,
      Complex.norm_real, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [he]
  exact norm_convolutionRow_tail_le a b N n hn

end NLS.Coeff
