import NLS.SequenceSpaces.SpectralConvolution
import NLS.SequenceSpaces.WeightedHolderMultiplier
import NLS.SequenceSpaces.WeightedFourierTail

/-!
# Weighted convolution between two Hölder multipliers

This is the domain-valued inner part of `T_n²`. Its two reciprocal symbols can
be split independently. The resulting algebraic decomposition is valid in the
weighted `ℓ¹` target and respects every scalar shifted norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Convolution between two reciprocal multipliers, with weighted `ℓ¹` output. -/
def sandwich (w : SpectralWeight) (a : Coeff q) (φ : WeightedCoeff w.toWeight p) (b : Coeff q) :
    WeightedCoeff w.toWeight p →L[ℂ] WeightedCoeff w.toWeight 1 :=
  (WeightedCoeff.holderMultiplier w.toWeight a).comp
    ((w.convolutionCLM φ).comp (WeightedCoeff.holderMultiplier w.toWeight b))

@[simp] theorem sandwich_apply (w : SpectralWeight) (a : Coeff q) (φ : WeightedCoeff w.toWeight p)
    (b : Coeff q) (f : WeightedCoeff w.toWeight p) (j : ℤ) :
    (w.sandwich a φ b f).val j = a j * ∑' k : ℤ, φ.val (j-k) * (b k * f.val k) := by
  simp only [sandwich, ContinuousLinearMap.comp_apply, convolutionCLM_apply,
    WeightedCoeff.holderMultiplier_apply, convolution_apply]

theorem shiftedNorm_sandwich_le (w : SpectralWeight) (a : Coeff q) (φ : WeightedCoeff w.toWeight p)
    (b : Coeff q) (i : ℤ) (f : WeightedCoeff w.toWeight p) :
    w.shiftedNorm i (w.sandwich a φ b f) ≤ (‖a‖ * ‖φ‖ * ‖b‖) * w.shiftedNorm i f := by
  calc
    _ ≤ ‖a‖ * w.shiftedNorm i (w.convolution φ (WeightedCoeff.holderMultiplier w.toWeight b f)) :=
      WeightedCoeff.shiftedNorm_holderMultiplier_le _ _ _ _
    _ ≤ ‖a‖ * (‖φ‖ * w.shiftedNorm i (WeightedCoeff.holderMultiplier w.toWeight b f)) :=
      mul_le_mul_of_nonneg_left (w.shiftedNorm_convolution_le i _ _) (norm_nonneg _)
    _ ≤ ‖a‖ * (‖φ‖ * (‖b‖ * w.shiftedNorm i f)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (WeightedCoeff.shiftedNorm_holderMultiplier_le w i b f) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem sandwich_add_left (w : SpectralWeight) (a a' : Coeff q)
    (φ : WeightedCoeff w.toWeight p) (b : Coeff q) :
    w.sandwich (a+a') φ b = w.sandwich a φ b + w.sandwich a' φ b := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  funext j
  simp [add_mul]

theorem sandwich_add_right (w : SpectralWeight) (a : Coeff q)
    (φ : WeightedCoeff w.toWeight p) (b b' : Coeff q) :
    w.sandwich a φ (b+b') = w.sandwich a φ b + w.sandwich a φ b' := by
  simp only [sandwich, WeightedCoeff.holderMultiplier_add, ContinuousLinearMap.comp_add]

/-- If near windows are separated, the inner product sees only the potential tail. -/
theorem sandwich_truncate_eq_tail (w : SpectralWeight) (a : Coeff q)
    (φ : WeightedCoeff w.toWeight p) (b : Coeff q) (A B : Finset ℤ) (N : ℕ)
    (hsep : ∀ j ∈ A, ∀ k ∈ B, N ≤ (j-k).natAbs) :
    w.sandwich (Coeff.truncate A a) φ (Coeff.truncate B b) =
      w.sandwich (Coeff.truncate A a) (WeightedCoeff.fourierTail w.toWeight N φ) (Coeff.truncate B b) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  funext j
  simp only [sandwich_apply]
  by_cases hj : j ∈ A
  · congr 1
    apply tsum_congr
    intro k
    by_cases hk : k ∈ B
    · simp [hk, hsep j hj k hk]
    · simp [hk]
  · simp [hj]

/-- The exact three-term decomposition into far output, far input, and near-near potential tail. -/
theorem sandwich_decomposition (w : SpectralWeight) (a : Coeff q)
    (φ : WeightedCoeff w.toWeight p) (b : Coeff q) (A B : Finset ℤ) (N : ℕ)
    (hsep : ∀ j ∈ A, ∀ k ∈ B, N ≤ (j-k).natAbs) :
    w.sandwich a φ b =
      w.sandwich (a-Coeff.truncate A a) φ b +
      w.sandwich (Coeff.truncate A a) φ (b-Coeff.truncate B b) +
      w.sandwich (Coeff.truncate A a) (WeightedCoeff.fourierTail w.toWeight N φ) (Coeff.truncate B b) := by
  have ha : a = (a-Coeff.truncate A a) + Coeff.truncate A a := by abel
  have hb : b = (b-Coeff.truncate B b) + Coeff.truncate B b := by abel
  calc
    _ = w.sandwich (a-Coeff.truncate A a) φ b + w.sandwich (Coeff.truncate A a) φ b := by
      conv_lhs => rw [ha, sandwich_add_left]
    _ = w.sandwich (a-Coeff.truncate A a) φ b +
        (w.sandwich (Coeff.truncate A a) φ (b-Coeff.truncate B b) +
          w.sandwich (Coeff.truncate A a) φ (Coeff.truncate B b)) := by
      conv_lhs => rhs; rw [hb, sandwich_add_right]
    _ = _ := by rw [sandwich_truncate_eq_tail w a φ b A B N hsep, add_assoc]

/-- A shifted norm obeys the triangle inequality because its shift map is linear. -/
theorem shiftedNorm_add_triangle (w : SpectralWeight) (i : ℤ) (a b : WeightedCoeff w.toWeight p) :
    w.shiftedNorm i (a+b) ≤ w.shiftedNorm i a + w.shiftedNorm i b := by
  unfold shiftedNorm
  rw [map_add]
  exact norm_add_le _ _

/-- General near/far bound, before the extra near-near weight gain is used. -/
theorem shiftedNorm_sandwich_le_split (w : SpectralWeight) (a : Coeff q)
    (φ : WeightedCoeff w.toWeight p) (b : Coeff q) (A B : Finset ℤ) (N : ℕ)
    (hsep : ∀ j ∈ A, ∀ k ∈ B, N ≤ (j-k).natAbs) (i : ℤ) (f : WeightedCoeff w.toWeight p) :
    w.shiftedNorm i (w.sandwich a φ b f) ≤
      (‖a-Coeff.truncate A a‖ * ‖φ‖ * ‖b‖ + ‖a‖ * ‖φ‖ * ‖b-Coeff.truncate B b‖ +
        ‖a‖ * ‖WeightedCoeff.fourierTail w.toWeight N φ‖ * ‖b‖) * w.shiftedNorm i f := by
  rw [sandwich_decomposition w a φ b A B N hsep]
  change w.shiftedNorm i (_ + _ + _) ≤ _
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne'
  have hf0 : 0 ≤ w.shiftedNorm i f := norm_nonneg _
  calc
    _ ≤ w.shiftedNorm i (w.sandwich (a-Coeff.truncate A a) φ b f) +
        w.shiftedNorm i (w.sandwich (Coeff.truncate A a) φ (b-Coeff.truncate B b) f) +
        w.shiftedNorm i (w.sandwich (Coeff.truncate A a) (WeightedCoeff.fourierTail w.toWeight N φ) (Coeff.truncate B b) f) :=
      (w.shiftedNorm_add_triangle i _ _).trans (add_le_add (w.shiftedNorm_add_triangle i _ _) le_rfl)
    _ ≤ _ := by
      rw [add_mul, add_mul]
      apply add_le_add
      · apply add_le_add
        · exact w.shiftedNorm_sandwich_le _ _ _ i f
        · apply (w.shiftedNorm_sandwich_le _ _ _ i f).trans
          gcongr
          exact Coeff.norm_truncate_le hq0 A a
      · apply (w.shiftedNorm_sandwich_le _ _ _ i f).trans
        gcongr
        · exact Coeff.norm_truncate_le hq0 A a
        · exact Coeff.norm_truncate_le hq0 B b

end NLS.SpectralWeight
