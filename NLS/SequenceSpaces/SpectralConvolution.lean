import NLS.SequenceSpaces.ShiftedWeight
import NLS.SequenceSpaces.Convolution

/-!
# Weighted convolution for the Section 6 weight class

The Banach-space series of weighted translations proves the exact Young bound
`ℓᵖ_w × ℓ¹_w → ℓᵖ_w`, including infinity. Forgetting the weight gives the
existing convolution, so this is the same coefficient product.
-/

noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted `ℓ¹` norm is the sum of the weighted coefficient magnitudes. -/
theorem hasSum_weighted_norm (w : SpectralWeight) (b : WeightedCoeff w.toWeight 1) :
    HasSum (fun k => w k * ‖b.val k‖) ‖b‖ := by
  have h := lp.hasSum_norm (p := 1) (by simp) (WeightedCoeff.weightEquiv w.toWeight 1 b)
  simpa only [WeightedCoeff.weightEquiv_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (w.positive _), ENNReal.toReal_one, Real.rpow_one, ← WeightedCoeff.norm_eq] using h

theorem summable_norm_convolution_terms (w : SpectralWeight)
    (a : WeightedCoeff w.toWeight p) (b : WeightedCoeff w.toWeight 1) :
    Summable (fun k : ℤ => ‖b.val k • w.modulation k a‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => ?_) ((w.hasSum_weighted_norm b).summable.mul_right ‖a‖)
  rw [norm_smul]
  calc
    _ ≤ ‖b.val k‖ * (w k * ‖a‖) := mul_le_mul_of_nonneg_left (w.norm_modulation_le k a) (norm_nonneg _)
    _ = _ := by ring

theorem summable_convolution_terms (w : SpectralWeight)
    (a : WeightedCoeff w.toWeight p) (b : WeightedCoeff w.toWeight 1) :
    Summable (fun k : ℤ => b.val k • w.modulation k a) :=
  (w.summable_norm_convolution_terms a b).of_norm

/-- Weighted convolution as an absolutely convergent series in the weighted Banach space. -/
def convolution (w : SpectralWeight) (a : WeightedCoeff w.toWeight p)
    (b : WeightedCoeff w.toWeight 1) : WeightedCoeff w.toWeight p :=
  ∑' k : ℤ, b.val k • w.modulation k a

/-- This weighted construction agrees with ordinary convolution of raw coefficients. -/
theorem toCoeff_convolution (w : SpectralWeight) (a : WeightedCoeff w.toWeight p)
    (b : WeightedCoeff w.toWeight 1) :
    w.toCoeff (w.convolution a b) = Coeff.convolution (w.toCoeff a) (w.toCoeff b) := by
  rw [convolution, ContinuousLinearMap.map_tsum _ (w.summable_convolution_terms a b)]
  unfold Coeff.convolution
  apply tsum_congr
  intro k
  rw [map_smul, toCoeff_modulation, toCoeff_apply]

@[simp] theorem convolution_apply (w : SpectralWeight) (a : WeightedCoeff w.toWeight p)
    (b : WeightedCoeff w.toWeight 1) (n : ℤ) :
    (w.convolution a b).val n = ∑' k : ℤ, a.val (n - k) * b.val k := by
  rw [← toCoeff_apply, toCoeff_convolution, Coeff.convolution_apply]
  simp only [toCoeff_apply]

/-- The exact weighted Young constant is one, also when the first exponent is infinity. -/
theorem norm_convolution_le (w : SpectralWeight) (a : WeightedCoeff w.toWeight p)
    (b : WeightedCoeff w.toWeight 1) : ‖w.convolution a b‖ ≤ ‖a‖ * ‖b‖ := by
  calc
    _ ≤ ∑' k : ℤ, ‖b.val k • w.modulation k a‖ := norm_tsum_le_tsum_norm (w.summable_norm_convolution_terms a b)
    _ ≤ ∑' k : ℤ, (w k * ‖b.val k‖) * ‖a‖ := by
      apply Summable.tsum_le_tsum _ (w.summable_norm_convolution_terms a b)
        ((w.hasSum_weighted_norm b).summable.mul_right ‖a‖)
      intro k
      rw [norm_smul]
      calc
        _ ≤ ‖b.val k‖ * (w k * ‖a‖) := mul_le_mul_of_nonneg_left (w.norm_modulation_le k a) (norm_nonneg _)
        _ = _ := by ring
    _ = ‖a‖ * ‖b‖ := by rw [tsum_mul_right, (w.hasSum_weighted_norm b).tsum_eq, mul_comm]

theorem convolution_add_left (w : SpectralWeight) (a a' : WeightedCoeff w.toWeight p)
    (b : WeightedCoeff w.toWeight 1) : w.convolution (a + a') b = w.convolution a b + w.convolution a' b := by
  simp only [convolution, map_add, smul_add]
  exact (w.summable_convolution_terms a b).tsum_add (w.summable_convolution_terms a' b)

theorem convolution_add_right (w : SpectralWeight) (a : WeightedCoeff w.toWeight p)
    (b b' : WeightedCoeff w.toWeight 1) : w.convolution a (b + b') = w.convolution a b + w.convolution a b' := by
  simp only [convolution, WeightedCoeff.add_val, add_smul]
  exact (w.summable_convolution_terms a b).tsum_add (w.summable_convolution_terms a b')

theorem convolution_smul_left (w : SpectralWeight) (c : ℂ) (a : WeightedCoeff w.toWeight p)
    (b : WeightedCoeff w.toWeight 1) : w.convolution (c • a) b = c • w.convolution a b := by
  simp only [convolution, map_smul, smul_comm (b.val _) c]
  exact (w.summable_convolution_terms a b).tsum_const_smul c

theorem convolution_smul_right (w : SpectralWeight) (c : ℂ) (a : WeightedCoeff w.toWeight p)
    (b : WeightedCoeff w.toWeight 1) : w.convolution a (c • b) = c • w.convolution a b := by
  simp only [convolution, WeightedCoeff.smul_val, mul_smul]
  exact (w.summable_convolution_terms a b).tsum_const_smul c

/-- Weighted multiplication is a bounded complex bilinear map. -/
def convolutionCLM (w : SpectralWeight) :
    WeightedCoeff w.toWeight p →L[ℂ] WeightedCoeff w.toWeight 1 →L[ℂ] WeightedCoeff w.toWeight p :=
  (LinearMap.mk₂ ℂ (w.convolution (p := p)) w.convolution_add_left w.convolution_smul_left
    w.convolution_add_right w.convolution_smul_right).mkContinuous₂ 1
      (fun a b => by simpa only [one_mul, LinearMap.mk₂_apply] using w.norm_convolution_le a b)

@[simp] theorem convolutionCLM_apply (w : SpectralWeight) (a : WeightedCoeff w.toWeight p)
    (b : WeightedCoeff w.toWeight 1) : w.convolutionCLM a b = w.convolution a b := rfl

/-- Modulation of the product may be assigned entirely to the second factor. -/
theorem modulation_convolution (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff w.toWeight p)
    (b : WeightedCoeff w.toWeight 1) :
    w.modulation i (w.convolution a b) = w.convolution a (w.modulation i b) := by
  apply Subtype.ext
  funext n
  simp only [modulation_apply, convolution_apply]
  rw [← (Equiv.addRight i).tsum_eq (fun k : ℤ => a.val (n - k) * b.val (k - i))]
  apply tsum_congr
  intro k
  change a.val (n - i - k) * b.val k = a.val (n - (k + i)) * b.val (k + i - i)
  rw [add_sub_cancel_right]
  rw [show n - i - k = n - (k + i) by omega]

/-- The shifted product estimate with its shift on the `ℓ¹` factor. -/
theorem shiftedNorm_convolution_le (w : SpectralWeight) (i : ℤ)
    (a : WeightedCoeff w.toWeight p) (b : WeightedCoeff w.toWeight 1) :
    w.shiftedNorm i (w.convolution a b) ≤ ‖a‖ * w.shiftedNorm i b := by
  rw [← norm_modulation, modulation_convolution, ← norm_modulation]
  exact w.norm_convolution_le a (w.modulation i b)

end NLS.SpectralWeight
