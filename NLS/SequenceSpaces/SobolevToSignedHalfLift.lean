import NLS.SequenceSpaces.SignedOrderHalfFourierEquiv
import NLS.SequenceSpaces.SignedSobolevPositiveEquivalence

/-! The exact inverse native signed minus-half weight sends an ordinary
Sobolev sequence of order s to the native signed order s-1/2. All raw
coefficients retain the same square-root multiplier. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

theorem sobolevToSignedHalfLift_bound (s t : ℝ) (hs : 0 ≤ s) (hst : s = t + 1/2) (k : ℤ) :
    Weight.signedSobolev t k * ‖(Weight.signedSobolev (-1/2) k : ℂ)⁻¹‖ ≤
      Weight.sobolev s k := by
  simp only [norm_inv, norm_real, Real.norm_eq_abs,
    Weight.signedSobolev_neg_half, one_div, inv_inv,
    abs_of_nonneg (Real.sqrt_nonneg (max 1 |(k : ℝ)|))]
  have he := Weight.signedSobolev_add_half t k
  rw [← hst] at he
  rw [mul_comm, ← he]
  exact Weight.signedSobolev_le_sobolev s hs k

def sobolevToSignedHalfLift (s t : ℝ) (hs : 0 ≤ s) (hst : s = t + 1/2)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WeightedCoeff (Weight.sobolev s) p →L[ℂ] WeightedCoeff (Weight.signedSobolev t) p :=
  weightedMultiplierCLM _ _ (fun k => (Weight.signedSobolev (-1/2) k : ℂ)⁻¹) 1 zero_le_one
    (by intro k; simpa only [one_mul] using sobolevToSignedHalfLift_bound s t hs hst k)

theorem sobolevToSignedHalfLift_apply (s t : ℝ) (hs : 0 ≤ s) (hst : s = t + 1/2)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : WeightedCoeff (Weight.sobolev s) p) (k : ℤ) :
    (sobolevToSignedHalfLift s t hs hst p a).val k =
      (Weight.signedSobolev (-1/2) k : ℂ)⁻¹ * a.val k := rfl

end NLS.WeightedCoeff
