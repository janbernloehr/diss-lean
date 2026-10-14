import NLS.SequenceSpaces.YoungConvolution
import NLS.SequenceSpaces.Reflection

/-!
# Transposing a convolution through a conjugate pairing

The absolutely convergent Banach-space convolution series can be paired
term by term. The reflected Young convolution is the exact transposed
row, with no finite-support assumption.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
variable [q.HolderConjugate r]

/-- Transposition preserves the actual infinite sums and all frequency signs. -/
theorem tsum_convolution_transpose (h : YoungRelation p r q)
    (a : Coeff p) (v : Coeff 1) (u : Coeff r) :
    (∑' k : ℤ, u k * convolution a v k) =
      ∑' l : ℤ, youngConvolution h (reflection a) u l * v l := by
  let A := exponentInclusion h.left_le a
  have he : (∑' k : ℤ, u k * convolution a v k) =
      (dualPairing (p := q) (q := r)).flip u (convolution A v) := by
    rw [ContinuousLinearMap.flip_apply, dualPairing_apply]
    apply tsum_congr
    intro k
    simp only [convolution_apply, A, exponentInclusion_apply, mul_comm]
  rw [he]
  unfold convolution
  rw [ContinuousLinearMap.map_tsum _ (summable_convolution_terms A v)]
  apply tsum_congr
  intro l
  rw [map_smul, ContinuousLinearMap.flip_apply, dualPairing_apply,
    youngConvolution_apply]
  change v l * (∑' k : ℤ, A (k-l)*u k) =
    (∑' k : ℤ, reflection a (l-k)*u k) * v l
  rw [mul_comm (v l)]
  congr 1
  apply tsum_congr
  intro k
  simp only [A, exponentInclusion_apply, reflection_apply, neg_sub]

end NLS.Coeff
