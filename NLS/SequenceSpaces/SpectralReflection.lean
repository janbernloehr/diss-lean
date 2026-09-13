import NLS.SequenceSpaces.ShiftedWeight
import NLS.SequenceSpaces.Reflection

/-!
# Reflection for the source spectral weights

Symmetry of a spectral weight makes Fourier reflection an exact isometry.
It reverses the shift in the scalar norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reflection in physical Fourier frequency, for every source spectral weight. -/
def reflection (w : SpectralWeight) : WeightedCoeff w.toWeight p ≃ₗᵢ[ℂ] WeightedCoeff w.toWeight p :=
  ((WeightedCoeff.weightIsometry w.toWeight p).trans Coeff.reflection).trans
    (WeightedCoeff.weightIsometry w.toWeight p).symm

@[simp] theorem reflection_apply (w : SpectralWeight) (a : WeightedCoeff w.toWeight p) (k : ℤ) :
    (w.reflection a).val k = a.val (-k) := by
  change (w (-k) : ℂ) * a.val (-k) / (w k : ℂ) = _
  rw [w.apply_neg]
  exact mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero k)

/-- Scalar modulation and reflection exchange the sign of the shift. -/
theorem modulation_reflection (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff w.toWeight p) :
    w.modulation i (w.reflection a) = w.reflection (w.modulation (-i) a) := by
  apply Subtype.ext
  funext k
  simp only [modulation_apply, reflection_apply]
  rw [show -(k-i) = -k-(-i) by ring]

/-- Reflection reverses the source shifted norm without a weight factor. -/
theorem shiftedNorm_reflection (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff w.toWeight p) :
    w.shiftedNorm i (w.reflection a) = w.shiftedNorm (-i) a := by
  rw [← norm_modulation, modulation_reflection, LinearIsometryEquiv.norm_map, norm_modulation]

end NLS.SpectralWeight
