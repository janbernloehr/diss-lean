import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.ShiftedWeight

/-!
# Weighted Hölder multipliers with arbitrary reciprocal symbols

The same conjugate-space symbol acts between weighted `ℓᵖ` and weighted `ℓ¹`.
Its norm controls every shifted scalar norm, independently of the weight.
-/

noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- A conjugate-space Fourier multiplier with output in weighted `ℓ¹`. -/
def holderMultiplier (w : Weight) (b : Coeff q) : WeightedCoeff w p →L[ℂ] WeightedCoeff w 1 :=
  (weightIsometry w 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((Coeff.holderProduct (q := 1)).flip b).comp (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem holderMultiplier_apply (w : Weight) (b : Coeff q) (a : WeightedCoeff w p) (k : ℤ) :
    (holderMultiplier w b a).val k = b k * a.val k := by
  change ((w k : ℂ) * a.val k * b k) / (w k : ℂ) = _
  field_simp [w.complex_ne_zero k]

theorem norm_holderMultiplier_le (w : Weight) (b : Coeff q) (a : WeightedCoeff w p) :
    ‖holderMultiplier w b a‖ ≤ ‖b‖ * ‖a‖ := by
  change ‖(weightIsometry w 1).symm (Coeff.holderProduct (q := 1) (weightIsometry w p a) b)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map, mul_comm] using Coeff.norm_holderProduct_le (q := 1) (weightIsometry w p a) b

theorem holderMultiplier_add (w : Weight) (b c : Coeff q) :
    holderMultiplier (p := p) w (b + c) = holderMultiplier w b + holderMultiplier w c := by
  apply ContinuousLinearMap.ext
  intro a
  apply Subtype.ext
  funext k
  simp only [add_apply, add_val, holderMultiplier_apply, lp.coeFn_add, Pi.add_apply, add_mul]

theorem shiftedNorm_holderMultiplier_le (w : SpectralWeight) (i : ℤ) (b : Coeff q)
    (a : WeightedCoeff w.toWeight p) :
    w.shiftedNorm i (holderMultiplier w.toWeight b a) ≤ ‖b‖ * w.shiftedNorm i a := by
  have he : w.toShift i (holderMultiplier w.toWeight b a) =
      holderMultiplier (w.toWeight.shift i) b (w.toShift i a) := by
    apply Subtype.ext
    funext k
    simp only [SpectralWeight.toShift_apply, holderMultiplier_apply]
  rw [SpectralWeight.shiftedNorm, he]
  exact norm_holderMultiplier_le _ _ _

end NLS.WeightedCoeff
