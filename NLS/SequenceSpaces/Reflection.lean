import NLS.SequenceSpaces.Translation
import NLS.SequenceSpaces.Weighted
import NLS.SequenceSpaces.Convolution

/-!
# Reflection of Fourier coefficients

Frequency reversal is an isometry, including for every real Sobolev weight.
It commutes with convolution when applied to both factors. This is the scalar
reflection used in Chapter 1, §4, equations (1.8)–(1.9); it is unrelated to
restriction to even or odd frequency indices.
-/

open scoped ENNReal
noncomputable section

namespace NLS

@[simp] theorem Weight.sobolev_neg (s : ℝ) (n : ℤ) :
    Weight.sobolev s (-n) = Weight.sobolev s n := by
  simp

namespace Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Frequency reversal, without complex conjugation. -/
def reflection : Coeff p ≃ₗᵢ[ℂ] Coeff p := reindexIsometry (Equiv.neg ℤ)

@[simp] theorem reflection_apply (a : Coeff p) (n : ℤ) :
    reflection a n = a (-n) := rfl

@[simp] theorem reflection_reflection (a : Coeff p) :
    reflection (reflection a) = a := by ext n; simp

@[simp] theorem reflection_symm (a : Coeff p) : reflection.symm a = reflection a := by
  apply reflection.injective
  simp

/-- Reflection reverses both convolution factors. -/
theorem reflection_convolution (a : Coeff p) (b : Coeff 1) :
    reflection (convolution a b) = convolution (reflection a) (reflection b) := by
  ext n
  simp only [reflection_apply, convolution_apply]
  rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => a (-n - k) * b k)]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply]
  rw [show -n - -k = -(n - k) by omega]

end Coeff

namespace WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reflection transported through the even Sobolev weight. -/
def reflection (s : ℝ) :
    WeightedCoeff (Weight.sobolev s) p ≃ₗᵢ[ℂ] WeightedCoeff (Weight.sobolev s) p :=
  ((weightIsometry (Weight.sobolev s) p).trans Coeff.reflection).trans
    (weightIsometry (Weight.sobolev s) p).symm

@[simp] theorem reflection_apply (s : ℝ) (a : WeightedCoeff (Weight.sobolev s) p)
    (n : ℤ) : (reflection s a).val n = a.val (-n) := by
  change ((Weight.sobolev s (-n) : ℂ) * a.val (-n)) / (Weight.sobolev s n : ℂ) = _
  rw [Weight.sobolev_neg]
  exact mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)

@[simp] theorem reflection_reflection (s : ℝ) (a : WeightedCoeff (Weight.sobolev s) p) :
    reflection s (reflection s a) = a := by
  apply Subtype.ext
  funext n
  simp

@[simp] theorem reflection_symm (s : ℝ) (a : WeightedCoeff (Weight.sobolev s) p) :
    (reflection s).symm a = reflection s a := by
  apply (reflection s).injective
  simp

end WeightedCoeff
end NLS
