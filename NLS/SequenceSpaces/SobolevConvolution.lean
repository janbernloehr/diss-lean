import NLS.SequenceSpaces.YoungConvolution
import NLS.SequenceSpaces.SobolevDerivative

/-! # Convolution preserves one Fourier derivative

Two one-derivative coefficient sequences have a one-derivative convolution.
The Leibniz identity is proved for the absolutely convergent coefficient sums.
This supplies the regularity needed for the original spectral equation.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The coefficientwise Leibniz identity, with every derivative term in `ℓᵖ`. -/
theorem sobolev_convolution_derivative_coeff (hp : p ≠ ⊤) (a b : ScalarDomain p) (n : ℤ) :
    Complex.I*(Real.pi:ℂ)*n*Coeff.convolution (scalarInclusion a) (WeightedCoeff.sobolevToL1CLM p hp b) n =
      (Coeff.convolution (derivative a) (WeightedCoeff.sobolevToL1CLM p hp b) +
        Coeff.youngConvolution (show YoungRelation 1 p p by simp [YoungRelation])
          (WeightedCoeff.sobolevToL1CLM p hp a) (derivative b)) n := by
  have hY : YoungRelation p 1 p := by simp [YoungRelation, add_comm]
  have h₁ := (Coeff.summable_norm_youngConvolution_terms hY (derivative a)
    (WeightedCoeff.sobolevToL1CLM p hp b) n).of_norm
  have h₂ := (Coeff.summable_norm_youngConvolution_terms hY.symm
    (WeightedCoeff.sobolevToL1CLM p hp a) (derivative b) n).of_norm
  simp only [Coeff.convolution_apply, Coeff.youngConvolution_apply, lp.coeFn_add, Pi.add_apply,
    scalarInclusion_apply, WeightedCoeff.sobolevToL1CLM_apply, derivative_apply] at h₁ h₂ ⊢
  rw [← h₁.tsum_add h₂, ← tsum_mul_left]
  apply tsum_congr
  intro k
  push_cast
  ring

/-- The actual convolution belongs to the one-derivative space. -/
theorem memlp_sobolev_convolution (hp : p ≠ ⊤) (a b : ScalarDomain p) :
    Memℓp (fun n => (Weight.sobolev 1 n:ℂ)*
      Coeff.convolution (scalarInclusion a) (WeightedCoeff.sobolevToL1CLM p hp b) n) p := by
  apply memlp_sobolev_weight_of_derivative (lp.memℓp _)
  simp only [sobolev_convolution_derivative_coeff hp a b]
  exact lp.memℓp _

/-- Convolution of one-derivative sequences, with unchanged physical coefficients. -/
def sobolevConvolution (hp : p ≠ ⊤) (a b : ScalarDomain p) : ScalarDomain p :=
  ⟨fun n => Coeff.convolution (scalarInclusion a) (WeightedCoeff.sobolevToL1CLM p hp b) n,
    memlp_sobolev_convolution hp a b⟩

@[simp] theorem sobolevConvolution_apply (hp : p ≠ ⊤) (a b : ScalarDomain p) (n : ℤ) :
    (sobolevConvolution hp a b).val n = ∑' k : ℤ, a.val (n-k)*b.val k := by
  simp only [sobolevConvolution, Coeff.convolution_apply, scalarInclusion_apply,
    WeightedCoeff.sobolevToL1CLM_apply]

/-- The regular convolution is the existing base-space convolution. -/
theorem scalarInclusion_sobolevConvolution (hp : p ≠ ⊤) (a b : ScalarDomain p) :
    scalarInclusion (sobolevConvolution hp a b) =
      Coeff.convolution (scalarInclusion a) (WeightedCoeff.sobolevToL1CLM p hp b) := by
  ext n
  exact scalarInclusion_apply _ _

/-- The derivative satisfies the Leibniz rule in the actual coefficient space. -/
theorem derivative_sobolevConvolution (hp : p ≠ ⊤) (a b : ScalarDomain p) :
    derivative (sobolevConvolution hp a b) =
      Coeff.convolution (derivative a) (WeightedCoeff.sobolevToL1CLM p hp b) +
        Coeff.youngConvolution (show YoungRelation 1 p p by simp [YoungRelation])
          (WeightedCoeff.sobolevToL1CLM p hp a) (derivative b) := by
  ext n
  exact sobolev_convolution_derivative_coeff hp a b n

end NLS.ZakharovShabat
