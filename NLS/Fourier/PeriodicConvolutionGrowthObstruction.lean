import NLS.Fourier.PeriodicDistributionConvolutionProduct
import NLS.Fourier.SparseConvolutionGrowth

/-! # Actual distributions whose convergent convolution is not a distribution

Both inputs are continuous functionals on the original smooth periodic
test space, at every positive physical period. Every convolution sum
has finite support. Its superpolynomial output prevents any original
product, for both unordered and symmetric summation.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.Fourier
open SmoothPeriodicTest
namespace SmoothPeriodicTest.Distribution
variable {L : ℝ} [Fact (0 < L)]

def sparseConvolutionLeftDistribution : Distribution L :=
  Classical.choose (existsUnique_of_polynomial_isBigO (L := L) sparseConvolutionLeft 1
    sparseConvolution_inputs_polynomial.1)

def sparseConvolutionRightDistribution : Distribution L :=
  Classical.choose (existsUnique_of_polynomial_isBigO (L := L) sparseConvolutionRight 0
    sparseConvolution_inputs_polynomial.2)

@[simp] theorem sparseConvolutionLeftDistribution_coefficient (n : ℤ) :
    sparseConvolutionLeftDistribution (L := L) (mode (-n)) = sparseConvolutionLeft n :=
  (Classical.choose_spec (existsUnique_of_polynomial_isBigO (L := L) sparseConvolutionLeft 1
    sparseConvolution_inputs_polynomial.1)).1 n

@[simp] theorem sparseConvolutionRightDistribution_coefficient (n : ℤ) :
    sparseConvolutionRightDistribution (L := L) (mode (-n)) = sparseConvolutionRight n :=
  (Classical.choose_spec (existsUnique_of_polynomial_isBigO (L := L) sparseConvolutionRight 0
    sparseConvolution_inputs_polynomial.2)).1 n

/-- Every original convolution is genuinely a finite sum. -/
theorem finite_support_original_sparseConvolution (n : ℤ) :
    (Function.support (fun k : ℤ =>
      sparseConvolutionLeftDistribution (L := L) (mode (-(n-k)))*
        sparseConvolutionRightDistribution (L := L) (mode (-k)))).Finite := by
  simpa only [sparseConvolutionLeftDistribution_coefficient,sparseConvolutionRightDistribution_coefficient]
    using finite_support_sparseConvolution n

theorem hasSum_original_sparseConvolution (n : ℤ) :
    HasSum (fun k : ℤ => sparseConvolutionLeftDistribution (L := L) (mode (-(n-k)))*
      sparseConvolutionRightDistribution (L := L) (mode (-k))) (sparseConvolutionValue n) := by
  simpa only [sparseConvolutionLeftDistribution_coefficient,sparseConvolutionRightDistribution_coefficient,
    sparseConvolutionValue] using (summable_sparseConvolution n).hasSum

/-- The actual convergent output cannot be the Fourier coefficients of any distribution. -/
theorem no_distribution_with_sparseConvolution_coefficients :
    ¬ ∃ w : Distribution L, ∀ n : ℤ, w (mode (-n)) = sparseConvolutionValue n := by
  rintro ⟨w,hw⟩
  apply not_polynomial_sparseConvolution w.order
  simpa only [hw] using w.coefficients_isBigO

/-- The polynomial-growth condition cannot be dropped from the unordered criterion. -/
theorem not_hasFourierProduct_sparseConvolution (w : Distribution L) :
    ¬ HasFourierProduct sparseConvolutionLeftDistribution sparseConvolutionRightDistribution w := by
  intro hw
  apply no_distribution_with_sparseConvolution_coefficients (L := L)
  exact ⟨w,fun n => (hw n).unique (hasSum_original_sparseConvolution (L := L) n)⟩

/-- Nor can it be dropped when convergence is interpreted as symmetric cutoffs. -/
theorem not_hasSymmetricFourierProduct_sparseConvolution (w : Distribution L) :
    ¬ HasSymmetricFourierProduct sparseConvolutionLeftDistribution sparseConvolutionRightDistribution w := by
  intro hw
  apply no_distribution_with_sparseConvolution_coefficients (L := L)
  exact ⟨w,fun n => tendsto_nhds_unique (hw n)
    ((hasSum_original_sparseConvolution (L := L) n).comp Finset.tendsto_Icc_neg)⟩

end SmoothPeriodicTest.Distribution
end NLS.Fourier
