import NLS.SequenceSpaces.WeightedHilbertProduct
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.WeightedMultiplier

/-! Pointwise products of weighted Hilbert sequences add their Sobolev
orders analytically. This is a coefficient product, with no convolution
or change of Fourier labels. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.WeightedCoeff

private def productToSobolev (s t : ℝ) :
    WeightedCoeff ((Weight.sobolev s).product (Weight.sobolev t)) 2 →L[ℂ]
      WeightedCoeff (Weight.sobolev (s + t)) 2 :=
  inclusionCLM _ _ (by intro k; rw [Weight.product_apply, Weight.sobolev_add])

def sobolevHilbertPointwiseProduct (s t : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) 2) (b : WeightedCoeff (Weight.sobolev t) 2) :
    WeightedCoeff (Weight.sobolev (s + t)) 2 :=
  productToSobolev s t
    (exponentInclusion _ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (hilbertProduct (Weight.sobolev s) (Weight.sobolev t) a b))

theorem sobolevHilbertPointwiseProduct_apply (s t : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) 2) (b : WeightedCoeff (Weight.sobolev t) 2) (k : ℤ) :
    (sobolevHilbertPointwiseProduct s t a b).val k = a.val k * b.val k := by
  simp only [sobolevHilbertPointwiseProduct, productToSobolev, inclusionCLM_apply,
    exponentInclusion_apply, hilbertProduct_apply]

theorem analyticAt_sobolevHilbertPointwiseProduct (s t : ℝ)
    (z : WeightedCoeff (Weight.sobolev s) 2 × WeightedCoeff (Weight.sobolev t) 2) :
    AnalyticAt ℂ (fun y => sobolevHilbertPointwiseProduct s t y.1 y.2) z :=
  ((productToSobolev s t).analyticAt _).comp
    (((exponentInclusion _ (by norm_num : (1 : ℝ≥0∞) ≤ 2)).analyticAt _).comp
      (analyticOnNhd_hilbertProduct _ _ z (mem_univ z)))

end NLS.WeightedCoeff
