import NLS.ZakharovShabat.WeightedPotentialInverse
import NLS.SequenceSpaces.HolderEmbedding

/-!
# The potential on the weighted derivative domain

One derivative embeds weighted `ℓᵖ` into weighted `ℓ¹` for every finite Banach
exponent. Weighted convolution then realizes the actual off-diagonal potential
as a continuous map from the derivative domain to the base space.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The weight ratio for a single derivative is independent of the spectral weight. -/
theorem oneDerivative_ratio (w : Weight) (k : ℤ) :
    (w k : ℂ) / (w.oneDerivative k : ℂ) = (Weight.sobolev 1 k : ℂ)⁻¹ := by
  simp only [Weight.oneDerivative_apply, Weight.sobolev_apply, Real.rpow_one, Complex.ofReal_mul]
  field_simp [w.complex_ne_zero k]

theorem memlp_oneDerivative_ratio (hp : p ≠ ⊤) (w : Weight) :
    Memℓp (fun k : ℤ => (w k : ℂ) / (w.oneDerivative k : ℂ)) p.conjExponent := by
  simp only [oneDerivative_ratio]
  exact Weight.inverse_sobolev_one_memlp ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)

/-- The coefficient-preserving weighted one-derivative embedding into `ℓ¹`. -/
def weightedDomainScalarL1 (hp : p ≠ ⊤) (w : Weight) :
    WeightedCoeff w.oneDerivative p →L[ℂ] WeightedCoeff w 1 :=
  WeightedCoeff.holderInclusion (r := p.conjExponent) _ _ (memlp_oneDerivative_ratio hp w)

@[simp] theorem weightedDomainScalarL1_apply (hp : p ≠ ⊤) (w : Weight)
    (f : WeightedCoeff w.oneDerivative p) (k : ℤ) :
    (weightedDomainScalarL1 hp w f).val k = f.val k := WeightedCoeff.holderInclusion_apply _ _ _ _ _

/-- The derivative embedding has the same exponent-only constant as the ordinary Sobolev embedding. -/
theorem norm_weightedDomainScalarL1_le (hp : p ≠ ⊤) (w : Weight) (f : WeightedCoeff w.oneDerivative p) :
    ‖weightedDomainScalarL1 hp w f‖ ≤ WeightedCoeff.sobolevEmbeddingConstant p hp * ‖f‖ := by
  have he : WeightedCoeff.weightRatio w.oneDerivative w (memlp_oneDerivative_ratio hp w) =
      WeightedCoeff.inverseWeight (q := p.conjExponent) (Weight.sobolev 1)
        (Weight.inverse_sobolev_one_memlp ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)) := by
    ext k
    exact oneDerivative_ratio w k
  have h := WeightedCoeff.norm_holderInclusion_le (p := p) (r := p.conjExponent) (q := 1)
    w.oneDerivative w (memlp_oneDerivative_ratio hp w) f
  rw [he] at h
  exact h

/-- Multiplication by the off-diagonal weighted potential on the derivative domain. -/
def weightedDomainPotential (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    WeightedDomain w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p :=
  (WeightedCoeffPair.mapComponents w.toWeight.oneDerivative w.toWeight
    ((w.convolutionCLM φ.fst).comp (weightedDomainScalarL1 hp w.toWeight))
    ((w.convolutionCLM φ.snd).comp (weightedDomainScalarL1 hp w.toWeight))).comp
      (LinearIsometryEquiv.withLpProdComm p ℂ (WeightedCoeff w.toWeight.oneDerivative p)
        (WeightedCoeff w.toWeight.oneDerivative p)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem weightedDomainPotential_fst (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (f : WeightedDomain w.toWeight p) (j : ℤ) :
    (weightedDomainPotential hp w φ f).fst.val j = ∑' k : ℤ, φ.fst.val (j-k) * f.snd.val k := by
  change (w.convolution φ.fst (weightedDomainScalarL1 hp w.toWeight f.snd)).val j = _
  simp only [SpectralWeight.convolution_apply, weightedDomainScalarL1_apply]

@[simp] theorem weightedDomainPotential_snd (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (f : WeightedDomain w.toWeight p) (j : ℤ) :
    (weightedDomainPotential hp w φ f).snd.val j = ∑' k : ℤ, φ.snd.val (j-k) * f.fst.val k := by
  change (w.convolution φ.snd (weightedDomainScalarL1 hp w.toWeight f.fst)).val j = _
  simp only [SpectralWeight.convolution_apply, weightedDomainScalarL1_apply]

/-- This is the restriction of the original potential operator, with unchanged Fourier coefficients. -/
theorem weightedDomainPotential_eq_original (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (f : WeightedDomain w.toWeight p) :
    weightedBaseToPair w (weightedDomainPotential hp w φ f) =
      potentialOperator hp (weightedBaseToPair w φ) (weightedDomainToDomain w f) := by
  apply Prod.ext <;> ext k <;>
    simp only [weightedBaseToPair_fst, weightedBaseToPair_snd, weightedDomainPotential_fst,
      weightedDomainPotential_snd, potentialOperator_apply, potentialMul_apply,
      weightedDomainToDomain_fst, weightedDomainToDomain_snd]

/-- Applying the actual domain potential after the complementary inverse gives precisely `T_n`. -/
theorem weightedDomainPotential_complementaryInverse (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    weightedDomainPotential hp w φ (complementaryFreeDomainInverse w.toWeight n z hz f) =
      weightedPotentialInverse hp w φ n z hz f := by
  apply weightedPair_ext <;> intro k <;>
    simp only [weightedDomainPotential_fst, weightedDomainPotential_snd, complementaryFreeDomainInverse_fst,
      complementaryFreeDomainInverse_snd, weightedPotentialInverse_fst, weightedPotentialInverse_snd,
      SpectralWeight.convolution_apply, complementaryScalarL1_apply, freeFrequency_true, freeFrequency_false]

end NLS.ZakharovShabat
