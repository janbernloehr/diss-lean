import NLS.ZakharovShabat.ExponentInclusions

/-!
# Operator compatibility under an increase of sequence exponent

The convolution formulas identify the actual operators and spectral pencils
under the coefficient-preserving domain and base inclusions.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Potential multiplication commutes with the canonical exponent inclusions. -/
theorem potentialMul_exponentInclusion (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : Coeff p) (a : ScalarDomain p) :
    potentialMul hq (Coeff.exponentInclusion h φ) (WeightedCoeff.exponentInclusion _ h a) =
      Coeff.exponentInclusion h (potentialMul hp φ a) := by
  ext n
  simp only [potentialMul_apply, Coeff.exponentInclusion_apply, WeightedCoeff.exponentInclusion_apply]

/-- The signed free operator has the same Fourier coefficients in both exponents. -/
theorem freeOperator_domainExponentInclusion (h : p ≤ q) (a : Domain p) :
    freeOperator (domainExponentInclusion h a) = pairExponentInclusion h (freeOperator a) := by
  apply Prod.ext <;> ext n <;>
    simp only [freeOperator_fst_apply, freeOperator_snd_apply, pairExponentInclusion_apply,
      domainExponentInclusion_apply, Coeff.exponentInclusion_apply, WeightedCoeff.exponentInclusion_apply]

/-- The full actual operator commutes with the exponent inclusion. -/
theorem operator_domainExponentInclusion (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (a : Domain p) :
    operator hq (pairExponentInclusion h φ) (domainExponentInclusion h a) =
      pairExponentInclusion h (operator hp φ a) := by
  apply Prod.ext <;> ext n <;>
    simp only [operator_fst_apply, operator_snd_apply, pairExponentInclusion_apply,
      domainExponentInclusion_apply, Coeff.exponentInclusion_apply, WeightedCoeff.exponentInclusion_apply]

/-- Spectral-pencil equations are transported without changing the spectral parameter. -/
theorem spectralPencil_domainExponentInclusion (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (z : ℂ) (a : Domain p) :
    spectralPencil hq (pairExponentInclusion h φ) z (domainExponentInclusion h a) =
      pairExponentInclusion h (spectralPencil hp φ z a) := by
  simp only [spectralPencil_apply, domainInclusion_domainExponentInclusion,
    operator_domainExponentInclusion hp hq, map_sub, map_smul]

end NLS.ZakharovShabat
