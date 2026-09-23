import NLS.SequenceSpaces.FiniteCoefficients
import NLS.SequenceSpaces.PairExponentEmbedding

/-! # Finite Fourier input in the original source pair space -/

noncomputable section
open scoped ENNReal
namespace NLS.CoeffPair
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Finite Fourier pairs with the original source component-sum norm. -/
def ofFinsupp : ((ℤ →₀ ℂ) × (ℤ →₀ ℂ)) →ₗ[ℂ] CoeffPair p :=
  (toMax p).symm.toLinearMap.comp (Coeff.ofFinsupp.prodMap Coeff.ofFinsupp)

@[simp] theorem ofFinsupp_fst (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    (ofFinsupp (p := p) a).fst n = a.1 n := rfl

@[simp] theorem ofFinsupp_snd (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    (ofFinsupp (p := p) a).snd n = a.2 n := rfl

/-- The same finite source input is represented identically at different exponents. -/
@[simp] theorem exponentInclusion_ofFinsupp (h : p ≤ q) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    exponentInclusion h (ofFinsupp (p := p) a) = ofFinsupp (p := q) a := by
  apply (toMax q).injective
  apply Prod.ext <;> ext n <;> rfl

end NLS.CoeffPair
