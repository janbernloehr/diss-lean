import NLS.Poisson.GardnerHamiltonianDirection
import NLS.Poisson.HminusGardnerHilbertRestriction

noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.Poisson

theorem gardnerHilbertDerivative_weight_bound (k : ℤ) :
    Weight.sobolev 0 k * ‖(2 * Real.pi : ℂ) * I * k‖ ≤
      (2 * Real.pi) * Weight.sobolev 1 k := by
  simp only [Weight.sobolev_apply,Real.rpow_zero,Real.rpow_one,one_mul,norm_mul,
    norm_I,mul_one,Complex.norm_intCast,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  norm_num
  nlinarith [Real.pi_pos]

/-- The actual unit-period Gardner derivative takes H1 cotangents into
native L2, with its original raw 2*pi*i*k coefficient multiplier. -/
def gardnerHilbertDerivative : WeightedCoeff (Weight.sobolev 1) 2 →L[ℂ] Coeff 2 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev 0) 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (WeightedCoeff.weightedMultiplierCLM _ _ (fun k => (2 * Real.pi : ℂ) * I * k)
      (2 * Real.pi) (by positivity) gardnerHilbertDerivative_weight_bound)

theorem gardnerHilbertDerivative_apply (a : WeightedCoeff (Weight.sobolev 1) 2) (k : ℤ) :
    gardnerHilbertDerivative a k = (2 * Real.pi : ℂ) * I * k * a.val k := by
  change (Weight.sobolev 0 k : ℂ) * ((2 * Real.pi : ℂ) * I * k * a.val k) = _
  rw [Weight.sobolev_zero_apply,ofReal_one,one_mul]

def gardnerHamiltonianHilbertDirection :
    (WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ] Coeff 2 :=
  gardnerHilbertDerivative.comp hminusCotangentCLM

/-- Every actual H-minus-one scalar Hamiltonian vector has a literal
mean-zero native L2 representative, not merely a distributional limit. -/
theorem gardnerHamiltonianHilbertDirection_inclusion
    (L : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    hilbertToHminus (gardnerHamiltonianHilbertDirection L) = gardnerHamiltonianDirection L := by
  apply Subtype.ext
  funext k
  rw [hilbertToHminus_apply]
  change gardnerHilbertDerivative (hminusCotangentCLM L) k = _
  rw [gardnerHilbertDerivative_apply]
  rfl

theorem gardnerHamiltonianHilbertDirection_zero_mode
    (L : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    gardnerHamiltonianHilbertDirection L 0 = 0 := by
  change gardnerHilbertDerivative (hminusCotangentCLM L) 0 = 0
  rw [gardnerHilbertDerivative_apply]
  simp

end NLS.Poisson
