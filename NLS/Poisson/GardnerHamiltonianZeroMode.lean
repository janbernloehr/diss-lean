import NLS.Poisson.GardnerHamiltonianDirection

/-! Every actual native Gardner Hamiltonian direction has zero raw
constant Fourier coefficient, independently of its cotangent. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Poisson

theorem gardnerHamiltonianDirection_zero_mode
    (L : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    (gardnerHamiltonianDirection L).val 0=0 := by
  change (gardnerDerivative (hminusCotangentCLM L)).val 0=0
  rw [gardnerDerivative_apply]
  simp

end NLS.Poisson
