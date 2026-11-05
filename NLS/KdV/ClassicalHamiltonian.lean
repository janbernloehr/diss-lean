import NLS.KdV.PeriodOneHamiltonianGradient

/-! The classical physical energy used to identify the scalar Hill/Miura
trace normalization. Integration is over the ORIGINAL unit period. -/
noncomputable section
open Complex NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

def classicalKdVHamiltonian (q : ℝ → ℂ) : ℂ :=
  ∫ x in (0:ℝ)..1, (1/2:ℂ)*(deriv q x)^2+(q x)^3

theorem periodOneKdVHamiltonian_eq_classical (q : ScalarDomain 2) :
    periodOneKdVHamiltonian q=classicalKdVHamiltonian
      (fun x : ℝ => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ))) :=
  periodOneKdVHamiltonian_eq_integral q

end NLS.KdV
