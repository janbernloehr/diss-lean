import NLS.ZakharovShabat.SobolevRiccatiClassicalAgreement
import NLS.ZakharovShabat.NLSHamiltonianDiscriminantAsymptotics

/-! # The Hamiltonian phase for nonsmooth Sobolev sources

The finite phase uses the actual Fourier-defined Hamiltonians. It is continuous in the original source and agrees with the smooth physical phase.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The finite Hamiltonian phase on the original, possibly nonsmooth,
Sobolev source. Every Hamiltonian is the actual Fourier-defined one. -/
def sobolevHamiltonianPhase (s N : ℕ) (hNs : N ≤ s) (ab : SobolevSource s) (z : ℂ) : ℂ :=
  -I*z+∑ k : Fin N, I*sobolevNLSHamiltonian s ab (k.val+1) (by omega)/(2*z)^(k.val+1)

theorem continuous_sobolevHamiltonianPhase (s N : ℕ) (hNs : N ≤ s) (z : ℂ) :
    Continuous (fun ab => sobolevHamiltonianPhase s N hNs ab z) := by
  apply continuous_const.add
  apply continuous_finsetSum
  intro k _
  exact (continuous_const.mul (continuous_sobolevNLSHamiltonian s (k.val+1) (by omega))).div_const _

/-- The Sobolev phase agrees exactly with the smooth physical phase. -/
theorem sobolevHamiltonianPhase_eq_classical
    (s N : ℕ) (hNs : N ≤ s) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hca : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hcb : ∀ j, ab.2.val j = periodOneCoefficient b j) (z : ℂ) :
    sobolevHamiltonianPhase s N hNs ab z = nlsHamiltonianPhase a b N z := by
  simp only [sobolevHamiltonianPhase,nlsHamiltonianPhase,Finset.sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [sobolevNLSHamiltonian_eq_classical s ab a b ha hb hpa hpb hca hcb]

end NLS.ZakharovShabat
