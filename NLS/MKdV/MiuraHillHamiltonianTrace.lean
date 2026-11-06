import NLS.MKdV.MiuraHillPhysicalTraceComparison
import NLS.MKdV.NativeMiuraHillHamiltonian
import NLS.MKdV.PhysicalHillDiscriminant
import NLS.MKdV.QuasiHillZSComparison
import NLS.ZakharovShabat.NLSHamiltonianDiscriminantAsymptotics

/-! # All-order scalar Hill trace calibration of the Miura Hamiltonians

The literal physical Hill discriminant, constructed from its position/
derivative IVPs, has the odd phase coefficients 2*K_m. This is an actual
spectral trace estimate; it does not yet identify a chosen primitive sheet
or its gap/action labels.
-/
noncomputable section
open Complex NLS.LinearVolterra NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.MKdV

def miuraHillHamiltonianPhase (f : ℝ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  -I*z+∑ j ∈ Finset.range N, I*(2*classicalMiuraHillHamiltonian f (j+1))/(2*z)^(2*j+1)

theorem nlsHamiltonianPhase_diagonal_eq_miura (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (N : ℕ) (z : ℂ) :
    nlsHamiltonianPhase f f (2*N) z = miuraHillHamiltonianPhase f N z := by
  induction N with
  | zero => simp [nlsHamiltonianPhase,miuraHillHamiltonianPhase]
  | succ N ih =>
    simp only [nlsHamiltonianPhase,miuraHillHamiltonianPhase] at ih ⊢
    rw [show 2*(N+1) = (2*N+1)+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,
      Finset.sum_range_succ,classicalNLSHamiltonian_odd_diagonal_eq_miuraHill f hf hp,
      show 2*N+1+1 = 2*N+2 by omega,classicalNLSHamiltonian_even_diagonal_eq_zero f hf hp]
    simp only [mul_zero,zero_div,add_zero]
    linear_combination ih

/-- All-order actual Hill trace asymptotics on every smooth complex periodic
profile. The coefficients are the independently constructed scalar hierarchy,
whose native H^(m-1) extension is `nativeMiuraHillHamiltonian`. -/
theorem exists_physicalMiuraDiscriminant_hamiltonian_error_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ |r| →
      ‖physicalMiuraDiscriminant (miuraProfileCurve f hf.continuous) ((r : ℂ)^2)-
        2*cos (I*miuraHillHamiltonianPhase f N r)‖ ≤ C/(2*|r|)^(2*N) := by
  obtain ⟨C,hC,h⟩ := exists_classicalDiscriminant_hamiltonian_error_bound f f hf hf hp hp (2*N)
  refine ⟨C,hC,?_⟩
  intro r hr
  rw [physicalMiuraDiscriminant_profile_eq_ZS f hf.continuous hp,
    ← nlsHamiltonianPhase_diagonal_eq_miura f hf hp N]
  exact h r hr

end NLS.MKdV
