import NLS.ZakharovShabat.NLSHamiltonianDiscriminantAsymptotics
import Mathlib.Analysis.Analytic.Order

/-! # The Hamiltonian phase as an inverse-frequency polynomial -/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ZakharovShabat

/-- The finite Hamiltonian correction, written in the inverse spectral variable. -/
def nlsHamiltonianCorrection (a b : ℝ → ℂ) (N : ℕ) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N, (I*classicalNLSHamiltonian a b (k+1)/2^(k+1))*w^(k+1)

@[simp] theorem nlsHamiltonianCorrection_zero (a b : ℝ → ℂ) (N : ℕ) :
    nlsHamiltonianCorrection a b N 0 = 0 := by simp [nlsHamiltonianCorrection]

@[fun_prop] theorem analyticAt_nlsHamiltonianCorrection (a b : ℝ → ℂ) (N : ℕ) (w : ℂ) :
    AnalyticAt ℂ (nlsHamiltonianCorrection a b N) w := by
  unfold nlsHamiltonianCorrection
  exact Finset.analyticAt_fun_sum _ (fun _ _ => analyticAt_const.mul (analyticAt_id.pow _))

theorem nlsHamiltonianPhase_eq_correction (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) :
    nlsHamiltonianPhase a b N z = -I*z+nlsHamiltonianCorrection a b N z⁻¹ := by
  unfold nlsHamiltonianPhase nlsHamiltonianCorrection
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_pow,div_mul_eq_div_div,div_eq_mul_inv,inv_pow]

/-- The finite phase correction tends to zero at infinite frequency. -/
theorem nlsHamiltonianCorrection_tendsto (a b : ℝ → ℂ) (N : ℕ) :
    Tendsto (fun z : ℂ => nlsHamiltonianCorrection a b N z⁻¹)
      (Bornology.cobounded ℂ) (𝓝 0) := by
  have h := (analyticAt_nlsHamiltonianCorrection a b N 0).continuousAt.tendsto.comp
    tendsto_inv₀_cobounded
  simpa using! h

/-- The Taylor coefficient of the correction is exactly the physical Hamiltonian. -/
theorem iteratedDeriv_nlsHamiltonianCorrection (a b : ℝ → ℂ) (N k : ℕ) (hk : k < N) :
    iteratedDeriv (k+1) (nlsHamiltonianCorrection a b N) 0 =
      ((k+1).factorial : ℂ)*(I*classicalNLSHamiltonian a b (k+1)/2^(k+1)) := by
  unfold nlsHamiltonianCorrection
  rw [iteratedDeriv_fun_sum (fun j _ => (analyticAt_const.mul (analyticAt_id.pow (j+1))).contDiffAt)]
  simp only [iteratedDeriv_const_mul_field,iteratedDeriv_fun_pow_zero]
  simp [Finset.mem_range.mpr hk,mul_comm]

end NLS.ZakharovShabat
