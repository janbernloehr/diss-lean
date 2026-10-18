import NLS.ZakharovShabat.NLSHamiltonianReflection

/-! # Exact cancellation of the two WKB phases

The finite physical Hamiltonian phases cancel under signed swap and spectral reflection, at every order and frequency.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The two actual finite WKB phases cancel exactly under signed swap
and spectral reflection, at every truncation and every complex frequency. -/
theorem nlsHamiltonianPhase_signedSwap
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (z : ℂ) :
    nlsHamiltonianPhase (-b) (-a) N (-z) = -nlsHamiltonianPhase a b N z := by
  have hterm (k : ℕ) :
      I*classicalNLSHamiltonian (-b) (-a) (k+1)/(2*(-z))^(k+1) =
        -(I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1)) := by
    have h := classicalNLSHamiltonian_reflection_relation a b ha hb hpa hpb k
    simp only [div_eq_mul_inv,mul_neg,← inv_pow,inv_neg]
    rw [neg_pow]
    linear_combination (I*((2*z)⁻¹)^(k+1))*h
  unfold nlsHamiltonianPhase
  simp only [hterm,Finset.sum_neg_distrib]
  ring

/-- The second WKB endpoint multiplier is the inverse of the first. -/
theorem exp_nlsHamiltonianPhase_signedSwap
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (z : ℂ) :
    exp (nlsHamiltonianPhase (-b) (-a) N (-z)) = (exp (nlsHamiltonianPhase a b N z))⁻¹ := by
  rw [nlsHamiltonianPhase_signedSwap a b ha hb hpa hpb,exp_neg]

end NLS.ZakharovShabat
