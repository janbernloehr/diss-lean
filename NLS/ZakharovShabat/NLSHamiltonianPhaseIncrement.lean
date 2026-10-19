import NLS.ZakharovShabat.NLSWKBDiagonalPhaseDecomposition
import NLS.ZakharovShabat.NLSHamiltonianPhaseReflection

/-! # The next Hamiltonian phase and diagonal primitives

The signed endpoint primitives are exactly the next Hamiltonian phase increment multiplied by the free carriers.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The next Hamiltonian phase coefficient is the exact primitive of
the first omitted Riccati density. -/
theorem nlsHamiltonianPhase_succ_sub
    (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) :
    nlsHamiltonianPhase a b (N+1) z-nlsHamiltonianPhase a b N z =
      ((2*I*z)⁻¹)^(N+1)*(∫ x in (0:ℝ)..1, a x*nlsRiccatiDensity a b N x) := by
  simp only [nlsHamiltonianPhase,Finset.sum_range_succ]
  have h := classicalNLSHamiltonian_riccati_coefficient a b N z
  rw [div_eq_mul_inv,← inv_pow] at h
  linear_combination -h

/-- The diagonal primitive at one period is the negative next phase
increment multiplied by the free first carrier. -/
theorem nlsWKBDiagonalPhasePrimitive_one_eq_phase_increment
    (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) :
    nlsWKBDiagonalPhasePrimitive a b N z 1 =
      -exp (-I*z)*(nlsHamiltonianPhase a b (N+1) z-nlsHamiltonianPhase a b N z) := by
  rw [nlsHamiltonianPhase_succ_sub]
  simp only [nlsWKBDiagonalPhasePrimitive,Complex.ofReal_one,mul_one]
  ring

/-- Both diagonal primitives form the first variation of the two free
carriers under the same next Hamiltonian phase increment. -/
theorem nlsWKBDiagonalPhasePrimitive_sum_eq_phase_increment
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (z : ℂ) :
    nlsWKBDiagonalPhasePrimitive a b N z 1+
      nlsWKBDiagonalPhasePrimitive (-b) (-a) N (-z) 1 =
      -(exp (-I*z)-exp (I*z))*(nlsHamiltonianPhase a b (N+1) z-nlsHamiltonianPhase a b N z) := by
  rw [nlsWKBDiagonalPhasePrimitive_one_eq_phase_increment,
    nlsWKBDiagonalPhasePrimitive_one_eq_phase_increment,
    nlsHamiltonianPhase_signedSwap a b ha hb hpa hpb,
    nlsHamiltonianPhase_signedSwap a b ha hb hpa hpb]
  simp only [mul_neg]
  ring_nf

end NLS.ZakharovShabat
