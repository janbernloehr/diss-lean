import NLS.KdV.HillRiccatiHierarchy
import NLS.KdV.HillL2UpperArcAsymptotics

/-! # The actual Hill primitive has the physical source hierarchy coefficients

All even integrated coefficients vanish. The odd coefficients carry precisely
the source unit-period factors, including the mean for nonzero-mean potentials.
The existing actual upper-arc bound therefore yields the physical all-order
expansion, without assuming a moment trace or a supplied phase asymptotic.
-/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

/-- The source Hamiltonians, with the unit-period inverse-frequency factors. -/
def hillHamiltonianPhase (q : ℝ → ℂ) (M : ℕ) (z : ℂ) : ℂ :=
  -I*z + I*(∫ x in (0 : ℝ)..1, q x)/(2*z) +
    ∑ m ∈ Finset.range M, I*classicalKdVHierarchyHamiltonian q m /
      (4^(m+1)*z^(2*m+3))

theorem hill_odd_phase_coefficient (H z : ℂ) (m : ℕ) :
    I*(2*H)/(2*z)^(2*m+3) = I*H/(4^(m+1)*z^(2*m+3)) := by
  have hp : (2 : ℂ)^(2*m+3) = 2*4^(m+1) := by
    rw [show 2*m+3 = 2*(m+1)+1 by omega, pow_add, pow_mul]
    norm_num
    ring
  rw [mul_pow, hp]
  field_simp

theorem nlsHamiltonianPhase_const_upper_source (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) (M : ℕ) (z : ℂ) :
    nlsHamiltonianPhase (fun _ => -1) (-q) (2*M+1) z = hillHamiltonianPhase q M z := by
  induction M with
  | zero => simp [nlsHamiltonianPhase, hillHamiltonianPhase]
  | succ M ih =>
    have hs : nlsHamiltonianPhase (fun _ => -1) (-q) (2*(M+1)+1) z =
        nlsHamiltonianPhase (fun _ => -1) (-q) (2*M+1) z +
          I*classicalNLSHamiltonian (fun _ => -1) (-q) (2*M+2)/(2*z)^(2*M+2) +
          I*classicalNLSHamiltonian (fun _ => -1) (-q) (2*M+3)/(2*z)^(2*M+3) := by
      rw [show 2*(M+1)+1 = (2*M+1)+1+1 by omega]
      simp only [nlsHamiltonianPhase, Finset.sum_range_succ]
      ring
    rw [hs, classicalNLSHamiltonian_const_upper_even q hq hp M,
      classicalNLSHamiltonian_const_upper_odd q hq M, ih, hill_odd_phase_coefficient]
    simp only [hillHamiltonianPhase, Finset.sum_range_succ, mul_zero, zero_div, add_zero]
    ring

/-- The all-order actual primitive expansion has the independent physical source coefficients. -/
theorem exists_hillL2RealCutPrimitive_upper_arc_source_hamiltonian_error_bound
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ n : ℕ, K ≤ n → ∀ t : Icc (0 : ℝ) Real.pi,
      ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))
          (hillFreeUpperFrequency n t ^ 2) -
        hillHamiltonianPhase (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) M
          (hillFreeUpperFrequency n t)‖ ≤ C / (2*hillFreeBandFrequency n)^(2*M+1) := by
  obtain ⟨C, hC, K, hbound⟩ := exists_hillL2RealCutPrimitive_upper_arc_error_bound
    Q hq hr hf hp (2*M+1) (by omega)
  refine ⟨C, hC, K, ?_⟩
  intro n hn t
  have h := hbound n hn t
  rw [show (fun x : ℝ => -Q (x : AddCircle (2 : ℝ))) =
      -(fun x : ℝ => Q (x : AddCircle (2 : ℝ))) by rfl,
    nlsHamiltonianPhase_const_upper_source _ hf hp] at h
  exact h

end NLS.KdV
