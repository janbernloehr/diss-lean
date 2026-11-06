import NLS.KdV.ClassicalTraceAsymptotics
import NLS.KdV.ClassicalDiscriminant
import NLS.ZakharovShabat.NLSHamiltonianWeightedAsymptotics

/-! # Physical Hill trace coefficients with uniform complex-frequency errors

The actual scalar energy discriminant has the physical quadratic and KdV
energy coefficients throughout the upper frequency half-plane. The error
constant is independent of imaginary height. Higher phase coefficients
remain explicit, so the energy coefficient is not hidden in its own error.
-/

noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

theorem exists_classicalHillDiscriminant_upper_higher_error_bound (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1)
    (hmean : (∫ x in (0 : ℝ)..1, q x) = 0) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → 0 ≤ z.im →
      ‖classicalHillDiscriminant (scalarPotentialCurve q hq.continuous) (z^2) -
        2*cos (z - classicalQuadraticInvariant q / (4*z^3) -
          classicalHamiltonian q / (16*z^5) -
          ∑ j ∈ Finset.range N, classicalNLSHamiltonian (fun _ => -1) (-q) (j+6) /
            (2*z)^(j+6))‖ ≤ C / (2*‖z‖)^(N+5) * Real.exp z.im := by
  obtain ⟨C, hC, herr⟩ := exists_classicalDiscriminant_upper_hamiltonian_error_bound
    (fun _ => -1) (-q) contDiff_const hq.neg (fun _ => rfl)
    (fun x => by change -q (x+1) = -q x; rw [hp x]) (N+5)
  refine ⟨C, hC, ?_⟩
  intro z hz him
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have h := herr z hz him
  rw [phase_const_upper_extended q hq hp hmean N z hz0] at h
  rw [classicalHillDiscriminant_sq, constantUpperPotential_scalarPotentialCurve]
  exact h

/-- Removing the free exponential gives a uniform inverse-power error
even when imaginary frequency grows without bound. -/
theorem exists_classicalHillDiscriminant_upper_normalized_error_bound (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1)
    (hmean : (∫ x in (0 : ℝ)..1, q x) = 0) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → 0 ≤ z.im →
      ‖exp (I*z) * (classicalHillDiscriminant (scalarPotentialCurve q hq.continuous) (z^2) -
        2*cos (z - classicalQuadraticInvariant q / (4*z^3) -
          classicalHamiltonian q / (16*z^5) -
          ∑ j ∈ Finset.range N, classicalNLSHamiltonian (fun _ => -1) (-q) (j+6) /
            (2*z)^(j+6)))‖ ≤ C / (2*‖z‖)^(N+5) := by
  obtain ⟨C, hC, herr⟩ := exists_classicalHillDiscriminant_upper_higher_error_bound q hq hp hmean N
  refine ⟨C, hC, ?_⟩
  intro z hz him
  rw [norm_mul, norm_exp, show (I*z).re = -z.im by simp [mul_re]]
  have h := mul_le_mul_of_nonneg_left (herr z hz him) (Real.exp_nonneg (-z.im))
  apply h.trans_eq
  rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end NLS.KdV
