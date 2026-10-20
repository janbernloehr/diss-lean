import NLS.ZakharovShabat.SobolevHamiltonianPhaseIncrement

/-! # The next Hamiltonian phase and its free model

The top available Riccati density gives a uniform inverse-frequency bound through phase order s+1.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The phase correction retains one inverse power through the next
phase N=s+1, using only the original Hs ball and the top L2 density. -/
theorem exists_uniform_nlsHamiltonian_next_phase_free_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s+1) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ →
        ‖nlsHamiltonianPhase a b N z+I*z‖ ≤ C*‖(2*I*z)⁻¹‖ := by
  induction N with
  | zero =>
    refine ⟨0,le_rfl,?_⟩
    intro ab hab a b ha hb hpa hpb hca hcb z hz
    simp [nlsHamiltonianPhase]
  | succ N ih =>
    obtain ⟨A,hA,hprev⟩ := ih (by omega)
    obtain ⟨B,hB,hinc⟩ := exists_uniform_nlsHamiltonianPhase_increment_bound s N hs (by omega) R hR
    refine ⟨A+B,by positivity,?_⟩
    intro ab hab a b ha hb hpa hpb hca hcb z hz
    let w := (2*I*z)⁻¹
    have hw : ‖w‖ ≤ 1 := by
      simp only [w,norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
      apply inv_le_one_of_one_le₀
      linarith
    have hp : ‖w‖^(N+1) ≤ ‖w‖ := by
      simpa only [pow_one] using pow_le_pow_of_le_one (norm_nonneg w) hw (by omega : 1 ≤ N+1)
    have he : nlsHamiltonianPhase a b (N+1) z+I*z =
        (nlsHamiltonianPhase a b N z+I*z)+
        (nlsHamiltonianPhase a b (N+1) z-nlsHamiltonianPhase a b N z) := by ring
    rw [he]
    calc
      _ ≤ ‖nlsHamiltonianPhase a b N z+I*z‖+
          ‖nlsHamiltonianPhase a b (N+1) z-nlsHamiltonianPhase a b N z‖ := norm_add_le _ _
      _ ≤ A*‖w‖+B*‖w‖^(N+1) := add_le_add
        (hprev ab hab a b ha hb hpa hpb hca hcb z hz)
        (hinc ab hab a b ha hb hpa hpb hca hcb z)
      _ ≤ A*‖w‖+B*‖w‖ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hB)
      _ = _ := by ring

end NLS.ZakharovShabat
