import NLS.ComplexAnalysis.ExponentialIncrementRemainder
import NLS.ZakharovShabat.SobolevHamiltonianPhaseIncrement
import NLS.ZakharovShabat.SobolevWKBCarrierFreeUniform

/-! # The next Hamiltonian carrier estimate

The exponential of the next phase has a uniform order-(N+2) linearization error on original Hs balls.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The next Hamiltonian carrier has its first-order expansion with a
uniform order-(N+2) remainder on original Hs balls, including N=s. -/
theorem exists_uniform_nlsHamiltonianPhase_exp_increment_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
        ‖exp (nlsHamiltonianPhase a b (N+1) z)-exp (nlsHamiltonianPhase a b N z)-
          exp (-I*z)*(nlsHamiltonianPhase a b (N+1) z-nlsHamiltonianPhase a b N z)‖ ≤
          C*‖(2*I*z)⁻¹‖^(N+2) := by
  obtain ⟨A,hA,hfree⟩ := exists_uniform_nlsWKBCarrier_free_error_bound s N hs hNs R hR H
  obtain ⟨B,hB,hcarrier⟩ := exists_uniform_nlsWKBCarrier_strip_bounds s N hs hNs R hR H
  obtain ⟨L,hL,hinc⟩ := exists_uniform_nlsHamiltonianPhase_increment_bound s N hs hNs R hR
  refine ⟨A*L+B*L^2*Real.exp L,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH
  let u := nlsHamiltonianPhase a b N z
  let v := nlsHamiltonianPhase a b (N+1) z-u
  let w := (2*I*z)⁻¹
  have hw : ‖w‖ ≤ 1 := by
    simp only [w,norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    apply inv_le_one_of_one_le₀
    linarith
  have hu : ‖exp u‖ ≤ B := by
    have h := (hcarrier ab hab a b ha hb hpa hpb hca hcb 1 ⟨by norm_num,le_rfl⟩ z hz hzH).1
    rw [nlsWKBCarrier_one a b ha hb] at h
    exact h
  have hue : ‖exp u-exp (-I*z)‖ ≤ A*‖w‖ := by
    have h := hfree ab hab a b ha hb hpa hpb hca hcb 1 ⟨by norm_num,le_rfl⟩ z hz hzH
    rw [nlsWKBCarrier_one a b ha hb] at h
    simpa only [u,w,nlsHamiltonianPhase,Complex.ofReal_one,mul_one] using h
  have hv : ‖v‖ ≤ L*‖w‖^(N+1) := hinc ab hab a b ha hb hpa hpb hca hcb z
  have h := norm_exp_increment_sub_linear_le u v (exp (-I*z)) N ‖w‖ A B L
    (norm_nonneg _) hw hA hB.le hL hu hue hv
  have he : u+v = nlsHamiltonianPhase a b (N+1) z := by dsimp only [v]; ring
  rw [he] at h
  exact h

end NLS.ZakharovShabat
