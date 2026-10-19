import NLS.ZakharovShabat.NLSHamiltonianPhaseIncrement
import NLS.ZakharovShabat.SobolevRiccatiApproximationUniform
import NLS.ComplexAnalysis.IntegralMajorantUnit

/-! # Uniform bounds for the next Hamiltonian phase

The next phase increment has its natural inverse-power bound on original Hs balls including the highest available density.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The next Hamiltonian phase increment has its natural inverse-power
bound uniformly on original Hs balls, including the top density N=s. -/
theorem exists_uniform_nlsHamiltonianPhase_increment_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) → ∀ z : ℂ,
      ‖nlsHamiltonianPhase a b (N+1) z-nlsHamiltonianPhase a b N z‖ ≤
        C*‖(2*I*z)⁻¹‖^(N+1) := by
  obtain ⟨A,hA,hpot⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  obtain ⟨L,hL,hL2⟩ := exists_uniform_nlsRiccatiDensity_L2_bound s N hNs R hR
  refine ⟨A*L,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z
  let r := nlsRiccatiDensity a b N
  have hr : Continuous r := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  have hL1 : (∫ x in (0:ℝ)..1, ‖r x‖) ≤ L := by
    have hi := integral_norm_le_sqrt_length_mul_L2 r 1 (by norm_num)
      (memLp_two_interval hr 0 1 (by norm_num))
    simp only [Real.sqrt_one,one_mul] at hi
    exact hi.trans (hL2 ab hab a b ha hb hpa hpb hca hcb)
  have hi : ‖∫ x in (0:ℝ)..1, a x*r x‖ ≤ A*L := by
    apply (norm_integral_unit_le_mul_integral_norm (fun x => a x*r x)
      (ha.continuous.mul hr) r hr A hA (fun x _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hpot ab hab a b ha hb hpa hpb hca hcb x) (norm_nonneg _))
      ⟨1,by constructor <;> norm_num⟩).trans
    exact mul_le_mul_of_nonneg_left hL1 hA
  rw [nlsHamiltonianPhase_succ_sub,norm_mul,norm_pow]
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring)

end NLS.ZakharovShabat
