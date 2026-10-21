import NLS.ZakharovShabat.SourceSpectralDisplacementSobolevBall
import NLS.ZakharovShabat.SourceBoundaryCriticalPhaseComparison

/-! # Uniform boundary-to-critical phase comparison

One absorption cutoff and one inverse-index estimate apply to both boundary conditions on every real Sobolev ball.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The phase comparison needed for root recovery has one absorption cutoff
and one inverse-index bound on every real original Hs ball. -/
theorem exists_uniform_real_source_boundary_critical_phase_difference_bounds
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R → ∀ θ : BoundaryCondition,
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.val.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.val.2.val j = periodOneCoefficient b j) →
      ∀ n : ℤ, K ≤ n.natAbs →
      ‖sourceBoundaryCriticalPhaseDifference s θ ab.val n+I*sourceBoundaryCriticalRootDifference s θ ab.val n‖ ≤
        (1/2:ℝ)*‖sourceBoundaryCriticalRootDifference s θ ab.val n‖ ∧
      (1+|(n:ℝ)|)*
        ‖sourceBoundaryCriticalPhaseDifference s θ ab.val n+I*sourceBoundaryCriticalRootDifference s θ ab.val n‖ ≤
        C*‖sourceBoundaryCriticalRootDifference s θ ab.val n‖ := by
  obtain ⟨_,M,_,_,hdisp⟩ := exists_uniform_real_higherSobolev_displacement_envelopes s hs R hR
  obtain ⟨K₀,hK₀,C,hC,hphase⟩ :=
    exists_uniform_nlsHamiltonian_next_phase_difference_bound s (s+1) hs le_rfl R hR
  obtain ⟨K₁,hK₁⟩ := exists_nat_gt (max M (2*C))
  let K := max K₀ K₁
  refine ⟨K,hK₀.trans_le (le_max_left _ _),C,hC,?_⟩
  intro ab hab θ a b ha hb hpa hpb hca hcb n hn
  let μ := canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
    (higherSobolevSourceInclusion s ab.val) n
  let κ := canonicalCriticalPoints (by norm_num) (by norm_num)
    (periodOnePotential (higherSobolevSourceInclusion s ab.val)) (periodOnePotential_mem _) n
  let q : ℝ := 1+|(n:ℝ)|
  have hq : 0 < q := by dsimp [q]; positivity
  have hKq : (K₁:ℝ) ≤ q := by
    have hn' : (K₁:ℝ) ≤ n.natAbs := by exact_mod_cast (le_max_right K₀ K₁).trans hn
    have hnabs : (n.natAbs:ℝ) = |(n:ℝ)| := by simp
    dsimp only [q]
    rw [← hnabs]
    linarith
  have hMq : M ≤ q := ((le_max_left M _).trans hK₁.le).trans hKq
  have hCq : 2*C ≤ q := ((le_max_right M _).trans hK₁.le).trans hKq
  have hμ : ‖μ-(Real.pi:ℂ)*n‖ ≤ 1 := by
    have h := ((hdisp ab hab).1 θ).2 n
    simp only [sourceBoundaryDisplacement_apply] at h
    change q*‖μ-(Real.pi:ℂ)*n‖ ≤ M at h
    nlinarith
  have hκ : ‖κ-(Real.pi:ℂ)*n‖ ≤ 1 := by
    have h := (hdisp ab hab).2.2 n
    simp only [sourceCriticalDisplacement,canonicalCriticalDisplacement_apply] at h
    change q*‖κ-(Real.pi:ℂ)*n‖ ≤ M at h
    nlinarith
  have h := hphase ab.val hab a b ha hb hpa hpb hca hcb n
    ((le_max_left _ _).trans hn) μ κ hμ hκ
  have he : sourceBoundaryCriticalPhaseDifference s θ ab.val n =
      nlsHamiltonianPhase a b (s+1) μ-nlsHamiltonianPhase a b (s+1) κ := by
    simp only [sourceBoundaryCriticalPhaseDifference,sourceBoundaryNextPhaseOffset,
      sourceCriticalNextPhaseOffset,sobolevNextHamiltonianPhase_eq_classical s ab.val a b ha hb hpa hpb hca hcb]
    ring
  change ‖nlsHamiltonianPhase a b (s+1) μ-nlsHamiltonianPhase a b (s+1) κ+I*(μ-κ)‖ ≤ C/q*‖μ-κ‖ at h
  rw [he]
  change ‖nlsHamiltonianPhase a b (s+1) μ-nlsHamiltonianPhase a b (s+1) κ+I*(μ-κ)‖ ≤ (1/2:ℝ)*‖μ-κ‖ ∧
    q*‖nlsHamiltonianPhase a b (s+1) μ-nlsHamiltonianPhase a b (s+1) κ+I*(μ-κ)‖ ≤ C*‖μ-κ‖
  constructor
  · exact h.trans (mul_le_mul_of_nonneg_right ((div_le_iff₀ hq).mpr (by linarith)) (norm_nonneg _))
  · calc
      _ ≤ q*(C/q*‖μ-κ‖) := mul_le_mul_of_nonneg_left h hq.le
      _ = C*‖μ-κ‖ := by field_simp

end NLS.ZakharovShabat
