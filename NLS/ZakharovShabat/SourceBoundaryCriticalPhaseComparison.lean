import NLS.ZakharovShabat.SourceBoundaryPhaseSmoothTail
import NLS.ZakharovShabat.SourceCriticalPhaseSmoothTail
import NLS.ZakharovShabat.SobolevNextPhaseDifference

/-! # The actual boundary-to-critical phase comparison

A common original-source neighborhood and cutoff give the smallness and inverse-index bounds needed to recover the root difference.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The difference between the canonical boundary root and critical point. -/
def sourceBoundaryCriticalRootDifference (s : ℕ) (θ : BoundaryCondition)
    (ab : SobolevSource s) (n : ℤ) : ℂ :=
  canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
    (higherSobolevSourceInclusion s ab) n-
  canonicalCriticalPoints (by norm_num) (by norm_num)
    (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n

/-- The corresponding next-phase difference; the free centers cancel. -/
def sourceBoundaryCriticalPhaseDifference (s : ℕ) (θ : BoundaryCondition)
    (ab : SobolevSource s) (n : ℤ) : ℂ :=
  sourceBoundaryNextPhaseOffset s θ ab n-sourceCriticalNextPhaseOffset s ab n

/-- On one original-source neighborhood, a common tail makes the nonlinear
boundary-to-critical phase difference small enough to absorb, while retaining
its inverse-index gain. Smooth periodic representatives remain explicit. -/
theorem exists_local_source_boundary_critical_phase_difference_bounds
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) (θ : BoundaryCondition) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ab ∈ U,
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ n : ℤ, K ≤ n.natAbs →
      ‖sourceBoundaryCriticalPhaseDifference s θ ab n+I*sourceBoundaryCriticalRootDifference s θ ab n‖ ≤
        (1/2:ℝ)*‖sourceBoundaryCriticalRootDifference s θ ab n‖ ∧
      (1+|(n:ℝ)|)*
        ‖sourceBoundaryCriticalPhaseDifference s θ ab n+I*sourceBoundaryCriticalRootDifference s θ ab n‖ ≤
        C*‖sourceBoundaryCriticalRootDifference s θ ab n‖ := by
  obtain ⟨U,hU,haU,R,_,M,hR,_,_,hu⟩ :=
    exists_local_higherSobolev_boundary_weighted_displacement_bounds s hs a₀ θ
  obtain ⟨V,hV,haV,_,_,M',_,_,_,hv⟩ :=
    exists_local_higherSobolev_critical_weighted_displacement_bounds s hs a₀
  obtain ⟨K₀,hK₀,C,hC,hphase⟩ :=
    exists_uniform_nlsHamiltonian_next_phase_difference_bound s (s+1) hs le_rfl R hR
  obtain ⟨K₁,hK₁⟩ := exists_nat_gt (max M (max M' (2*C)))
  let K := max K₀ K₁
  refine ⟨U ∩ V,hU.inter hV,⟨haU,haV⟩,K,hK₀.trans_le (le_max_left _ _),C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb n hn
  let μ := canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
    (higherSobolevSourceInclusion s ab) n
  let κ := canonicalCriticalPoints (by norm_num) (by norm_num)
    (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n
  let q : ℝ := 1+|(n:ℝ)|
  have hq : 0 < q := by dsimp [q]; positivity
  have hKq : (K₁:ℝ) ≤ q := by
    have hn' : (K₁:ℝ) ≤ n.natAbs := by exact_mod_cast (le_max_right K₀ K₁).trans hn
    have hnabs : (n.natAbs:ℝ) = |(n:ℝ)| := by simp
    dsimp only [q]
    rw [← hnabs]
    linarith
  have hMq : M ≤ q := ((le_max_left M _).trans hK₁.le).trans hKq
  have hM'q : M' ≤ q := ((le_max_left M' _).trans (le_max_right M _)).trans (hK₁.le.trans hKq)
  have hCq : 2*C ≤ q := ((le_max_right M' _).trans (le_max_right M _)).trans (hK₁.le.trans hKq)
  have hμ : ‖μ-(Real.pi:ℂ)*n‖ ≤ 1 := by
    have h := (hu ab hab.1).2.2 n
    change q*‖μ-(Real.pi:ℂ)*n‖ ≤ M at h
    nlinarith
  have hκ : ‖κ-(Real.pi:ℂ)*n‖ ≤ 1 := by
    have h := (hv ab hab.2).2.2 n
    change q*‖κ-(Real.pi:ℂ)*n‖ ≤ M' at h
    nlinarith
  have h := hphase ab (hu ab hab.1).1 a b ha hb hpa hpb hca hcb n
    ((le_max_left _ _).trans hn) μ κ hμ hκ
  have he : sourceBoundaryCriticalPhaseDifference s θ ab n =
      nlsHamiltonianPhase a b (s+1) μ-nlsHamiltonianPhase a b (s+1) κ := by
    simp only [sourceBoundaryCriticalPhaseDifference,sourceBoundaryNextPhaseOffset,
      sourceCriticalNextPhaseOffset,sobolevNextHamiltonianPhase_eq_classical s ab a b ha hb hpa hpb hca hcb]
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
