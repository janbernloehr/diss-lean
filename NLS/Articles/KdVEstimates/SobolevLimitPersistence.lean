import NLS.Articles.KdVEstimates.DynamicalCorollary
import NLS.KdV.HillWeightedPhysicalLimit

/-! Sobolev membership of physical L² approximation limits is a conclusion.
The classical approximants have a common bound on their initial Sobolev
norms; the previously proved dynamical estimate supplies the bound at every
time. This theorem does not construct the approximating trajectories. -/
noncomputable section
set_option autoImplicit false
open NLS.KdV Filter Topology
namespace NLS.Articles.KdVEstimates

theorem exists_sobolev_bound_of_classical_approximation (m : ℕ) (hm : 1 ≤ m) :
    ∃ α : ℝ, 0 < α ∧
      ∀ (v : ℕ → ℝ → RealHillWeightedPotential (hillIntegerWeight m))
        (u : ℝ → RealPeriodOneHillPotential) (B : ℝ),
      (∀ N, (v N 0).val.val 0 = 0) →
      (∀ N, IsClassicalKdVTrajectory
        (fun t => hillRealWeightedEmbedding (hillIntegerWeight m) (v N t))) →
      (∀ N, ‖(v N 0).val‖ ≤ B) →
      (∀ t, Tendsto (fun N => hillRealWeightedEmbedding (hillIntegerWeight m) (v N t))
        atTop (𝓝 (u t))) →
      ∀ t, ∃ p : RealHillWeightedPotential (hillIntegerWeight m),
        hillRealWeightedEmbedding (hillIntegerWeight m) p = u t ∧
        ‖p.val‖ ≤ α*(B+(1+B)^(m*m+m-1)*B) := by
  obtain ⟨α,hα,hestimate⟩ := corollary1_dynamical_classical m hm
  refine ⟨α,hα,?_⟩
  intro v u B hmean hpde hB hlim t
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  apply exists_hillRealWeighted_of_bounded_tendsto (hillIntegerWeight m)
    (fun N => v N t) (u t) _ _ (hlim t)
  intro N
  have hlow : ‖(hillRealNativeIntegerLower m (m-1) (by omega) (v N 0)).val‖ ≤ B := by
    exact (WeightedCoeff.norm_inclusionCLM_le _ _ _ _).trans (hB N)
  apply (hestimate (v N) (hmean N) (hpde N) t).trans
  apply mul_le_mul_of_nonneg_left _ hα.le
  gcongr
  exact hB N

/-- Initial convergence in H^m suffices for a uniform-in-time H^m bound
on any physical L² limit of the classical approximants. The limit path is
not assumed to take values in H^m. -/
theorem sobolev_membership_of_convergent_initial_approximation (m : ℕ) (hm : 1 ≤ m)
    (v : ℕ → ℝ → RealHillWeightedPotential (hillIntegerWeight m))
    (u : ℝ → RealPeriodOneHillPotential)
    (p₀ : RealHillWeightedPotential (hillIntegerWeight m))
    (hmean : ∀ N, (v N 0).val.val 0 = 0)
    (hpde : ∀ N, IsClassicalKdVTrajectory
      (fun t => hillRealWeightedEmbedding (hillIntegerWeight m) (v N t)))
    (hinit : Tendsto (fun N => (v N 0).val) atTop (𝓝 p₀.val))
    (hlim : ∀ t, Tendsto (fun N => hillRealWeightedEmbedding (hillIntegerWeight m) (v N t))
      atTop (𝓝 (u t))) :
    ∃ C : ℝ, ∀ t, ∃ p : RealHillWeightedPotential (hillIntegerWeight m),
      hillRealWeightedEmbedding (hillIntegerWeight m) p = u t ∧ ‖p.val‖ ≤ C := by
  obtain ⟨B,hB⟩ := (isBounded_iff_forall_norm_le).mp
    (Metric.isBounded_range_of_tendsto (fun N => (v N 0).val) hinit)
  obtain ⟨α,_,hα⟩ := exists_sobolev_bound_of_classical_approximation m hm
  exact ⟨α*(B+(1+B)^(m*m+m-1)*B),hα v u B hmean hpde
    (fun N => hB _ ⟨N,rfl⟩) hlim⟩

end NLS.Articles.KdVEstimates
