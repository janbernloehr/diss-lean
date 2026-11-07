import NLS.Articles.KdVPseudomeasures.EndpointDirichletProjectionConvergence
import NLS.KdV.DirichletFreeProjectionBounds

/-! Uniform physical L2 norm of the ACTUAL Dirichlet source projections. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- One original endpoint ball cutoff bounds every actual Dirichlet
projection by THREE in the SAME ordinary physical interval L2 norm. -/
theorem exists_uniform_sourceDirichletProjection_norm_le_three
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, ∀ n : ℕ+, N ≤ (n:ℕ) →
        ‖originalDirichletRieszProjection (sourceOriginalComplexPotential r hr q hp) n‖ ≤ 3 := by
  obtain ⟨ND,hND,hD⟩ := exists_uniform_sourceEndpointDirichletProjection_sub_free_small r hr R
    (epsilon := 1) (by norm_num)
  obtain ⟨NF,_,hF⟩ := exists_dirichletFreeProjection_bounds_and_sine_fixed
  refine ⟨max ND (NF+1),hND.trans (le_max_left _ _),?_⟩
  intro q hq hp n hn
  have he := (hD q hq hp n ((le_max_left _ _).trans hn)).2.2
  have hf := (hF n (by omega)).2.1
  have ht := norm_le_norm_sub_add (originalDirichletRieszProjection (sourceOriginalComplexPotential r hr q hp) n)
    (singularDirichletL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ))
  linarith

end NLS.Articles.KdVPseudomeasures
