import NLS.Articles.KdVPseudomeasures.OriginalDirichletProjectionConvergence
import NLS.Articles.KdVPseudomeasures.PeriodicSourceCircles
import NLS.Fourier.PeriodicEndpointCompactInclusion
import NLS.KdV.HminusOneDirichletCompactCircles

/-! Uniform actual Dirichlet projection convergence and source-circle
isolation on every fixed ORIGINAL complex endpoint norm ball. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The entire original endpoint ball has compact image in the actual
original H-minus-one space, before imposing any physical constraint. -/
theorem isCompact_sourceComplexHminusOne_normBall (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) :
    IsCompact (sourceComplexHminusOne r hr ''
      {q : FourierLebesgueSpace (2:ℝ) (-r) ⊤ | ‖q‖ ≤ R}) := by
  have he : (closedBall (0 : FourierLebesgueSpace (2:ℝ) (-r) ⊤) R) =
      {q | ‖q‖ ≤ R} := by ext q; simp
  rw [← he]
  exact isCompact_endpointLowerInclusion_closedBall (L := 2) r (-1) R (by norm_num)
    (admissible_hminusOne_threshold r hr)

/-- ONE cutoff before ALL physically period-one sources in each original
complex endpoint ball gives actual Dirichlet convergence in all THREE
original physical operator norms. No supplied compactness premise remains. -/
theorem exists_uniform_sourceEndpointDirichletProjection_sub_free_small
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, ∀ n : ℕ+, N ≤ (n:ℕ) →
        ‖originalDirichletContinuousRieszProjection (sourceOriginalComplexPotential r hr q hp) n-
          singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
        ‖originalDirichletLinfRieszProjection (sourceOriginalComplexPotential r hr q hp) n-
          singularDirichletLinfRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
        ‖originalDirichletRieszProjection (sourceOriginalComplexPotential r hr q hp) n-
          singularDirichletL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon := by
  obtain ⟨N,_,hbound⟩ := exists_uniform_originalDirichletProjection_cutoff_on_compact _
    (isCompact_sourceComplexHminusOne_normBall r hr R) heps
  refine ⟨max 2 (N+1),by omega,?_⟩
  intro q hq hp n hn
  exact hbound (sourceOriginalComplexPotential r hr q hp) ⟨q,hq,rfl⟩ n (by omega)

/-- The same ball admits ONE cutoff for all actual Dirichlet circles,
same-index isolation and actual algebraic multiplicity one. -/
theorem exists_uniform_sourceEndpointDirichlet_sourceCircles
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, ∀ n : ℕ+, N ≤ (n:ℕ) →
        let a := sourceOriginalComplexPotential r hr q hp
        sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularDirichletResolventSet a.val ∧
        originalComplexDirichletLabels a n ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ∧
        (∀ z ∈ closedBall (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ),
          z ∈ singularDirichletSpectrum a.val ↔ z = originalComplexDirichletLabels a n) ∧
        singularDirichletAlgebraicMultiplicity a.val (originalComplexDirichletLabels a n) = 1 := by
  let K := sourceComplexHminusOne r hr ''
    {q : FourierLebesgueSpace (2:ℝ) (-r) ⊤ | ‖q‖ ≤ R}
  have hK : IsCompact K := isCompact_sourceComplexHminusOne_normBall r hr R
  obtain ⟨N,_,hbound⟩ := exists_uniform_hillHminusDirichlet_sourceCircles_on_compact
    (periodOneOriginalExtract '' K) (hK.image periodOneOriginalExtract.continuous)
  refine ⟨max 2 (N+1),by omega,?_⟩
  intro q hq hp n hn a
  have hb := hbound (periodOneOriginalExtract a.val) ⟨a.val,⟨q,hq,rfl⟩,rfl⟩ n (by omega)
  rw [originalComplexDirichlet_distribution a] at hb
  exact hb

end NLS.Articles.KdVPseudomeasures
