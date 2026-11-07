import NLS.Articles.KdVPseudomeasures.OriginalDirichletRieszKernel
import NLS.KdV.HminusOneDirichletEigenfunctionComparison

/-! Actual high original Dirichlet eigenfunctions approach the LITERAL
free sine in the closed-interval uniform norm, locally uniformly in the
ORIGINAL complex H^-1 distribution topology, at the SAME positive index. -/
noncomputable section
open Set Metric Complex
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- For every epsilon>0, ONE original ambient H^-1 norm-open neighborhood
and cutoff give nonzero ACTUAL native Dirichlet eigenfunctions within epsilon
of sin(n*pi*x), uniformly on the CLOSED physical unit interval, for ALL nearby
complex physically period-one sources and ALL subsequent ORIGINAL indices.
The phase is fixed by the physical Dirac initial column. Their L2 normalization
is NOT imposed here; it will be controlled by this actual sine comparison. -/
theorem exists_uniform_originalDirichletEigenfunction_sine_comparison
    (q : OriginalComplexHminusOnePotential) {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ N : ℕ, ∃ U : Set (FourierLebesgueSpace (2:ℝ) (-1) 2),
      0 < N ∧ IsOpen U ∧ q.val ∈ U ∧
      ∀ a : OriginalComplexHminusOnePotential, a.val ∈ U →
        ∀ n : ℕ+, N < (n:ℕ) → ∃ g : UnitDirichletH1, g ≠ 0 ∧
          singularDirichletOperator a.val g =
            originalComplexDirichletLabels a n • singularDirichletDomainInclusion g ∧
          ‖unitDirichletContinuousInclusion g-dirichletFreeSineCurve n‖ < epsilon := by
  let F := periodOneOriginalExtract
  obtain ⟨N,V,hN,hV,hqV,hcompare⟩ :=
    exists_uniform_hillHminusDirichletEigenfunction_sine_comparison (F q.val) heps
  refine ⟨N,F ⁻¹' V,hN,hV.preimage F.continuous,hqV,?_⟩
  intro a ha n hn
  obtain ⟨g,hg0,hg,he⟩ := hcompare (F a.val) ha n hn
  rw [originalComplexDirichlet_distribution a] at hg
  exact ⟨g,hg0,hg,he⟩

end NLS.Articles.KdVPseudomeasures
