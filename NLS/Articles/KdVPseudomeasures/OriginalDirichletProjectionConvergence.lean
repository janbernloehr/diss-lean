import NLS.Articles.KdVPseudomeasures.OriginalDirichletEigenfunctionComparison
import NLS.KdV.DirichletFreeRieszKernel

/-! The Dirichlet part of source (33): ACTUAL ordinary physical
L2-to-Linfinity and L2 operator convergence to the ACTUAL zero-potential
source contour projection, on prescribed-tolerance neighborhoods and
uniformly on EVERY fixed compact ORIGINAL complex H^-1 set.
The precise fractional-Sobolev logarithmic C.4 rate remains separate. -/
noncomputable section
open Set Metric Complex
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat

/-- The identical original source contour projection, now from ordinary
physical L2 into ordinary physical essential-supremum L-infinity. -/
def originalDirichletLinfRieszProjection (q : OriginalComplexHminusOnePotential) (n : ℕ+) :
    IntervalL2 →L[ℂ] IntervalLinf :=
  singularDirichletLinfRieszProjection q.val (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)

/-- The actual original L-infinity output is the SAME physical function
as the actual original L2 projection output, a.e. on the original interval. -/
theorem originalDirichletLinfRieszProjection_eq_L2_ae
    (q : OriginalComplexHminusOnePotential) (n : ℕ+) (F : IntervalL2) :
    originalDirichletLinfRieszProjection q n F =ᵐ[MeasureTheory.volume.restrict (Ioc (0:ℝ) 1)]
      originalDirichletRieszProjection q n F :=
  singularDirichletLinfRieszProjection_eq_L2_ae q.val _ _ F

/-- Dirichlet part of source (33), including the L2 norm needed in (34):
for EVERY epsilon>0 ONE original ambient H^-1 norm-open neighborhood and
ONE cutoff make the ACTUAL source projections epsilon-close to the ACTUAL
zero-potential contour projection in ALL THREE physical operator norms.
No abstract projection, changed circle, supplied eigenfunction comparison,
normalization bound or convergence estimate is used as a hypothesis. -/
theorem exists_uniform_originalDirichletProjection_sub_free_small
    (q : OriginalComplexHminusOnePotential) {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ N : ℕ, ∃ U : Set (FourierLebesgueSpace (2:ℝ) (-1) 2),
      0 < N ∧ IsOpen U ∧ q.val ∈ U ∧
      ∀ a : OriginalComplexHminusOnePotential, a.val ∈ U →
        ∀ n : ℕ+, N < (n:ℕ) →
          ‖originalDirichletContinuousRieszProjection a n-
            singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
          ‖originalDirichletLinfRieszProjection a n-
            singularDirichletLinfRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
          ‖originalDirichletRieszProjection a n-
            singularDirichletL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon := by
  let F := periodOneOriginalExtract
  obtain ⟨N,V,hN,hV,hqV,hcompare⟩ :=
    exists_uniform_hillHminusDirichletProjection_sub_free_small (F q.val) heps
  refine ⟨N,F ⁻¹' V,hN,hV.preimage F.continuous,hqV,?_⟩
  intro a ha n hn
  have h := hcompare (F a.val) ha n hn
  rw [originalComplexDirichlet_distribution a] at h
  exact h

/-- The Dirichlet source projections converge UNIFORMLY on EVERY fixed
compact set of ORIGINAL H^-1 distributions, in continuous uniform,
ordinary essential-supremum and ordinary L2 operator norms. -/
theorem exists_uniform_originalDirichletProjection_cutoff_on_compact
    (K : Set (FourierLebesgueSpace (2:ℝ) (-1) 2)) (hK : IsCompact K)
    {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ N : ℕ, 0 < N ∧ ∀ a : OriginalComplexHminusOnePotential, a.val ∈ K →
      ∀ n : ℕ+, N < (n:ℕ) →
        ‖originalDirichletContinuousRieszProjection a n-
          singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
        ‖originalDirichletLinfRieszProjection a n-
          singularDirichletLinfRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon ∧
        ‖originalDirichletRieszProjection a n-
          singularDirichletL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < epsilon := by
  let F := periodOneOriginalExtract
  obtain ⟨N,hN,hbound⟩ := exists_uniform_hillHminusDirichletProjection_cutoff_on_compact
    (F '' K) (hK.image F.continuous) heps
  refine ⟨N,hN,?_⟩
  intro a ha n hn
  have h := hbound (F a.val) ⟨a.val,ha,rfl⟩ n hn
  rw [originalComplexDirichlet_distribution a] at h
  exact h

/-- Source-normalized ACTUAL high original Dirichlet eigenfunctions have
uniform physical sup-norm and strictly positive bilinear-mass bounds on ONE
original complex H^-1 neighborhood/cutoff. Both the literal L2 norm-square
integral one and the COMPLEX unconjugated mass integral are retained. -/
theorem exists_uniform_normalized_originalDirichletEigenfunction_bounds
    (q : OriginalComplexHminusOnePotential) :
    ∃ N : ℕ, ∃ U : Set (FourierLebesgueSpace (2:ℝ) (-1) 2),
      0 < N ∧ IsOpen U ∧ q.val ∈ U ∧
      ∀ a : OriginalComplexHminusOnePotential, a.val ∈ U →
        ∀ n : ℕ+, N < (n:ℕ) → ∃ g : UnitDirichletH1,
          singularDirichletOperator a.val g =
            originalComplexDirichletLabels a n • singularDirichletDomainInclusion g ∧
          ‖unitDirichletL2Inclusion g‖ = 1 ∧
          (∫ x in (0:ℝ)..1, ‖unitDirichletRepresentative g x‖^2) = 1 ∧
          ‖unitDirichletContinuousInclusion g‖ ≤ 4 ∧
          (1/16:ℝ) ≤ ‖∫ x in (0:ℝ)..1,
            unitDirichletRepresentative g x*unitDirichletRepresentative g x‖ := by
  let F := periodOneOriginalExtract
  obtain ⟨N,V,hN,hV,hqV,hbounds⟩ :=
    exists_uniform_normalized_hillHminusDirichletEigenfunction_bounds (F q.val)
  refine ⟨N,F ⁻¹' V,hN,hV.preimage F.continuous,hqV,?_⟩
  intro a ha n hn
  obtain ⟨g,hg,hnorm,hint,hC,hM⟩ := hbounds (F a.val) ha n hn
  rw [originalComplexDirichlet_distribution a] at hg
  rw [singularDirichletDomainInclusion_representative_pairing] at hM
  exact ⟨g,hg,hnorm,hint,hC,hM⟩

end NLS.Articles.KdVPseudomeasures
