import NLS.Articles.KdVPseudomeasures.OriginalDirichletSourceCircles
import NLS.KdV.SingularDirichletProjectionComparison

/-! Exact physical kernels of ALL high original Dirichlet projections on
ONE original complex H^-1 norm neighborhood. No supplied contour, isolation,
projection, rank or bilinear-normalization hypotheses remain. -/
noncomputable section
open Set Metric MeasureTheory
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat

/-- The SAME actual source contour projection, with its physical continuous
output and the closed-unit-interval uniform norm. -/
def originalDirichletContinuousRieszProjection (q : OriginalComplexHminusOnePotential) (n : ℕ+) :
    IntervalL2 →L[ℂ] C(Icc (0:ℝ) 1,ℂ) :=
  singularDirichletContinuousRieszProjection q.val (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)

/-- On ONE original complex H^-1 neighborhood and cutoff, every high
ACTUAL source contour projection has its literal physical rank-one kernel.
The eigenfunction has the source's exact L2 normalization; its COMPLEX
bilinear square integral is proved NONZERO. The L2-to-uniform operator bound
retains that actual denominator, ready for high-frequency comparison.
No quantitative decay rate or overlap lower bound is inferred here. -/
theorem exists_uniform_originalDirichletRiesz_physical_kernel
    (q : OriginalComplexHminusOnePotential) :
    ∃ N : ℕ, ∃ U : Set (FourierLebesgueSpace (2:ℝ) (-1) 2),
      0 < N ∧ IsOpen U ∧ q.val ∈ U ∧
      ∀ a : OriginalComplexHminusOnePotential, a.val ∈ U →
        ∀ n : ℕ+, N < (n:ℕ) → ∃ g : UnitDirichletH1,
          singularDirichletOperator a.val g =
            originalComplexDirichletLabels a n • singularDirichletDomainInclusion g ∧
          ‖unitDirichletL2Inclusion g‖ = 1 ∧
          (∫ x in (0:ℝ)..1, ‖unitDirichletRepresentative g x‖^2) = 1 ∧
          (∫ x in (0:ℝ)..1, unitDirichletRepresentative g x*unitDirichletRepresentative g x) ≠ 0 ∧
          (∀ F : IntervalL2,
            originalDirichletRieszProjection a n F =
              ((∫ y in (0:ℝ)..1, F y*unitDirichletRepresentative g y)/
                (∫ y in (0:ℝ)..1, unitDirichletRepresentative g y*unitDirichletRepresentative g y)) •
                  unitDirichletL2Inclusion g) ∧
          (∀ F : IntervalL2, ∀ x : Icc (0:ℝ) 1,
            originalDirichletContinuousRieszProjection a n F x =
              ((∫ y in (0:ℝ)..1, F y*unitDirichletRepresentative g y)/
                (∫ y in (0:ℝ)..1, unitDirichletRepresentative g y*unitDirichletRepresentative g y))*
                  unitDirichletRepresentative g x.val) ∧
          ‖originalDirichletContinuousRieszProjection a n‖ ≤
            ‖unitDirichletContinuousInclusion g‖/
              ‖∫ y in (0:ℝ)..1, unitDirichletRepresentative g y*unitDirichletRepresentative g y‖ := by
  obtain ⟨N,U,hN,hU,hq,_,hcircles⟩ := exists_uniform_originalComplexDirichlet_sourceCircles q
  refine ⟨N,U,hN,hU,hq,?_⟩
  intro a ha n hn
  obtain ⟨hc,hl,hiso,hm⟩ := hcircles a ha n hn
  have honly (z : ℂ) (hz : z ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ))
      (hs : z ∈ singularDirichletSpectrum a.val) : z = originalComplexDirichletLabels a n :=
    (hiso z (ball_subset_closedBall hz)).mp hs
  obtain ⟨g,hg,hnorm,hint,_⟩ := exists_originalDirichletRiesz_normalized_generator a n hc hl honly hm
  have hg0 : g ≠ 0 := by
    intro he
    rw [he,map_zero,norm_zero] at hnorm
    norm_num at hnorm
  have hr : (0:ℝ) < (n:ℝ) := by exact_mod_cast n.property
  have hmass := singularDirichlet_bilinear_mass_ne_zero_of_simple_isolated a.val _ _ hr hc
    _ hl honly hm g hg0 hg
  rw [singularDirichletDomainInclusion_representative_pairing] at hmass
  refine ⟨g,hg,hnorm,hint,hmass,?_,?_,?_⟩
  · intro F
    change unitDirichletL2Inclusion (singularDirichletRieszToH1 a.val _ _
      (singularDirichletL2BaseInclusion F)) = _
    rw [singularDirichletRieszToH1_eq_pairing_smul a.val _ _ hr hc _ hl honly hm g hg0 hg,
      map_smul,singularDirichletL2BaseInclusion_representative_pairing,
      singularDirichletDomainInclusion_representative_pairing]
  · intro F x
    exact singularDirichletContinuousRieszProjection_apply_integral a.val _ _ hr hc
      _ hl honly hm g hg0 hg F x
  · have hb := norm_singularDirichletContinuousRieszProjection_le a.val _ _ hr hc
      _ hl honly hm g hg0 hg
    rw [hnorm,one_mul,singularDirichletDomainInclusion_representative_pairing] at hb
    exact hb

end NLS.Articles.KdVPseudomeasures
