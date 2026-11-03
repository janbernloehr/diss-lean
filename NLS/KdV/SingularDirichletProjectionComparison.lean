import NLS.KdV.SingularDirichletRieszKernel
import NLS.FunctionalAnalysis.RankOneKernelComparison

/-! Quantitative comparison of the ACTUAL complex Dirichlet projections
in L2-to-uniform operator norm, from physical eigenfunction errors.
No abstract projection is substituted for the original contour operator. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat
local instance dirichletProjectionComparisonH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletProjectionComparisonH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletProjectionComparisonBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletProjectionComparisonBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- Difference of the ACTUAL eigenfunction evaluation functionals costs
only the physical L2 error, with constant exactly one. -/
theorem norm_singularDirichletL2Eigenfunctional_sub_le (g h : UnitDirichletH1) :
    ‖singularDirichletL2Eigenfunctional g-singularDirichletL2Eigenfunctional h‖ ≤
      ‖unitDirichletL2Inclusion (g-h)‖ := by
  have he : singularDirichletL2Eigenfunctional g-singularDirichletL2Eigenfunctional h =
      singularDirichletL2Eigenfunctional (g-h) := by
    apply ContinuousLinearMap.ext
    intro F
    change singularDirichletL2BaseInclusion F g-singularDirichletL2BaseInclusion F h =
      singularDirichletL2BaseInclusion F (g-h)
    rw [map_sub]
  rw [he]
  exact norm_singularDirichletL2Eigenfunctional_le _

/-- A physical eigenfunction comparison controls the SAME ACTUAL contour
projections in the stronger L2-to-continuous-uniform operator norm.
Both potentials may be complex; the actual bilinear masses are retained.
This is the operator step needed to turn high-frequency eigenfunction
estimates into the Dirichlet part of Appendix C.4. -/
theorem norm_singularDirichletContinuousRieszProjection_sub_le
    (q p : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hcq : sphere c r ⊆ singularDirichletResolventSet q)
    (hcp : sphere c r ⊆ singularDirichletResolventSet p)
    (lambda mu : ℂ) (hl : lambda ∈ ball c r) (hmu : mu ∈ ball c r)
    (hoq : ∀ z ∈ ball c r, z ∈ singularDirichletSpectrum q → z = lambda)
    (hop : ∀ z ∈ ball c r, z ∈ singularDirichletSpectrum p → z = mu)
    (hmq : singularDirichletAlgebraicMultiplicity q lambda = 1)
    (hmp : singularDirichletAlgebraicMultiplicity p mu = 1)
    (g h : UnitDirichletH1) (hg0 : g ≠ 0) (hh0 : h ≠ 0)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g)
    (hh : singularDirichletOperator p h = mu • singularDirichletDomainInclusion h) :
    ‖singularDirichletContinuousRieszProjection q c r-singularDirichletContinuousRieszProjection p c r‖ ≤
      (‖unitDirichletL2Inclusion g‖/‖singularDirichletDomainInclusion g g‖)*
        ‖unitDirichletContinuousInclusion (g-h)‖+
      (‖unitDirichletL2Inclusion (g-h)‖/‖singularDirichletDomainInclusion g g‖+
        ((‖unitDirichletL2Inclusion g‖+‖unitDirichletL2Inclusion h‖)*‖unitDirichletL2Inclusion (g-h)‖)*
          ‖unitDirichletL2Inclusion h‖/
          (‖singularDirichletDomainInclusion g g‖*‖singularDirichletDomainInclusion h h‖))*
            ‖unitDirichletContinuousInclusion h‖ := by
  rw [singularDirichletContinuousRieszProjection_eq_rankOne q c r hr hcq lambda hl hoq hmq g hg0 hg,
    singularDirichletContinuousRieszProjection_eq_rankOne p c r hr hcp mu hmu hop hmp h hh0 hh]
  have hmassg := singularDirichlet_bilinear_mass_ne_zero_of_simple_isolated q c r hr hcq lambda hl hoq hmq g hg0 hg
  have hmassh := singularDirichlet_bilinear_mass_ne_zero_of_simple_isolated p c r hr hcp mu hmu hop hmp h hh0 hh
  have hb := NLS.FunctionalAnalysis.norm_rankOneKernel_sub_le
    (singularDirichletL2Eigenfunctional g) (singularDirichletL2Eigenfunctional h)
    (unitDirichletContinuousInclusion g) (unitDirichletContinuousInclusion h)
    (singularDirichletDomainInclusion g g) (singularDirichletDomainInclusion h h) hmassg hmassh
  rw [← map_sub] at hb
  apply hb.trans
  gcongr
  · exact norm_singularDirichletL2Eigenfunctional_le g
  · exact norm_singularDirichletL2Eigenfunctional_sub_le g h
  · exact norm_singularDirichlet_bilinear_mass_sub_le g h
  · exact norm_singularDirichletL2Eigenfunctional_le h

end NLS.KdV
