import NLS.KdV.DirichletSineMassBounds
import NLS.KdV.SingularDirichletProjectionComparison

/-! An explicit small-sine-error bound for the ACTUAL Dirichlet source
projection minus the ACTUAL free contour projection in L2-to-uniform norm. -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat
local instance dirichletProjectionFreeH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletProjectionFreeH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace

/-- For the SAME literal source circle, actual simple spectral isolation
and the proved physical sine error imply the quantitative operator bound
40*delta. The free operator is the ACTUAL free contour integral. -/
theorem norm_singularDirichletProjection_sub_free_le_of_sine_error
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (n : ℕ+) (lambda : ℂ)
    (hcq : sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularDirichletResolventSet q)
    (hc0 : sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularDirichletResolventSet 0)
    (hl : lambda ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ))
    (hoq : ∀ z ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ), z ∈ singularDirichletSpectrum q → z = lambda)
    (ho0 : ∀ z ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ), z ∈ singularDirichletSpectrum 0 → z = ((Real.pi:ℂ)*(n:ℕ))^2)
    (hmq : singularDirichletAlgebraicMultiplicity q lambda = 1)
    (hm0 : singularDirichletAlgebraicMultiplicity 0 (((Real.pi:ℂ)*(n:ℕ))^2) = 1)
    (g : UnitDirichletH1) (hg0 : g ≠ 0)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g)
    {delta : ℝ} (hd : 0 ≤ delta) (hdsmall : delta ≤ 1/16)
    (he : ‖unitDirichletContinuousInclusion g-dirichletFreeSineCurve n‖ ≤ delta) :
    ‖singularDirichletContinuousRieszProjection q (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
      singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ ≤ 40*delta := by
  obtain ⟨h,hh0,hh,hhC⟩ := exists_native_freeDirichlet_sine n
  have hr : (0:ℝ) < (n:ℝ) := by exact_mod_cast n.property
  have hcenter : ((Real.pi:ℂ)*(n:ℕ))^2 ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) := mem_ball_self hr
  have hCh : ‖unitDirichletContinuousInclusion h‖ ≤ 1 := by
    rw [hhC]
    exact norm_dirichletFreeSineCurve_le_one n
  have hLh : ‖unitDirichletL2Inclusion h‖ ≤ 1 :=
    (norm_unitDirichletL2Inclusion_le_uniform h).trans hCh
  have hdiffC : ‖unitDirichletContinuousInclusion (g-h)‖ ≤ delta := by rw [map_sub,hhC]; exact he
  have hdiffL : ‖unitDirichletL2Inclusion (g-h)‖ ≤ delta :=
    (norm_unitDirichletL2Inclusion_le_uniform _).trans hdiffC
  obtain ⟨_,hLg,_,_,hMg⟩ := dirichletSineComparison_norm_and_mass_bounds n g hdsmall he
  have hMh : ‖singularDirichletDomainInclusion h h‖ = (1/2:ℝ) := by
    rw [singularDirichlet_mass_of_freeSine n h hhC]
    norm_num
  have hb := norm_singularDirichletContinuousRieszProjection_sub_le q 0 _ _ hr hcq hc0
    lambda _ hl hcenter hoq ho0 hmq hm0 g h hg0 hh0 hg hh
  apply hb.trans
  calc
    _ ≤ (2/(1/4:ℝ))*delta+
        (delta/(1/4:ℝ)+((2+1)*delta)*1/((1/4:ℝ)*(1/2:ℝ)))*1 := by
      gcongr
      exact hMh.ge
    _ = 36*delta := by ring
    _ ≤ 40*delta := by linarith

end NLS.KdV
