import NLS.KdV.SingularDirichletRieszCoefficient
import NLS.KdV.SingularDirichletRieszL2
import NLS.KdV.SingularDirichletPhysicalPairing
import NLS.Fourier.UnitDirichletContinuous

/-! The ACTUAL Dirichlet contour projection from full physical L2 into
the closed-interval UNIFORM norm, with its exact physical rank-one kernel. -/
noncomputable section
open Set Metric MeasureTheory
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat
local instance dirichletRieszKernelH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletRieszKernelH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletRieszKernelBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletRieszKernelBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- Evaluation against the physical eigenfunction on ALL ordinary L2 data. -/
def singularDirichletL2Eigenfunctional (g : UnitDirichletH1) : IntervalL2 →L[ℂ] ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ g).comp singularDirichletL2BaseInclusion

/-- Its bound uses the exact physical L2 norm with constant one. -/
theorem norm_singularDirichletL2Eigenfunctional_le (g : UnitDirichletH1) :
    ‖singularDirichletL2Eigenfunctional g‖ ≤ ‖unitDirichletL2Inclusion g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro F
  exact (norm_singularDirichletL2BaseInclusion_pairing_le F g).trans_eq (mul_comm _ _)

/-- Native bilinear mass changes continuously in the PHYSICAL L2 norm,
with the exact elementary product bound. -/
theorem norm_singularDirichlet_bilinear_mass_sub_le (g h : UnitDirichletH1) :
    ‖singularDirichletDomainInclusion g g-singularDirichletDomainInclusion h h‖ ≤
      (‖unitDirichletL2Inclusion g‖+‖unitDirichletL2Inclusion h‖)*‖unitDirichletL2Inclusion (g-h)‖ := by
  have he : singularDirichletDomainInclusion g g-singularDirichletDomainInclusion h h =
      singularDirichletDomainInclusion (g-h) g+singularDirichletDomainInclusion h (g-h) := by
    simp only [map_sub,_root_.sub_apply]
    ring
  have h1 := norm_singularDirichletL2BaseInclusion_pairing_le (unitDirichletL2Inclusion (g-h)) g
  have h2 := norm_singularDirichletL2BaseInclusion_pairing_le (unitDirichletL2Inclusion h) (g-h)
  rw [singularDirichletL2BaseInclusion_domain] at h1 h2
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

/-- The same original contour integral takes values in the exact physical
continuous representatives, in their closed-interval supremum norm. -/
def singularDirichletContinuousRieszProjection
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    IntervalL2 →L[ℂ] C(Icc (0:ℝ) 1,ℂ) :=
  unitDirichletContinuousInclusion.comp
    ((singularDirichletRieszToH1 q c r).comp singularDirichletL2BaseInclusion)

/-- The uniform-norm realization is a representative of the IDENTICAL
actual physical L2 contour projection, on EVERY physical L2 input. -/
theorem singularDirichletContinuousRieszProjection_representative
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (F : IntervalL2) :
    singularDirichletL2RieszProjection q c r F =ᵐ[volume.restrict (Ioc 0 1)]
      NLS.LinearVolterra.extend (singularDirichletContinuousRieszProjection q c r F) := by
  filter_upwards [unitDirichletL2Inclusion_representative
    (singularDirichletRieszToH1 q c r (singularDirichletL2BaseInclusion F)),
    ae_restrict_mem measurableSet_Ioc] with x hx hxi
  have ht : x ∈ Icc (0:ℝ) 1 := ⟨hxi.1.le,hxi.2⟩
  have he := NLS.LinearVolterra.extend_coe
    (singularDirichletContinuousRieszProjection q c r F) ⟨x,ht⟩
  exact hx.trans he.symm

/-- The ACTUAL strong projection is exactly the rank-one physical kernel
operator. The denominator is the actual nonzero complex bilinear mass. -/
theorem singularDirichletContinuousRieszProjection_eq_rankOne
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (lambda : ℂ)
    (hl : lambda ∈ ball c r)
    (honly : ∀ z ∈ ball c r, z ∈ singularDirichletSpectrum q → z = lambda)
    (hm : singularDirichletAlgebraicMultiplicity q lambda = 1)
    (g : UnitDirichletH1) (hg0 : g ≠ 0)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g) :
    singularDirichletContinuousRieszProjection q c r =
      ((singularDirichletDomainInclusion g g)⁻¹ • singularDirichletL2Eigenfunctional g).smulRight
        (unitDirichletContinuousInclusion g) := by
  apply ContinuousLinearMap.ext
  intro F
  change unitDirichletContinuousInclusion (singularDirichletRieszToH1 q c r
    (singularDirichletL2BaseInclusion F)) =
      ((singularDirichletDomainInclusion g g)⁻¹*singularDirichletL2BaseInclusion F g) •
        unitDirichletContinuousInclusion g
  rw [singularDirichletRieszToH1_eq_pairing_smul q c r hr hc lambda hl honly hm g hg0 hg,
    map_smul,div_eq_mul_inv,mul_comm]

/-- The pointwise kernel uses the literal ORIGINAL physical integrals.
It holds at EVERY point of the CLOSED interval, not merely almost everywhere. -/
theorem singularDirichletContinuousRieszProjection_apply_integral
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (lambda : ℂ)
    (hl : lambda ∈ ball c r)
    (honly : ∀ z ∈ ball c r, z ∈ singularDirichletSpectrum q → z = lambda)
    (hm : singularDirichletAlgebraicMultiplicity q lambda = 1)
    (g : UnitDirichletH1) (hg0 : g ≠ 0)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g)
    (F : IntervalL2) (x : Icc (0:ℝ) 1) :
    singularDirichletContinuousRieszProjection q c r F x =
      ((∫ y in (0:ℝ)..1, F y*unitDirichletRepresentative g y)/
        (∫ y in (0:ℝ)..1, unitDirichletRepresentative g y*unitDirichletRepresentative g y))*
          unitDirichletRepresentative g x.val := by
  change unitDirichletContinuousInclusion (singularDirichletRieszToH1 q c r
    (singularDirichletL2BaseInclusion F)) x = _
  rw [singularDirichletRieszToH1_eq_pairing_smul q c r hr hc lambda hl honly hm g hg0 hg,
    map_smul,ContinuousMap.smul_apply]
  change (singularDirichletL2BaseInclusion F g/singularDirichletDomainInclusion g g)*
    unitDirichletRepresentative g x.val = _
  rw [singularDirichletL2BaseInclusion_representative_pairing,
    singularDirichletDomainInclusion_representative_pairing]

/-- The actual L2-to-uniform operator bound has precisely the physical
norm and bilinear-mass denominator needed for projection comparison. -/
theorem norm_singularDirichletContinuousRieszProjection_le
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (lambda : ℂ)
    (hl : lambda ∈ ball c r)
    (honly : ∀ z ∈ ball c r, z ∈ singularDirichletSpectrum q → z = lambda)
    (hm : singularDirichletAlgebraicMultiplicity q lambda = 1)
    (g : UnitDirichletH1) (hg0 : g ≠ 0)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g) :
    ‖singularDirichletContinuousRieszProjection q c r‖ ≤
      ‖unitDirichletL2Inclusion g‖*‖unitDirichletContinuousInclusion g‖/
        ‖singularDirichletDomainInclusion g g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro F
  change ‖unitDirichletContinuousInclusion (singularDirichletRieszToH1 q c r
    (singularDirichletL2BaseInclusion F))‖ ≤ _
  rw [singularDirichletRieszToH1_eq_pairing_smul q c r hr hc lambda hl honly hm g hg0 hg,
    map_smul,norm_smul,norm_div]
  calc
    _ ≤ (‖F‖*‖unitDirichletL2Inclusion g‖)/‖singularDirichletDomainInclusion g g‖*
        ‖unitDirichletContinuousInclusion g‖ := by
      gcongr
      exact norm_singularDirichletL2BaseInclusion_pairing_le F g
    _ = _ := by ring

end NLS.KdV
