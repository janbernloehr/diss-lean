import NLS.KdV.SingularDirichletRieszSimple
import NLS.KdV.SingularDirichletL2Base

/-! The ACTUAL Dirichlet spectral projection on ordinary physical
L2([0,1],C), induced by the full-dual source resolvent and its original H1 lift. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat
local instance dirichletRieszL2H1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletRieszL2H1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletRieszL2BaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletRieszL2BaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- The actual original projection on the FULL ordinary physical interval L2 space. -/
def singularDirichletL2RieszProjection (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    IntervalL2 →L[ℂ] IntervalL2 :=
  unitDirichletL2Inclusion.comp ((singularDirichletRieszToH1 q c r).comp singularDirichletL2BaseInclusion)

/-- The ordinary L2 projection is exactly the SAME full-base native spectral operator. -/
theorem singularDirichletL2RieszProjection_base
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (F : IntervalL2) :
    singularDirichletL2BaseInclusion (singularDirichletL2RieszProjection q c r F) =
      singularDirichletRieszProjection q c r (singularDirichletL2BaseInclusion F) := by
  change singularDirichletL2BaseInclusion (unitDirichletL2Inclusion
    (singularDirichletRieszToH1 q c r (singularDirichletL2BaseInclusion F))) = _
  rw [singularDirichletL2BaseInclusion_domain,← singularDirichletRieszToH1_inclusion q c r hr hc]

/-- Its restriction to the full native H1 domain is exactly the actual domain projection. -/
theorem singularDirichletL2RieszProjection_domain
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (f : UnitDirichletH1) :
    singularDirichletL2RieszProjection q c r (unitDirichletL2Inclusion f) =
      unitDirichletL2Inclusion (singularDirichletDomainRieszProjection q c r f) := by
  change unitDirichletL2Inclusion (singularDirichletRieszToH1 q c r
    (singularDirichletL2BaseInclusion (unitDirichletL2Inclusion f))) = _
  rw [singularDirichletL2BaseInclusion_domain]
  rfl

/-- The full physical L2 realization is a genuine bounded idempotent. -/
theorem isIdempotentElem_singularDirichletL2RieszProjection
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) :
    IsIdempotentElem (singularDirichletL2RieszProjection q c r) := by
  apply ContinuousLinearMap.ext
  intro F
  apply singularDirichletL2BaseInclusion_injective
  change singularDirichletL2BaseInclusion
    (singularDirichletL2RieszProjection q c r (singularDirichletL2RieszProjection q c r F)) =
      singularDirichletL2BaseInclusion (singularDirichletL2RieszProjection q c r F)
  rw [singularDirichletL2RieszProjection_base q c r hr.le hc,
    singularDirichletL2RieszProjection_base q c r hr.le hc]
  exact congrArg (fun T : UnitDirichletHminus →L[ℂ] UnitDirichletHminus =>
    T (singularDirichletL2BaseInclusion F)) (isIdempotentElem_singularDirichletRieszProjection q c r hr hc)

/-- For an actual simple isolated eigenvalue, the FULL ordinary L2 spectral
range is EXACTLY its actual native eigenfunction line. -/
theorem singularDirichletL2RieszProjection_range_eq_span
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (lambda : ℂ)
    (hl : lambda ∈ ball c r)
    (honly : ∀ z ∈ ball c r, z ∈ singularDirichletSpectrum q → z = lambda)
    (hm : singularDirichletAlgebraicMultiplicity q lambda = 1)
    (g : UnitDirichletH1) (hg0 : g ≠ 0)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g) :
    (singularDirichletL2RieszProjection q c r).range =
      Submodule.span ℂ {unitDirichletL2Inclusion g} := by
  have hrange := (singularDirichletRieszProjection_range_eq_single_root q c r hr hc lambda hl honly).trans
    (singularDirichletRootSpaceTop_eq_span_of_multiplicity_one q lambda hm g hg0 hg)
  apply le_antisymm
  · rintro y ⟨F,rfl⟩
    have hb : singularDirichletRieszProjection q c r (singularDirichletL2BaseInclusion F) ∈
        Submodule.span ℂ {singularDirichletDomainInclusion g} := by
      rw [← hrange]
      exact ⟨singularDirichletL2BaseInclusion F,rfl⟩
    obtain ⟨nu,hnu⟩ := Submodule.mem_span_singleton.mp hb
    have he : singularDirichletL2RieszProjection q c r F = nu • unitDirichletL2Inclusion g := by
      apply singularDirichletL2BaseInclusion_injective
      rw [singularDirichletL2RieszProjection_base q c r hr.le hc,map_smul,
        singularDirichletL2BaseInclusion_domain]
      exact hnu.symm
    change singularDirichletL2RieszProjection q c r F ∈ Submodule.span ℂ {unitDirichletL2Inclusion g}
    rw [he]
    exact Submodule.smul_mem _ nu (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro y hy
    have he : y = unitDirichletL2Inclusion g := hy
    rw [he]
    refine ⟨unitDirichletL2Inclusion g,?_⟩
    apply singularDirichletL2BaseInclusion_injective
    change singularDirichletL2BaseInclusion
      (singularDirichletL2RieszProjection q c r (unitDirichletL2Inclusion g)) =
        singularDirichletL2BaseInclusion (unitDirichletL2Inclusion g)
    rw [singularDirichletL2RieszProjection_base q c r hr.le hc,
      singularDirichletL2BaseInclusion_domain,
      singularDirichletRieszProjection_eigenvector_inside q c r hr hc lambda hl g hg]

/-- The actual source scalar amplitude exists for EVERY physical L2 datum.
Its upper bound is in the ACTUAL physical L2 operator norm, with no
unproved claim of convergence to the free projection. -/
theorem exists_singularDirichletL2Riesz_amplitude_bound
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (lambda : ℂ)
    (hl : lambda ∈ ball c r)
    (honly : ∀ z ∈ ball c r, z ∈ singularDirichletSpectrum q → z = lambda)
    (hm : singularDirichletAlgebraicMultiplicity q lambda = 1)
    (g : UnitDirichletH1)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g)
    (hn : ‖unitDirichletL2Inclusion g‖ = 1) (F : IntervalL2) :
    ∃ nu : ℂ, singularDirichletL2RieszProjection q c r F = nu • unitDirichletL2Inclusion g ∧
      ‖nu‖ ≤ ‖singularDirichletL2RieszProjection q c r‖*‖F‖ := by
  have hg0 : g ≠ 0 := by
    intro he
    rw [he,map_zero,norm_zero] at hn
    norm_num at hn
  have hmem : singularDirichletL2RieszProjection q c r F ∈
      Submodule.span ℂ {unitDirichletL2Inclusion g} := by
    rw [← singularDirichletL2RieszProjection_range_eq_span q c r hr hc lambda hl honly hm g hg0 hg]
    exact ⟨F,rfl⟩
  obtain ⟨nu,hnu⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨nu,hnu.symm,?_⟩
  have hb := (singularDirichletL2RieszProjection q c r).le_opNorm F
  rw [← hnu,norm_smul,hn,mul_one] at hb
  exact hb

end NLS.KdV
