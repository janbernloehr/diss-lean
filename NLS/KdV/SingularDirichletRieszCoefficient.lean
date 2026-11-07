import NLS.KdV.SingularDirichletRieszBilinear
import NLS.KdV.SingularDirichletRieszSimple

/-! The ACTUAL simple complex Dirichlet projection coefficient is the
unconjugated native mass pairing divided by the eigenfunction's nonzero
bilinear mass. All full native dual data and the entire H1 domain are retained. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
local instance dirichletRieszCoefficientH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletRieszCoefficientH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletRieszCoefficientBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletRieszCoefficientBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- EVERY full-dual projected datum lies on the actual simple eigenfunction
line INSIDE the original native H1 domain. -/
theorem exists_singularDirichletRieszToH1_amplitude
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (lambda : ℂ)
    (hl : lambda ∈ ball c r)
    (honly : ∀ z ∈ ball c r, z ∈ singularDirichletSpectrum q → z = lambda)
    (hm : singularDirichletAlgebraicMultiplicity q lambda = 1)
    (g : UnitDirichletH1) (hg0 : g ≠ 0)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g)
    (F : UnitDirichletHminus) :
    ∃ nu : ℂ, singularDirichletRieszToH1 q c r F = nu • g := by
  have hrange := (singularDirichletRieszProjection_range_eq_single_root q c r hr hc lambda hl honly).trans
    (singularDirichletRootSpaceTop_eq_span_of_multiplicity_one q lambda hm g hg0 hg)
  have hmem : singularDirichletRieszProjection q c r F ∈
      Submodule.span ℂ {singularDirichletDomainInclusion g} := by
    rw [← hrange]
    exact ⟨F,rfl⟩
  obtain ⟨nu,hnu⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨nu,singularDirichletDomainInclusion_injective ?_⟩
  rw [← singularDirichletRieszToH1_inclusion q c r hr.le hc,map_smul]
  exact hnu.symm

/-- Green symmetry identifies EVERY actual projection coefficient before
division: F(g)=nu*J(g)(g). This is complex bilinear, with no reality premise. -/
theorem singularDirichletRieszToH1_amplitude_pairing
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (lambda : ℂ)
    (hl : lambda ∈ ball c r) (g : UnitDirichletH1)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g)
    (F : UnitDirichletHminus) (nu : ℂ)
    (hnu : singularDirichletRieszToH1 q c r F = nu • g) :
    F g = nu*singularDirichletDomainInclusion g g := by
  calc
    F g = F (singularDirichletRieszToH1 q c r (singularDirichletDomainInclusion g)) := by
      rw [singularDirichletRieszToH1_eigenvector_inside q c r hr hc lambda hl g hg]
    _ = singularDirichletDomainInclusion g (singularDirichletRieszToH1 q c r F) :=
      singularDirichletRieszToH1_bilinear q c r hr.le hc F _
    _ = _ := by rw [hnu,map_smul]; rfl

/-- An ACTUAL algebraically simple isolated complex Dirichlet eigenfunction
cannot have zero bilinear mass. Geometric simplicity alone is not used. -/
theorem singularDirichlet_bilinear_mass_ne_zero_of_simple_isolated
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (lambda : ℂ)
    (hl : lambda ∈ ball c r)
    (honly : ∀ z ∈ ball c r, z ∈ singularDirichletSpectrum q → z = lambda)
    (hm : singularDirichletAlgebraicMultiplicity q lambda = 1)
    (g : UnitDirichletH1) (hg0 : g ≠ 0)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g) :
    singularDirichletDomainInclusion g g ≠ 0 := by
  intro hzero
  let F := singularDirichletDomainInclusion (unitDirichletConjugate g)
  obtain ⟨nu,hnu⟩ := exists_singularDirichletRieszToH1_amplitude q c r hr hc lambda hl honly hm g hg0 hg F
  have he := singularDirichletRieszToH1_amplitude_pairing q c r hr hc lambda hl g hg F nu hnu
  rw [hzero,mul_zero] at he
  have hpos := singularDirichletDomainInclusion_energy_pos g hg0
  have hz : singularDirichletDomainInclusion g (unitDirichletConjugate g) = 0 := by
    rw [singularDirichletDomainInclusion_bilinear]
    exact he
  rw [hz,Complex.zero_re] at hpos
  exact (lt_irrefl 0) hpos

/-- Exact rank-one formula for the ACTUAL full-dual-to-H1 contour operator. -/
theorem singularDirichletRieszToH1_eq_pairing_smul
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (lambda : ℂ)
    (hl : lambda ∈ ball c r)
    (honly : ∀ z ∈ ball c r, z ∈ singularDirichletSpectrum q → z = lambda)
    (hm : singularDirichletAlgebraicMultiplicity q lambda = 1)
    (g : UnitDirichletH1) (hg0 : g ≠ 0)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g)
    (F : UnitDirichletHminus) :
    singularDirichletRieszToH1 q c r F =
      (F g/singularDirichletDomainInclusion g g) • g := by
  obtain ⟨nu,hnu⟩ := exists_singularDirichletRieszToH1_amplitude q c r hr hc lambda hl honly hm g hg0 hg F
  have he := singularDirichletRieszToH1_amplitude_pairing q c r hr hc lambda hl g hg F nu hnu
  rw [he,mul_div_cancel_right₀ _ (singularDirichlet_bilinear_mass_ne_zero_of_simple_isolated
    q c r hr hc lambda hl honly hm g hg0 hg)]
  exact hnu

end NLS.KdV
