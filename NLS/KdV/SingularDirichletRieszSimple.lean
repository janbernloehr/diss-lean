import NLS.KdV.SingularDirichletRieszRange
import NLS.KdV.SingularDirichletRieszDomain
import NLS.KdV.SingularDirichletNormalizedEigenfunction

/-! A circle enclosing exactly one ACTUAL simple native Dirichlet eigenvalue
has precisely its normalized eigenfunction line as spectral range. This
uses the actual full algebraic root space, not geometric simplicity alone. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
local instance dirichletRieszSimpleH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletRieszSimpleH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletRieszSimpleBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletRieszSimpleBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- A single enclosed actual spectral value gives its ENTIRE algebraic root
space as the actual Riesz range, even when that value is multiple. -/
theorem singularDirichletRieszProjection_range_eq_single_root
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (lambda : ℂ)
    (hl : lambda ∈ ball c r)
    (honly : ∀ z ∈ ball c r, z ∈ singularDirichletSpectrum q → z = lambda) :
    (singularDirichletRieszProjection q c r).range = singularDirichletRootSpaceTop q lambda := by
  obtain ⟨a,ha⟩ := singularDirichletResolventSet_nonempty q
  rw [singularDirichletRieszProjection_range_eq_roots q c r hr hc a ha]
  apply le_antisymm
  · apply iSup_le
    intro z
    by_cases hz : z.val = lambda
    · rw [hz]
    · have hzres : z.val ∈ singularDirichletResolventSet q := by
        by_contra hnot
        exact hz (honly z.val z.property hnot)
      rw [singularDirichletRootSpaceTop_eq_bot_of_mem_resolvent q z.val hzres]
      exact bot_le
  · exact le_iSup (fun z : ball c r => singularDirichletRootSpaceTop q z.val) ⟨lambda,hl⟩

/-- The source's simple spectral projection has a genuinely normalized native
generator. Its range is EXACTLY that line in the FULL original dual base. -/
theorem exists_singularDirichletRiesz_normalized_generator
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (lambda : ℂ)
    (hl : lambda ∈ ball c r)
    (honly : ∀ z ∈ ball c r, z ∈ singularDirichletSpectrum q → z = lambda)
    (hm : singularDirichletAlgebraicMultiplicity q lambda = 1) :
    ∃ g : UnitDirichletH1,
      singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g ∧
      ‖unitDirichletL2Inclusion g‖ = 1 ∧
      (∫ x in (0:ℝ)..1, ‖unitDirichletRepresentative g x‖^2) = 1 ∧
      (singularDirichletRieszProjection q c r).range =
        Submodule.span ℂ {singularDirichletDomainInclusion g} := by
  obtain ⟨g,hg,hn,hi,hspan⟩ := exists_singularDirichlet_simple_normalized_generator q lambda hm
  exact ⟨g,hg,hn,hi,(singularDirichletRieszProjection_range_eq_single_root q c r hr hc lambda hl honly).trans hspan⟩

/-- At an actual simple isolated root, every native spectral projection image
is a scalar multiple of its actual domain eigenfunction, inside H1 itself. -/
theorem exists_singularDirichletDomainRiesz_amplitude
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (lambda : ℂ)
    (hl : lambda ∈ ball c r)
    (honly : ∀ z ∈ ball c r, z ∈ singularDirichletSpectrum q → z = lambda)
    (hm : singularDirichletAlgebraicMultiplicity q lambda = 1)
    (g : UnitDirichletH1) (hg0 : g ≠ 0)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g)
    (f : UnitDirichletH1) :
    ∃ nu : ℂ, singularDirichletDomainRieszProjection q c r f = nu • g := by
  have hrange := (singularDirichletRieszProjection_range_eq_single_root q c r hr hc lambda hl honly).trans
    (singularDirichletRootSpaceTop_eq_span_of_multiplicity_one q lambda hm g hg0 hg)
  have hmem : singularDirichletRieszProjection q c r (singularDirichletDomainInclusion f) ∈
      Submodule.span ℂ {singularDirichletDomainInclusion g} := by
    rw [← hrange]
    exact ⟨singularDirichletDomainInclusion f,rfl⟩
  obtain ⟨nu,hnu⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨nu,singularDirichletDomainInclusion_injective ?_⟩
  change singularDirichletDomainInclusion
    (singularDirichletRieszToH1 q c r (singularDirichletDomainInclusion f)) =
      singularDirichletDomainInclusion (nu • g)
  rw [← singularDirichletRieszToH1_inclusion q c r hr.le hc,map_smul]
  exact hnu.symm

/-- The actual projected native residual has precisely the scalar spectral
factor used before source identity (31); this is an operator identity on the
FULL native domain, with the actual Riesz projection and actual eigenvector. -/
theorem singularDirichletRiesz_projected_residual
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q)
    (lambda mu nu : ℂ) (f g : UnitDirichletH1)
    (hg : singularDirichletOperator q g = mu • singularDirichletDomainInclusion g)
    (hproj : singularDirichletDomainRieszProjection q c r f = nu • g) :
    singularDirichletRieszProjection q c r
      (singularDirichletOperator q f-lambda • singularDirichletDomainInclusion f) =
        (nu*(mu-lambda)) • singularDirichletDomainInclusion g := by
  rw [map_sub,map_smul]
  rw [← singularDirichletOperator_riesz_intertwine q c r hr hc f,
    singularDirichletRieszToH1_inclusion q c r hr hc]
  change singularDirichletOperator q (singularDirichletDomainRieszProjection q c r f)-
    lambda • singularDirichletDomainInclusion (singularDirichletDomainRieszProjection q c r f) = _
  rw [hproj,map_smul,map_smul,hg]
  module

end NLS.KdV
