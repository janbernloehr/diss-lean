import NLS.KdV.SingularDirichletAlgebraicMultiplicity
import NLS.Fourier.UnitDirichletL2

/-! Actual native Dirichlet eigenfunctions with the SOURCE interval L2
normalization, for every complex potential and every actual spectral value. -/
noncomputable section
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat
local instance normalizedDirichletH1NormedGroup : NormedAddCommGroup UnitDirichletH1 :=
  unitDirichletSubspace.normedAddCommGroup
local instance normalizedDirichletH1NormedSpace : NormedSpace ℂ UnitDirichletH1 :=
  unitDirichletSubspace.normedSpace

/-- Every actual native complex eigenvalue has an eigenfunction normalized
in the literal L2([0,1],C) norm, retaining the ENTIRE zero-trace H1 domain. -/
theorem exists_singularDirichlet_normalized_eigenfunction
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ)
    (hl : lambda ∈ singularDirichletSpectrum q) :
    ∃ g : UnitDirichletH1,
      singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g ∧
      ‖unitDirichletL2Inclusion g‖ = 1 ∧
      (∫ x in (0:ℝ)..1, ‖unitDirichletRepresentative g x‖^2) = 1 := by
  obtain ⟨f,hf0,hf⟩ := (mem_singularDirichletSpectrum_iff q lambda).mp hl
  have hfL2 : unitDirichletL2Inclusion f ≠ 0 := by
    intro he
    exact hf0 (unitDirichletL2Inclusion_injective (by simpa only [map_zero] using he))
  have hn : ‖unitDirichletL2Inclusion f‖ ≠ 0 := norm_ne_zero_iff.mpr hfL2
  let a : ℂ := ((‖unitDirichletL2Inclusion f‖)⁻¹:ℝ)
  let g : UnitDirichletH1 := a • f
  have hg : ‖unitDirichletL2Inclusion g‖ = 1 := by
    rw [show g = a • f from rfl,map_smul,norm_smul]
    dsimp [a]
    rw [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hn]
  refine ⟨g,?_,hg,?_⟩
  · change singularDirichletOperator q (a • f) = lambda • singularDirichletDomainInclusion (a • f)
    rw [map_smul,map_smul,hf,smul_smul,smul_smul,mul_comm a lambda]
  · rw [← norm_sq_unitDirichletL2Inclusion,hg,one_pow]

/-- At actual algebraic multiplicity one, the ENTIRE native algebraic root
space is the span of ANY nonzero actual eigenfunction's base inclusion.
There is no unaccounted associated-vector direction. -/
theorem singularDirichletRootSpaceTop_eq_span_of_multiplicity_one
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ)
    (hm : singularDirichletAlgebraicMultiplicity q lambda = 1)
    (g : UnitDirichletH1) (hg0 : g ≠ 0)
    (hg : singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g) :
    singularDirichletRootSpaceTop q lambda =
      Submodule.span ℂ {singularDirichletDomainInclusion g} := by
  let := finiteDimensional_singularDirichletRootSpaceTop q lambda
  have hgJ : singularDirichletDomainInclusion g ≠ 0 := by
    intro he
    exact hg0 (singularDirichletDomainInclusion_injective (by simpa only [map_zero] using he))
  have hlevel : singularDirichletDomainInclusion g ∈ singularDirichletRootSpace q lambda 1 := by
    apply (mem_singularDirichletRootSpace_succ q lambda 0 _).mpr
    refine ⟨g,rfl,?_⟩
    change singularDirichletPencil q lambda g = 0
    exact (singularDirichletPencil_eq_zero_iff q lambda g).mpr hg
  have htop : singularDirichletDomainInclusion g ∈ singularDirichletRootSpaceTop q lambda :=
    (le_iSup (fun n => singularDirichletRootSpace q lambda n) 1) hlevel
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_le
    (Submodule.span_le.mpr (by simpa only [Set.singleton_subset_iff] using! htop))
  rw [finrank_span_singleton hgJ]
  exact hm.le

/-- The simple native spectral root space has an actual generator with the
source's interval normalization; its span is the FULL algebraic root space. -/
theorem exists_singularDirichlet_simple_normalized_generator
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ)
    (hm : singularDirichletAlgebraicMultiplicity q lambda = 1) :
    ∃ g : UnitDirichletH1,
      singularDirichletOperator q g = lambda • singularDirichletDomainInclusion g ∧
      ‖unitDirichletL2Inclusion g‖ = 1 ∧
      (∫ x in (0:ℝ)..1, ‖unitDirichletRepresentative g x‖^2) = 1 ∧
      singularDirichletRootSpaceTop q lambda =
        Submodule.span ℂ {singularDirichletDomainInclusion g} := by
  have hl := (singularDirichletAlgebraicMultiplicity_pos_iff q lambda).mp (by rw [hm]; omega)
  obtain ⟨g,hg,hn,hi⟩ := exists_singularDirichlet_normalized_eigenfunction q lambda hl
  have hg0 : g ≠ 0 := by
    intro he
    rw [he,map_zero,norm_zero] at hn
    norm_num at hn
  exact ⟨g,hg,hn,hi,singularDirichletRootSpaceTop_eq_span_of_multiplicity_one q lambda hm g hg0 hg⟩

end NLS.KdV
