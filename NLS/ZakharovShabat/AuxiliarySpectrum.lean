import NLS.ZakharovShabat.AuxiliarySpaces
import NLS.ZakharovShabat.BoundarySpectrum
import NLS.ZakharovShabat.BoundaryRootSpaces

/-!
# The actual auxiliary restricted pencils and spectra

For a Neumann-reflected potential, L(φ) preserves each auxiliary boundary
space. Its restricted z-L pencil is conjugate to the ordinary boundary pencil
at (iφ₋,-iφ₊). The auxiliary resolvent set is defined by actual bijectivity;
its spectral equivalence, discreteness, and eigenvector criterion are proved.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
namespace BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition)

/-- The actual operator preserves the auxiliary condition for Neumann-reflected potentials. -/
theorem operator_mem_auxiliary (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace)
    (f : Domain p) (hf : f ∈ auxiliaryDomain b) : operator hp φ f ∈ auxiliarySpace b := by
  obtain ⟨g,hg,rfl⟩ := hf
  change operator hp φ (auxiliaryPhase (ScalarDomain p) g) ∈ auxiliarySpace b
  rw [operator_auxiliaryPhase]
  exact ⟨operator hp (auxiliaryPotential φ) g,
    operator_mem b hp _ ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) g hg,rfl⟩

/-- The actual bounded domain-to-base auxiliary operator. -/
def auxiliaryOperator (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) :
    auxiliaryDomain (p := p) b →L[ℂ] auxiliarySpace (p := p) b :=
  ((operator hp φ).comp (auxiliaryDomain b).subtypeL).codRestrict _
    (fun f => operator_mem_auxiliary b hp φ hφ f.val f.property)

/-- Restrict z-L itself to the actual auxiliary domain and base space. -/
def auxiliaryPencil (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) (z : ℂ) :
    auxiliaryDomain (p := p) b →L[ℂ] auxiliarySpace (p := p) b :=
  ((spectralPencil hp φ z).comp (auxiliaryDomain b).subtypeL).codRestrict _ (fun f =>
    (auxiliarySpace b).sub_mem
      ((auxiliarySpace b).smul_mem z ((inclusion_mem_auxiliary b f.val).mpr f.property))
      (operator_mem_auxiliary b hp φ hφ f.val f.property))

/-- The auxiliary restricted pencil is conjugate to the ordinary restricted pencil. -/
theorem auxiliaryPencil_conjugate (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace)
    (z : ℂ) (f : domain (p := p) b) :
    auxiliaryPencil b hp φ hφ z (auxiliaryDomainEquiv b f) =
      auxiliaryBaseEquiv b (pencil b hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) z f) := by
  apply Subtype.ext
  exact spectralPencil_auxiliaryPhase hp φ z f.val

/-- The auxiliary resolvent set is defined by bijectivity of its restricted pencil. -/
def auxiliaryResolventSet (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) : Set ℂ :=
  {z | Function.Bijective (auxiliaryPencil b hp φ hφ z)}

private theorem bijective_iff_of_intertwining {A B C D : Type*} (e : A ≃ B) (d : C ≃ D)
    (f : A → C) (g : B → D) (h : ∀ a, g (e a) = d (f a)) : Function.Bijective g ↔ Function.Bijective f := by
  have he : g ∘ e = d ∘ f := funext h
  rw [← e.bijective_comp g, he]
  exact d.comp_bijective f

/-- Actual auxiliary and conjugated ordinary pencils have the same resolvent set. -/
theorem auxiliaryResolventSet_eq (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) :
    auxiliaryResolventSet b hp φ hφ =
      resolventSet b hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) := by
  ext z
  change Function.Bijective (auxiliaryPencil b hp φ hφ z) ↔ Function.Bijective (pencil b hp _ _ z)
  exact bijective_iff_of_intertwining (auxiliaryDomainEquiv b).toEquiv (auxiliaryBaseEquiv b).toEquiv
    (pencil b hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) z)
    (auxiliaryPencil b hp φ hφ z) (auxiliaryPencil_conjugate b hp φ hφ z)

/-- The spectrum of the actual auxiliary restricted operator. -/
def auxiliarySpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) : Set ℂ :=
  (auxiliaryResolventSet b hp φ hφ)ᶜ

/-- Spectral equivalence follows from the proved restricted-pencil conjugation. -/
theorem auxiliarySpectrum_eq (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) :
    auxiliarySpectrum b hp φ hφ =
      spectrum b hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) := by
  rw [auxiliarySpectrum, auxiliaryResolventSet_eq, spectrum]

/-- The auxiliary spectrum is closed. -/
theorem isClosed_auxiliarySpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) :
    IsClosed (auxiliarySpectrum b hp φ hφ) := by
  rw [auxiliarySpectrum_eq]
  exact isClosed_spectrum b hp _ _

/-- The auxiliary spectrum has only finitely many values in bounded sets. -/
theorem finite_auxiliarySpectrum_inter_of_isBounded (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) {K : Set ℂ} (hK : Bornology.IsBounded K) :
    Set.Finite (auxiliarySpectrum b hp φ hφ ∩ K) := by
  rw [auxiliarySpectrum_eq]
  exact finite_spectrum_inter_of_isBounded b hp _ _ hK

/-- The actual auxiliary spectrum is discrete, for every finite Banach exponent. -/
theorem discreteTopology_auxiliarySpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) :
    DiscreteTopology (auxiliarySpectrum b hp φ hφ) := by
  rw [auxiliarySpectrum_eq]
  exact discreteTopology_spectrum b hp _ _

/-- Every auxiliary spectral value has a nonzero eigenvector in the actual auxiliary domain. -/
theorem mem_auxiliarySpectrum_iff_exists_eigenvector (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) : z ∈ auxiliarySpectrum b hp φ hφ ↔
      ∃ f : Domain p, f ∈ auxiliaryDomain b ∧ f ≠ 0 ∧ operator hp φ f = z • domainInclusion f := by
  rw [auxiliarySpectrum_eq, mem_spectrum_iff_exists_eigenvector]
  constructor
  · rintro ⟨f,hf,hf0,he⟩
    refine ⟨auxiliaryPhase (ScalarDomain p) f,⟨f,hf,rfl⟩,?_,(eigenvector_auxiliaryPhase_iff hp φ z f).mpr he⟩
    exact (auxiliaryPhase (ScalarDomain p)).map_ne_zero_iff.mpr hf0
  · rintro ⟨f,hf,hf0,he⟩
    let g := (auxiliaryPhase (ScalarDomain p)).symm f
    have hg : auxiliaryPhase (ScalarDomain p) g = f := (auxiliaryPhase (ScalarDomain p)).apply_symm_apply f
    refine ⟨g,(mem_auxiliaryDomain b f).mp hf,?_,?_⟩
    · intro h
      apply hf0
      rw [← hg, h, map_zero]
    · exact (eigenvector_auxiliaryPhase_iff hp φ z g).mp (by simpa only [hg] using he)

end BoundaryCondition
end NLS.ZakharovShabat
