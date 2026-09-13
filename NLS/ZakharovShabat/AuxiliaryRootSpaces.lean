import NLS.ZakharovShabat.AuxiliarySpectrum

/-!
# Generalized root spaces of the auxiliary operators

Root chains use the actual auxiliary pencil and domain inclusion at every step.
Phase conjugation identifies these chains, and hence their algebraic
multiplicities, with ordinary boundary chains at the transformed potential.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition)

/-- Inclusion of the actual auxiliary operator domain in its base space. -/
def auxiliaryInclusion : auxiliaryDomain (p := p) b →L[ℂ] auxiliarySpace (p := p) b :=
  (domainInclusion.comp (auxiliaryDomain b).subtypeL).codRestrict _
    (fun f => (inclusion_mem_auxiliary b f.val).mpr f.property)

theorem auxiliaryInclusion_conjugate (f : domain (p := p) b) :
    auxiliaryInclusion b (auxiliaryDomainEquiv b f) = auxiliaryBaseEquiv b (inclusion b f) := by
  apply Subtype.ext
  exact domainInclusion_auxiliaryPhase f.val

/-- Recursive generalized eigenspaces of the actual auxiliary pencil. -/
def auxiliaryRootSpace (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) (z : ℂ) :
    ℕ → Submodule ℂ (auxiliarySpace (p := p) b)
  | 0 => ⊥
  | n + 1 => ((auxiliaryRootSpace hp φ hφ z n).comap
      (auxiliaryPencil b hp φ hφ z).toLinearMap).map (auxiliaryInclusion b).toLinearMap

@[simp] theorem auxiliaryRootSpace_zero (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) : auxiliaryRootSpace b hp φ hφ z 0 = ⊥ := rfl

theorem mem_auxiliaryRootSpace_succ (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) (n : ℕ) (x : auxiliarySpace (p := p) b) :
    x ∈ auxiliaryRootSpace b hp φ hφ z (n + 1) ↔
      ∃ f : auxiliaryDomain (p := p) b, auxiliaryInclusion b f = x ∧
        auxiliaryPencil b hp φ hφ z f ∈ auxiliaryRootSpace b hp φ hφ z n := by
  simp only [auxiliaryRootSpace, Submodule.mem_map, Submodule.mem_comap]
  exact exists_congr fun _ => and_comm

/-- Phase conjugation preserves every finite generalized root chain. -/
theorem mem_auxiliaryRootSpace_conjugate (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) (n : ℕ) (x : space (p := p) b) :
    auxiliaryBaseEquiv b x ∈ auxiliaryRootSpace b hp φ hφ z n ↔
      x ∈ rootSpace b hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) z n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [mem_auxiliaryRootSpace_succ, mem_rootSpace_succ]
    constructor
    · rintro ⟨f, hf, hn⟩
      obtain ⟨g, rfl⟩ := (auxiliaryDomainEquiv (p := p) b).surjective f
      rw [auxiliaryInclusion_conjugate] at hf
      rw [auxiliaryPencil_conjugate] at hn
      exact ⟨g, (auxiliaryBaseEquiv b).injective hf, (ih _).mp hn⟩
    · rintro ⟨f, hf, hn⟩
      refine ⟨auxiliaryDomainEquiv b f, ?_, ?_⟩
      · rw [auxiliaryInclusion_conjugate, hf]
      · rw [auxiliaryPencil_conjugate]
        exact (ih _).mpr hn

theorem auxiliaryRootSpace_mono (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) : Monotone (auxiliaryRootSpace b hp φ hφ z) := by
  intro m n h x hx
  obtain ⟨y, rfl⟩ := (auxiliaryBaseEquiv (p := p) b).surjective x
  rw [mem_auxiliaryRootSpace_conjugate] at hx ⊢
  exact rootSpace_mono b hp _ _ z h hx

/-- The full space of finite auxiliary generalized root chains. -/
def auxiliaryRootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) (z : ℂ) :
    Submodule ℂ (auxiliarySpace (p := p) b) := ⨆ n : ℕ, auxiliaryRootSpace b hp φ hφ z n

theorem mem_auxiliaryRootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) (x : auxiliarySpace (p := p) b) :
    x ∈ auxiliaryRootSpaceTop b hp φ hφ z ↔ ∃ n, x ∈ auxiliaryRootSpace b hp φ hφ z n :=
  Submodule.mem_iSup_of_directed _ (auxiliaryRootSpace_mono b hp φ hφ z).directed_le

theorem mem_auxiliaryRootSpaceTop_conjugate (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) (x : space (p := p) b) :
    auxiliaryBaseEquiv b x ∈ auxiliaryRootSpaceTop b hp φ hφ z ↔
      x ∈ rootSpaceTop b hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) z := by
  simp only [mem_auxiliaryRootSpaceTop, mem_rootSpaceTop, mem_auxiliaryRootSpace_conjugate]

theorem map_rootSpaceTop_auxiliary (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) :
    (rootSpaceTop b hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) z).map
      (auxiliaryBaseEquiv b).toLinearEquiv.toLinearMap = auxiliaryRootSpaceTop b hp φ hφ z := by
  ext x
  obtain ⟨y, rfl⟩ := (auxiliaryBaseEquiv (p := p) b).surjective x
  rw [mem_auxiliaryRootSpaceTop_conjugate]
  constructor
  · rintro ⟨a, ha, he⟩
    exact (auxiliaryBaseEquiv b).injective he ▸ ha
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- An equivalence of actual full root spaces, including all Jordan chains. -/
def auxiliaryRootSpaceTopEquiv (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) :
    rootSpaceTop b hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) z ≃ₗ[ℂ]
      auxiliaryRootSpaceTop b hp φ hφ z :=
  (auxiliaryBaseEquiv b).toLinearEquiv.ofSubmodules _ _ (map_rootSpaceTop_auxiliary b hp φ hφ z)

theorem finiteDimensional_auxiliaryRootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) : FiniteDimensional ℂ (auxiliaryRootSpaceTop b hp φ hφ z) := by
  let := finiteDimensional_rootSpaceTop b hp (auxiliaryPotential φ)
    ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) z
  exact FiniteDimensional.of_injective
    (V₂ := ↥(rootSpaceTop b hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) z))
    (auxiliaryRootSpaceTopEquiv b hp φ hφ z).symm.toLinearMap
    (auxiliaryRootSpaceTopEquiv b hp φ hφ z).symm.injective

theorem exists_auxiliaryRootSpace_eq_top (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) :
    ∃ n : ℕ, auxiliaryRootSpace b hp φ hφ z n = auxiliaryRootSpaceTop b hp φ hφ z := by
  obtain ⟨n, hn⟩ := exists_rootSpace_eq_top b hp (auxiliaryPotential φ)
    ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) z
  refine ⟨n, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := (auxiliaryBaseEquiv (p := p) b).surjective x
  rw [mem_auxiliaryRootSpace_conjugate, mem_auxiliaryRootSpaceTop_conjugate, hn]

theorem finiteDimensional_auxiliaryRootSpace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) (n : ℕ) :
    FiniteDimensional ℂ (auxiliaryRootSpace b hp φ hφ z n) := by
  let := finiteDimensional_auxiliaryRootSpaceTop b hp φ hφ z
  have hle : auxiliaryRootSpace b hp φ hφ z n ≤ auxiliaryRootSpaceTop b hp φ hφ z := le_iSup _ n
  exact FiniteDimensional.of_injective (V₂ := ↥(auxiliaryRootSpaceTop b hp φ hφ z))
    (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

theorem isClosed_auxiliaryRootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) :
    IsClosed (auxiliaryRootSpaceTop b hp φ hφ z : Set (auxiliarySpace (p := p) b)) := by
  let := finiteDimensional_auxiliaryRootSpaceTop b hp φ hφ z
  exact (auxiliaryRootSpaceTop b hp φ hφ z).closed_of_finiteDimensional

/-- Algebraic multiplicity is the dimension of the actual auxiliary full root space. -/
def auxiliaryAlgebraicMultiplicity (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) : ℕ :=
  Module.finrank ℂ (auxiliaryRootSpaceTop b hp φ hφ z)

theorem auxiliaryAlgebraicMultiplicity_eq (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) : auxiliaryAlgebraicMultiplicity b hp φ hφ z =
      algebraicMultiplicity b hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) z :=
  (auxiliaryRootSpaceTopEquiv b hp φ hφ z).finrank_eq.symm

theorem auxiliaryAlgebraicMultiplicity_pos_iff (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) :
    0 < auxiliaryAlgebraicMultiplicity b hp φ hφ z ↔ z ∈ auxiliarySpectrum b hp φ hφ := by
  rw [auxiliaryAlgebraicMultiplicity_eq, auxiliarySpectrum_eq, algebraicMultiplicity_pos_iff]

theorem auxiliaryAlgebraicMultiplicity_eq_zero_iff (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (z : ℂ) :
    auxiliaryAlgebraicMultiplicity b hp φ hφ z = 0 ↔ z ∈ auxiliaryResolventSet b hp φ hφ := by
  rw [auxiliaryAlgebraicMultiplicity_eq, auxiliaryResolventSet_eq, algebraicMultiplicity_eq_zero_iff]

end NLS.ZakharovShabat.BoundaryCondition
