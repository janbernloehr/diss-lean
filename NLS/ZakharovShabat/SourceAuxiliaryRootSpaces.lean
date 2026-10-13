import NLS.ZakharovShabat.SourceAuxiliarySpectra
import NLS.ZakharovShabat.AuxiliaryRootSpaces

/-!
# Original auxiliary root chains and algebraic multiplicity

The transported subspaces satisfy exactly the original domain-to-base pencil
recursion, including auxiliary-domain membership at every step. The full space
consists of all finite chains. Its finite dimension is the original restricted
operator's algebraic multiplicity; a continuous linear equivalence proves
agreement with the auxiliary coefficient theory.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite original auxiliary root space; its exact pencil recursion is proved below. -/
def sourceAuxiliaryRootSpace (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ) (n : ℕ) :
    Submodule ℂ (auxiliarySourceSpace (p := p) b) :=
  (b.auxiliaryRootSpace hp (CoeffPair.toMax p φ) hφ z n).comap (sourceAuxiliaryBaseEquiv b).toLinearMap

theorem sourceAuxiliaryBaseEquiv_inclusion (b : BoundaryCondition)
    (a : sourceWeightedAuxiliarySubspace (p := p) b 1) :
    sourceAuxiliaryBaseEquiv b (sourceAuxiliaryInclusion b a) = b.auxiliaryInclusion (sourceAuxiliaryDomainEquiv b a) := by
  rfl

theorem sourceAuxiliaryBaseEquiv_pencil (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ)
    (a : sourceWeightedAuxiliarySubspace (p := p) b 1) :
    sourceAuxiliaryBaseEquiv b (sourceAuxiliaryPencil b hp φ hφ z a) =
      b.auxiliaryPencil hp (CoeffPair.toMax p φ) hφ z (sourceAuxiliaryDomainEquiv b a) := by
  rw [sourceAuxiliaryPencil_eq_conj]
  change sourceAuxiliaryBaseEquiv b ((sourceAuxiliaryBaseEquiv b).symm _) = _
  exact (sourceAuxiliaryBaseEquiv b).apply_symm_apply _

theorem sourceAuxiliaryRootSpace_zero (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ) :
    sourceAuxiliaryRootSpace b hp φ hφ z 0 = ⊥ := by
  ext x
  change sourceAuxiliaryBaseEquiv b x = 0 ↔ x = 0
  exact map_eq_zero_iff _ (sourceAuxiliaryBaseEquiv b).injective

/-- Each step uses the actual original auxiliary domain, pencil, and inclusion. -/
theorem mem_sourceAuxiliaryRootSpace_succ (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ) (n : ℕ)
    (x : auxiliarySourceSpace (p := p) b) :
    x ∈ sourceAuxiliaryRootSpace b hp φ hφ z (n+1) ↔
      ∃ a : sourceWeightedAuxiliarySubspace (p := p) b 1,
        sourceAuxiliaryInclusion b a = x ∧ sourceAuxiliaryPencil b hp φ hφ z a ∈ sourceAuxiliaryRootSpace b hp φ hφ z n := by
  change sourceAuxiliaryBaseEquiv b x ∈ b.auxiliaryRootSpace hp (CoeffPair.toMax p φ) hφ z (n+1) ↔ _
  rw [b.mem_auxiliaryRootSpace_succ hp (CoeffPair.toMax p φ) hφ z n (sourceAuxiliaryBaseEquiv b x)]
  constructor
  · rintro ⟨a,ha,hn⟩
    refine ⟨(sourceAuxiliaryDomainEquiv b).symm a,?_,?_⟩
    · apply (sourceAuxiliaryBaseEquiv b).injective
      rw [sourceAuxiliaryBaseEquiv_inclusion,ContinuousLinearEquiv.apply_symm_apply,ha]
    · change sourceAuxiliaryBaseEquiv b (sourceAuxiliaryPencil b hp φ hφ z ((sourceAuxiliaryDomainEquiv b).symm a)) ∈ b.auxiliaryRootSpace hp (CoeffPair.toMax p φ) hφ z n
      rw [sourceAuxiliaryBaseEquiv_pencil,ContinuousLinearEquiv.apply_symm_apply]
      exact hn
  · rintro ⟨a,ha,hn⟩
    refine ⟨sourceAuxiliaryDomainEquiv b a,?_,?_⟩
    · rw [← sourceAuxiliaryBaseEquiv_inclusion,ha]
    · change sourceAuxiliaryBaseEquiv b (sourceAuxiliaryPencil b hp φ hφ z a) ∈ b.auxiliaryRootSpace hp (CoeffPair.toMax p φ) hφ z n at hn
      rwa [sourceAuxiliaryBaseEquiv_pencil] at hn

/-- The full original root space, consisting of all finite auxiliary chains. -/
def sourceAuxiliaryRootSpaceTop (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ) :
    Submodule ℂ (auxiliarySourceSpace (p := p) b) :=
  (b.auxiliaryRootSpaceTop hp (CoeffPair.toMax p φ) hφ z).comap (sourceAuxiliaryBaseEquiv b).toLinearMap

theorem mem_sourceAuxiliaryRootSpaceTop (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ)
    (x : auxiliarySourceSpace (p := p) b) :
    x ∈ sourceAuxiliaryRootSpaceTop b hp φ hφ z ↔ ∃ n, x ∈ sourceAuxiliaryRootSpace b hp φ hφ z n :=
  b.mem_auxiliaryRootSpaceTop hp (CoeffPair.toMax p φ) hφ z (sourceAuxiliaryBaseEquiv b x)

/-- Coefficient-preserving continuous equivalence of the full root spaces. -/
def sourceAuxiliaryRootSpaceTopEquiv (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ) :
    sourceAuxiliaryRootSpaceTop b hp φ hφ z ≃L[ℂ] b.auxiliaryRootSpaceTop hp (CoeffPair.toMax p φ) hφ z :=
  (sourceAuxiliaryBaseEquiv b).ofSubmodule' _

/-- Algebraic multiplicity is the dimension of the full original root space. -/
def sourceAuxiliaryAlgebraicMultiplicity (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ) : ℕ :=
  Module.finrank ℂ (sourceAuxiliaryRootSpaceTop b hp φ hφ z)

/-- Changing the base and domain norms retains every Jordan chain and its dimension. -/
theorem sourceAuxiliaryAlgebraicMultiplicity_eq (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ) :
    sourceAuxiliaryAlgebraicMultiplicity b hp φ hφ z = b.auxiliaryAlgebraicMultiplicity hp (CoeffPair.toMax p φ) hφ z :=
  (sourceAuxiliaryRootSpaceTopEquiv b hp φ hφ z).toLinearEquiv.finrank_eq

theorem finiteDimensional_sourceAuxiliaryRootSpaceTop (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ) :
    FiniteDimensional ℂ (sourceAuxiliaryRootSpaceTop b hp φ hφ z) := by
  let := b.finiteDimensional_auxiliaryRootSpaceTop hp (CoeffPair.toMax p φ) hφ z
  exact FiniteDimensional.of_injective (V₂ := b.auxiliaryRootSpaceTop hp (CoeffPair.toMax p φ) hφ z)
    (sourceAuxiliaryRootSpaceTopEquiv b hp φ hφ z).toLinearMap
    (sourceAuxiliaryRootSpaceTopEquiv b hp φ hφ z).injective

/-- The actual restricted-pencil recursion, with original norms on both spaces. -/
theorem sourceAuxiliaryRootSpace_succ (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ) (n : ℕ) :
    sourceAuxiliaryRootSpace b hp φ hφ z (n+1) =
      ((sourceAuxiliaryRootSpace b hp φ hφ z n).comap
        (sourceAuxiliaryPencil b hp φ hφ z).toLinearMap).map (sourceAuxiliaryInclusion b).toLinearMap := by
  ext x
  rw [mem_sourceAuxiliaryRootSpace_succ]
  simp only [Submodule.mem_map, Submodule.mem_comap]
  exact exists_congr (fun _ => and_comm)

/-- All sufficiently long original root chains lie in one finite level. -/
theorem exists_sourceAuxiliaryRootSpace_eq_top (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ) :
    ∃ n : ℕ, sourceAuxiliaryRootSpace b hp φ hφ z n = sourceAuxiliaryRootSpaceTop b hp φ hφ z := by
  obtain ⟨n,hn⟩ := b.exists_auxiliaryRootSpace_eq_top hp (CoeffPair.toMax p φ) hφ z
  refine ⟨n,?_⟩
  unfold sourceAuxiliaryRootSpace sourceAuxiliaryRootSpaceTop
  rw [hn]

/-- Algebraic multiplicity is positive exactly at the actual restricted spectral points. -/
theorem sourceAuxiliaryAlgebraicMultiplicity_pos_iff (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ) :
    0 < sourceAuxiliaryAlgebraicMultiplicity b hp φ hφ z ↔ z ∈ sourceAuxiliarySpectrum b hp φ hφ := by
  rw [sourceAuxiliaryAlgebraicMultiplicity_eq,sourceAuxiliarySpectrum_eq]
  exact b.auxiliaryAlgebraicMultiplicity_pos_iff hp (CoeffPair.toMax p φ) hφ z

end NLS.ZakharovShabat
