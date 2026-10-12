import NLS.ZakharovShabat.SourceBoundarySpectra
import NLS.ZakharovShabat.BoundaryRootSpaces

/-!
# Original boundary root chains and algebraic multiplicity

The transported subspaces satisfy exactly the original domain-to-base pencil
recursion, including boundary-domain membership at every step. The full space
consists of all finite chains. Its finite dimension is the original restricted
operator's algebraic multiplicity; a continuous linear equivalence proves
agreement with the auxiliary coefficient theory.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite original boundary root space; its exact pencil recursion is proved below. -/
def sourceBoundaryRootSpace (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ) (n : ℕ) :
    Submodule ℂ (sourceBoundaryBaseSubspace (p := p) b) :=
  (b.rootSpace hp (CoeffPair.toMax p φ) hφ z n).comap (sourceBoundaryBaseEquiv b).toLinearMap

theorem sourceBoundaryBaseEquiv_inclusion (b : BoundaryCondition)
    (a : sourceWeightedBoundarySubspace (p := p) b 1) :
    sourceBoundaryBaseEquiv b (sourceBoundaryInclusion b a) = b.inclusion (sourceBoundaryDomainEquiv b a) := by
  change sourceBoundaryBaseEquiv b ((sourceBoundaryBaseEquiv b).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem sourceBoundaryBaseEquiv_pencil (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ)
    (a : sourceWeightedBoundarySubspace (p := p) b 1) :
    sourceBoundaryBaseEquiv b (sourceBoundaryPencil b hp φ hφ z a) =
      b.pencil hp (CoeffPair.toMax p φ) hφ z (sourceBoundaryDomainEquiv b a) := by
  change sourceBoundaryBaseEquiv b ((sourceBoundaryBaseEquiv b).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem sourceBoundaryRootSpace_zero (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ) :
    sourceBoundaryRootSpace b hp φ hφ z 0 = ⊥ := by
  ext x
  change sourceBoundaryBaseEquiv b x = 0 ↔ x = 0
  exact map_eq_zero_iff _ (sourceBoundaryBaseEquiv b).injective

/-- Each step uses the actual original boundary domain, pencil, and inclusion. -/
theorem mem_sourceBoundaryRootSpace_succ (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ) (n : ℕ)
    (x : sourceBoundaryBaseSubspace (p := p) b) :
    x ∈ sourceBoundaryRootSpace b hp φ hφ z (n+1) ↔
      ∃ a : sourceWeightedBoundarySubspace (p := p) b 1,
        sourceBoundaryInclusion b a = x ∧ sourceBoundaryPencil b hp φ hφ z a ∈ sourceBoundaryRootSpace b hp φ hφ z n := by
  change sourceBoundaryBaseEquiv b x ∈ b.rootSpace hp (CoeffPair.toMax p φ) hφ z (n+1) ↔ _
  rw [b.mem_rootSpace_succ hp (CoeffPair.toMax p φ) hφ z n (sourceBoundaryBaseEquiv b x)]
  constructor
  · rintro ⟨a,ha,hn⟩
    refine ⟨(sourceBoundaryDomainEquiv b).symm a,?_,?_⟩
    · apply (sourceBoundaryBaseEquiv b).injective
      rw [sourceBoundaryBaseEquiv_inclusion,ContinuousLinearEquiv.apply_symm_apply,ha]
    · change sourceBoundaryBaseEquiv b (sourceBoundaryPencil b hp φ hφ z ((sourceBoundaryDomainEquiv b).symm a)) ∈ b.rootSpace hp (CoeffPair.toMax p φ) hφ z n
      rw [sourceBoundaryBaseEquiv_pencil,ContinuousLinearEquiv.apply_symm_apply]
      exact hn
  · rintro ⟨a,ha,hn⟩
    refine ⟨sourceBoundaryDomainEquiv b a,?_,?_⟩
    · rw [← sourceBoundaryBaseEquiv_inclusion,ha]
    · change sourceBoundaryBaseEquiv b (sourceBoundaryPencil b hp φ hφ z a) ∈ b.rootSpace hp (CoeffPair.toMax p φ) hφ z n at hn
      rwa [sourceBoundaryBaseEquiv_pencil] at hn

/-- The full original root space, consisting of all finite boundary chains. -/
def sourceBoundaryRootSpaceTop (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ) :
    Submodule ℂ (sourceBoundaryBaseSubspace (p := p) b) :=
  (b.rootSpaceTop hp (CoeffPair.toMax p φ) hφ z).comap (sourceBoundaryBaseEquiv b).toLinearMap

theorem mem_sourceBoundaryRootSpaceTop (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ)
    (x : sourceBoundaryBaseSubspace (p := p) b) :
    x ∈ sourceBoundaryRootSpaceTop b hp φ hφ z ↔ ∃ n, x ∈ sourceBoundaryRootSpace b hp φ hφ z n :=
  b.mem_rootSpaceTop hp (CoeffPair.toMax p φ) hφ z (sourceBoundaryBaseEquiv b x)

/-- Coefficient-preserving continuous equivalence of the full root spaces. -/
def sourceBoundaryRootSpaceTopEquiv (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ) :
    sourceBoundaryRootSpaceTop b hp φ hφ z ≃L[ℂ] b.rootSpaceTop hp (CoeffPair.toMax p φ) hφ z :=
  (sourceBoundaryBaseEquiv b).ofSubmodule' _

/-- Algebraic multiplicity is the dimension of the full original root space. -/
def sourceBoundaryAlgebraicMultiplicity (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ) : ℕ :=
  Module.finrank ℂ (sourceBoundaryRootSpaceTop b hp φ hφ z)

/-- Changing the base and domain norms retains every Jordan chain and its dimension. -/
theorem sourceBoundaryAlgebraicMultiplicity_eq (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ) :
    sourceBoundaryAlgebraicMultiplicity b hp φ hφ z = b.algebraicMultiplicity hp (CoeffPair.toMax p φ) hφ z :=
  (sourceBoundaryRootSpaceTopEquiv b hp φ hφ z).toLinearEquiv.finrank_eq

theorem finiteDimensional_sourceBoundaryRootSpaceTop (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ) :
    FiniteDimensional ℂ (sourceBoundaryRootSpaceTop b hp φ hφ z) := by
  let := b.finiteDimensional_rootSpaceTop hp (CoeffPair.toMax p φ) hφ z
  exact FiniteDimensional.of_injective (V₂ := b.rootSpaceTop hp (CoeffPair.toMax p φ) hφ z)
    (sourceBoundaryRootSpaceTopEquiv b hp φ hφ z).toLinearMap
    (sourceBoundaryRootSpaceTopEquiv b hp φ hφ z).injective

/-- The actual restricted-pencil recursion, with original norms on both spaces. -/
theorem sourceBoundaryRootSpace_succ (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ) (n : ℕ) :
    sourceBoundaryRootSpace b hp φ hφ z (n+1) =
      ((sourceBoundaryRootSpace b hp φ hφ z n).comap
        (sourceBoundaryPencil b hp φ hφ z).toLinearMap).map (sourceBoundaryInclusion b).toLinearMap := by
  ext x
  rw [mem_sourceBoundaryRootSpace_succ]
  simp only [Submodule.mem_map, Submodule.mem_comap]
  exact exists_congr (fun _ => and_comm)

/-- All sufficiently long original root chains lie in one finite level. -/
theorem exists_sourceBoundaryRootSpace_eq_top (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ) :
    ∃ n : ℕ, sourceBoundaryRootSpace b hp φ hφ z n = sourceBoundaryRootSpaceTop b hp φ hφ z := by
  obtain ⟨n,hn⟩ := b.exists_rootSpace_eq_top hp (CoeffPair.toMax p φ) hφ z
  refine ⟨n,?_⟩
  unfold sourceBoundaryRootSpace sourceBoundaryRootSpaceTop
  rw [hn]

/-- Algebraic multiplicity is positive exactly at the actual restricted spectral points. -/
theorem sourceBoundaryAlgebraicMultiplicity_pos_iff (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (z : ℂ) :
    0 < sourceBoundaryAlgebraicMultiplicity b hp φ hφ z ↔ z ∈ sourceBoundarySpectrum b hp φ hφ := by
  rw [sourceBoundaryAlgebraicMultiplicity_eq,sourceBoundarySpectrum_eq]
  exact b.algebraicMultiplicity_pos_iff hp (CoeffPair.toMax p φ) hφ z

end NLS.ZakharovShabat
