import NLS.ZakharovShabat.AuxiliaryPhase
import NLS.ZakharovShabat.BoundaryResolvent

/-!
# The auxiliary D and N coefficient spaces

Phase transport constructs the source's closed boundary spaces in the base
norm and at every real Sobolev regularity. The raw coefficients satisfy the
explicit ±i reflection conditions, and domain inclusion respects them.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
namespace BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition)

/-- The auxiliary closed base space corresponding to the ordinary condition b. -/
def auxiliarySpace : Submodule ℂ (PairSpace p) :=
  (space b).map (auxiliaryPhase (Coeff p)).toLinearMap

/-- The source auxiliary space at arbitrary real Sobolev regularity. -/
def auxiliaryWeightedSpace (s : ℝ) :
    Submodule ℂ (WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p) :=
  (match b with
    | .dirichlet => weightedDirichletSubspace s
    | .neumann => weightedNeumannSubspace s).map
      (auxiliaryPhase (WeightedCoeff (Weight.sobolev s) p)).toLinearMap

/-- The one-derivative auxiliary boundary domain. -/
abbrev auxiliaryDomain : Submodule ℂ (Domain p) := auxiliaryWeightedSpace b 1

/-- Phase transport is an isometry onto the actual auxiliary base space. -/
def auxiliaryBaseEquiv : space (p := p) b ≃ₗᵢ[ℂ] auxiliarySpace (p := p) b :=
  LinearIsometryEquiv.submoduleMap (space b) (auxiliaryPhase (Coeff p))

/-- Phase transport is an isometry onto the actual auxiliary operator domain. -/
def auxiliaryDomainEquiv : domain (p := p) b ≃ₗᵢ[ℂ] auxiliaryDomain (p := p) b :=
  LinearIsometryEquiv.submoduleMap (domain b) (auxiliaryPhase (ScalarDomain p))

theorem mem_auxiliarySpace (f : PairSpace p) :
    f ∈ auxiliarySpace b ↔ (auxiliaryPhase (Coeff p)).symm f ∈ space b := by
  constructor
  · rintro ⟨g,hg,rfl⟩
    simpa [smul_smul] using hg
  · intro hf
    exact ⟨(auxiliaryPhase (Coeff p)).symm f,hf,(auxiliaryPhase (Coeff p)).apply_symm_apply f⟩

theorem mem_auxiliaryDomain (f : Domain p) :
    f ∈ auxiliaryDomain b ↔ (auxiliaryPhase (ScalarDomain p)).symm f ∈ domain b := by
  change f ∈ (domain b).map (auxiliaryPhase (ScalarDomain p)).toLinearMap ↔ _
  constructor
  · rintro ⟨g,hg,hgf⟩
    rw [← hgf]
    change (auxiliaryPhase (ScalarDomain p)).symm (auxiliaryPhase (ScalarDomain p) g) ∈ domain b
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact hg
  · intro hf
    exact ⟨(auxiliaryPhase (ScalarDomain p)).symm f,hf,(auxiliaryPhase (ScalarDomain p)).apply_symm_apply f⟩

/-- The raw coefficient condition in equation (1.11). -/
theorem mem_auxiliaryDirichletSpace (f : PairSpace p) :
    f ∈ auxiliarySpace .dirichlet ↔ ∀ n, f.1 n = -Complex.I*f.2 (-n) := by
  simp only [mem_auxiliarySpace, space, auxiliaryPhase_symm_apply, mem_dirichletSubspace,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, neg_mul]

/-- The raw coefficient condition in equation (1.12). -/
theorem mem_auxiliaryNeumannSpace (f : PairSpace p) :
    f ∈ auxiliarySpace .neumann ↔ ∀ n, f.1 n = Complex.I*f.2 (-n) := by
  simp only [mem_auxiliarySpace, space, auxiliaryPhase_symm_apply, mem_neumannSubspace, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, neg_mul, neg_neg]

/-- The same source phase condition holds at any Sobolev exponent. -/
theorem mem_auxiliaryWeightedSpace (s : ℝ)
    (f : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p) :
    f ∈ auxiliaryWeightedSpace b s ↔
      match b with
      | .dirichlet => ∀ n, f.1.val n = -Complex.I*f.2.val (-n)
      | .neumann => ∀ n, f.1.val n = Complex.I*f.2.val (-n) := by
  have he : f ∈ auxiliaryWeightedSpace b s ↔
      (auxiliaryPhase (WeightedCoeff (Weight.sobolev s) p)).symm f ∈
        (match b with | .dirichlet => weightedDirichletSubspace s | .neumann => weightedNeumannSubspace s) := by
    constructor
    · rintro ⟨g,hg,rfl⟩
      simpa [smul_smul] using hg
    · intro hf
      exact ⟨_,hf,(auxiliaryPhase _).apply_symm_apply f⟩
  rw [he]
  cases b <;> simp

/-- The auxiliary base spaces are closed in the actual coefficient norm. -/
theorem isClosed_auxiliarySpace : IsClosed (auxiliarySpace (p := p) b : Set (PairSpace p)) := by
  have he : (auxiliarySpace (p := p) b : Set (PairSpace p)) =
      (auxiliaryPhase (Coeff p)).symm ⁻¹' (space (p := p) b : Set (PairSpace p)) := by
    ext f
    exact mem_auxiliarySpace b f
  rw [he]
  exact (isClosed_space b).preimage (auxiliaryPhase (Coeff p)).symm.continuous

/-- The auxiliary domain is closed in the one-derivative norm. -/
theorem isClosed_auxiliaryDomain : IsClosed (auxiliaryDomain (p := p) b : Set (Domain p)) := by
  have he : (auxiliaryDomain (p := p) b : Set (Domain p)) =
      (auxiliaryPhase (ScalarDomain p)).symm ⁻¹' (domain (p := p) b : Set (Domain p)) := by
    ext f
    exact mem_auxiliaryDomain b f
  rw [he]
  exact (isClosed_domain b).preimage (auxiliaryPhase (ScalarDomain p)).symm.continuous

/-- Both auxiliary spaces are closed at every real Sobolev regularity. -/
theorem isClosed_auxiliaryWeightedSpace (s : ℝ) :
    IsClosed (auxiliaryWeightedSpace (p := p) b s :
      Set (WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p)) := by
  cases b
  · exact (auxiliaryPhase (WeightedCoeff (Weight.sobolev s) p)).toContinuousLinearEquiv.toHomeomorph.isClosedMap _
      (isClosed_weightedDirichletSubspace s)
  · exact (auxiliaryPhase (WeightedCoeff (Weight.sobolev s) p)).toContinuousLinearEquiv.toHomeomorph.isClosedMap _
      (isClosed_weightedNeumannSubspace s)

/-- The two auxiliary base spaces give the source's complementary decomposition. -/
theorem isCompl_auxiliarySpaces :
    IsCompl (auxiliarySpace (p := p) .dirichlet) (auxiliarySpace (p := p) .neumann) :=
  (Submodule.orderIsoMapComap (auxiliaryPhase (Coeff p)).toLinearEquiv).isCompl_iff.mp isCompl_dirichlet_neumann

/-- The complementary decomposition persists at every real Sobolev regularity. -/
theorem isCompl_auxiliaryWeightedSpaces (s : ℝ) :
    IsCompl (auxiliaryWeightedSpace (p := p) .dirichlet s) (auxiliaryWeightedSpace (p := p) .neumann s) :=
  (Submodule.orderIsoMapComap (auxiliaryPhase (WeightedCoeff (Weight.sobolev s) p)).toLinearEquiv).isCompl_iff.mp
    (isCompl_weightedDirichlet_neumann s)

/-- The actual domain inclusion has the same auxiliary boundary condition in the base norm. -/
theorem inclusion_mem_auxiliary (f : Domain p) :
    domainInclusion f ∈ auxiliarySpace b ↔ f ∈ auxiliaryDomain b := by
  rw [mem_auxiliarySpace, mem_auxiliaryDomain]
  have he : (auxiliaryPhase (Coeff p)).symm (domainInclusion f) =
      domainInclusion ((auxiliaryPhase (ScalarDomain p)).symm f) := by simp
  rw [he]
  exact inclusion_mem b _

end BoundaryCondition
end NLS.ZakharovShabat
