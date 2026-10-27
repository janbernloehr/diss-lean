import NLS.ZakharovShabat.SourceParityRootChains
import NLS.ZakharovShabat.UnitParityResolvent

/-! # Actual classical signed Jordan chains on the full unit-interval domains -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- Physical unit-interval conjugacy preserves every chain level of the actual partial operator. -/
theorem mem_unitParityRootSpace_iff (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0)
    (r : ℤ) (z : ℂ) (n : ℕ) (x : sourceParitySubspace (p := 2) r) :
    sourceParityUnitEquiv r x ∈ linearPMapRootSpace (unitParityOperator φ hφ r) z n ↔
      x ∈ sourceParityRootSpace (by simp) φ hφ r z n :=
  (pencilRootSpace_equiv (sourceParityDomainInclusion r).toLinearMap
    (sourceParitySpectralPencil (by simp) φ hφ r z).toLinearMap
    (unitParityOperator φ hφ r).domain.subtype (linearPMapPencil (unitParityOperator φ hφ r) z)
    (unitParityDomainEquiv r) (sourceParityUnitEquiv r).toLinearEquiv
    (unitParityDomainEquiv_coe r) (unitParityPencil_intertwining φ hφ r z) n x).symm

/-- Finite physical signed root chains are defined from the actual classical operator pencil. -/
def classicalSignedRootSpace (u : IntervalPairL2) (r : ℤ) (z : ℂ) : ℕ → Submodule ℂ IntervalPairL2 :=
  linearPMapRootSpace (classicalSignedOperator u r) z

/-- The full generalized eigenspace is the union of finite actual classical chains. -/
def classicalSignedRootSpaceTop (u : IntervalPairL2) (r : ℤ) (z : ℂ) : Submodule ℂ IntervalPairL2 :=
  linearPMapRootSpaceTop (classicalSignedOperator u r) z

theorem mem_classicalSignedRootSpaceTop (u : IntervalPairL2) (r : ℤ) (z : ℂ) (x : IntervalPairL2) :
    x ∈ classicalSignedRootSpaceTop u r z ↔ ∃ n, x ∈ classicalSignedRootSpace u r z n :=
  mem_linearPMapRootSpaceTop _ _ x

/-- The actual classical chains are exactly the physically restricted original parity chains. -/
theorem classicalSignedRootSpace_eq_map (u : IntervalPairL2) (r : ℤ) (z : ℂ) (n : ℕ) :
    classicalSignedRootSpace u r z n =
      (sourceParityRootSpace (by simp) (periodOnePair (sourcePhysicalL2Equiv.symm u))
        (periodOnePotential_mem _) r z n).map (sourceParityUnitEquiv r).toLinearEquiv.toLinearMap := by
  ext x
  obtain ⟨a,rfl⟩ := (sourceParityUnitEquiv r).surjective x
  change sourceParityUnitEquiv r a ∈ linearPMapRootSpace
    (unitParityOperator (periodOnePair (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) r) z n ↔ _
  rw [mem_unitParityRootSpace_iff]
  constructor
  · intro ha
    exact ⟨a,ha,rfl⟩
  · rintro ⟨b,hb,he⟩
    exact (sourceParityUnitEquiv r).injective he ▸ hb

/-- Full physical generalized eigenspaces retain all original generalized vectors of the same parity. -/
theorem classicalSignedRootSpaceTop_eq_map (u : IntervalPairL2) (r : ℤ) (z : ℂ) :
    classicalSignedRootSpaceTop u r z =
      (sourceParityRootSpaceTop (by simp) (periodOnePair (sourcePhysicalL2Equiv.symm u))
        (periodOnePotential_mem _) r z).map (sourceParityUnitEquiv r).toLinearEquiv.toLinearMap := by
  change (⨆ n : ℕ, classicalSignedRootSpace u r z n) =
    (⨆ n : ℕ, sourceParityRootSpace (by simp) (periodOnePair (sourcePhysicalL2Equiv.symm u))
      (periodOnePotential_mem _) r z n).map _
  rw [Submodule.map_iSup]
  exact iSup_congr (classicalSignedRootSpace_eq_map u r z)

theorem classicalSignedRootSpaceTop_le_domain (u : IntervalPairL2) (r : ℤ) (z : ℂ) :
    classicalSignedRootSpaceTop u r z ≤ (classicalSignedOperator u r).domain :=
  linearPMapRootSpaceTop_le_domain _ _

/-- Each actual classical signed generalized eigenspace is finite dimensional. -/
theorem finiteDimensional_classicalSignedRootSpaceTop (u : IntervalPairL2) (r : ℤ) (z : ℂ) :
    FiniteDimensional ℂ (classicalSignedRootSpaceTop u r z) := by
  rw [classicalSignedRootSpaceTop_eq_map]
  let : FiniteDimensional ℂ (sourceParityRootSpaceTop (by simp)
    (periodOnePair (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) r z) :=
    finiteDimensional_sourceParityRootSpaceTop _ _ _ _ _
  infer_instance

theorem exists_classicalSignedRootSpace_eq_top (u : IntervalPairL2) (r : ℤ) (z : ℂ) :
    ∃ n : ℕ, classicalSignedRootSpace u r z n = classicalSignedRootSpaceTop u r z := by
  obtain ⟨n,hn⟩ := exists_sourceParityRootSpace_eq_top (by simp)
    (periodOnePair (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) r z
  exact ⟨n,by rw [classicalSignedRootSpace_eq_map,classicalSignedRootSpaceTop_eq_map,hn]⟩

end NLS.ZakharovShabat
