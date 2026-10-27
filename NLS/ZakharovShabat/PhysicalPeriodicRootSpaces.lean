import NLS.FunctionalAnalysis.LinearPMapRootSpace
import NLS.ZakharovShabat.PhysicalPeriodicSpectrum
import NLS.ZakharovShabat.RootSpaces

/-! # Full root chains of the actual physical period-two operator -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Original coefficient root chains use precisely the generic domain-to-base recursion. -/
theorem periodicRootSpace_eq_pencilRootSpace {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (n : ℕ) :
    periodicRootSpace hp φ z n =
      pencilRootSpace domainInclusion.toLinearMap (spectralPencil hp φ z).toLinearMap n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [periodicRootSpace,pencilRootSpace,ih]

/-- The exact coefficient-to-physical base-space isomorphism. -/
def periodicPhysicalBaseEquiv : PairSpace 2 ≃ₗ[ℂ] SourceCirclePairL2 :=
  (CoeffPair.toMax 2).symm.toLinearEquiv.trans sourceCircleSynthesis.toLinearEquiv

/-- Actual physical root chains require membership in the actual H1 operator domain at each step. -/
def physicalPeriodicRootSpace (φ : CoeffPair 2) (z : ℂ) : ℕ → Submodule ℂ SourceCirclePairL2 :=
  linearPMapRootSpace (physicalPeriodicOperator φ) z

/-- Full physical generalized eigenspace, defined independently of the coefficient root spaces. -/
def physicalPeriodicRootSpaceTop (φ : CoeffPair 2) (z : ℂ) : Submodule ℂ SourceCirclePairL2 :=
  linearPMapRootSpaceTop (physicalPeriodicOperator φ) z

theorem mem_physicalPeriodicRootSpaceTop (φ : CoeffPair 2) (z : ℂ) (x : SourceCirclePairL2) :
    x ∈ physicalPeriodicRootSpaceTop φ z ↔ ∃ n, x ∈ physicalPeriodicRootSpace φ z n :=
  mem_linearPMapRootSpaceTop _ _ x

/-- The exact physical and original coefficient pencils preserve every finite root-chain level. -/
theorem mem_physicalPeriodicRootSpace_iff (φ : CoeffPair 2) (z : ℂ) (n : ℕ) (x : PairSpace 2) :
    periodicPhysicalBaseEquiv x ∈ physicalPeriodicRootSpace φ z n ↔
      x ∈ periodicRootSpace (by simp) (CoeffPair.toMax 2 φ) z n := by
  let d : Domain 2 ≃ₗ[ℂ] (physicalPeriodicOperator φ).domain :=
    (WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm.toLinearEquiv.trans physicalPeriodicDomainEquiv
  have hι (a : Domain 2) :
      ((physicalPeriodicOperator φ).domain.subtype (d a)) = periodicPhysicalBaseEquiv (domainInclusion a) := by
    change sourceCircleSynthesis ((CoeffPair.toMax 2).symm (domainInclusion
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2)
        ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm a)))) =
      sourceCircleSynthesis ((CoeffPair.toMax 2).symm (domainInclusion a))
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hP (a : Domain 2) : linearPMapPencil (physicalPeriodicOperator φ) z (d a) =
      periodicPhysicalBaseEquiv (spectralPencil (by simp) (CoeffPair.toMax 2 φ) z a) := by
    change linearPMapPencil (physicalPeriodicOperator φ) z (physicalPeriodicDomainEquiv
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm a)) = _
    rw [physicalPeriodicPencil_intertwining]
    change sourceCircleSynthesis ((CoeffPair.toMax 2).symm
      (spectralPencil (by simp) (CoeffPair.toMax 2 φ) z
        ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2)
          ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm a)))) =
      sourceCircleSynthesis ((CoeffPair.toMax 2).symm
        (spectralPencil (by simp) (CoeffPair.toMax 2 φ) z a))
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [periodicRootSpace_eq_pencilRootSpace]
  exact (pencilRootSpace_equiv domainInclusion.toLinearMap
    (spectralPencil (by simp) (CoeffPair.toMax 2 φ) z).toLinearMap
    (physicalPeriodicOperator φ).domain.subtype (linearPMapPencil (physicalPeriodicOperator φ) z)
    d periodicPhysicalBaseEquiv hι hP n x).symm

/-- The physical root space is exactly the image of the original root space, at every chain length. -/
theorem physicalPeriodicRootSpace_eq_map (φ : CoeffPair 2) (z : ℂ) (n : ℕ) :
    physicalPeriodicRootSpace φ z n =
      (periodicRootSpace (by simp) (CoeffPair.toMax 2 φ) z n).map periodicPhysicalBaseEquiv.toLinearMap := by
  ext x
  obtain ⟨a,rfl⟩ := periodicPhysicalBaseEquiv.surjective x
  rw [mem_physicalPeriodicRootSpace_iff]
  constructor
  · intro ha
    exact ⟨a,ha,rfl⟩
  · rintro ⟨b,hb,he⟩
    exact periodicPhysicalBaseEquiv.injective he ▸ hb

/-- The full physical root space contains exactly the transported original generalized eigenvectors. -/
theorem physicalPeriodicRootSpaceTop_eq_map (φ : CoeffPair 2) (z : ℂ) :
    physicalPeriodicRootSpaceTop φ z =
      (periodicRootSpaceTop (by simp) (CoeffPair.toMax 2 φ) z).map periodicPhysicalBaseEquiv.toLinearMap := by
  change (⨆ n : ℕ, physicalPeriodicRootSpace φ z n) = _
  rw [periodicRootSpaceTop,Submodule.map_iSup]
  exact iSup_congr (physicalPeriodicRootSpace_eq_map φ z)

theorem physicalPeriodicRootSpaceTop_le_domain (φ : CoeffPair 2) (z : ℂ) :
    physicalPeriodicRootSpaceTop φ z ≤ (physicalPeriodicOperator φ).domain :=
  linearPMapRootSpaceTop_le_domain _ _

/-- Physical Jordan chains stabilize at some finite length. -/
theorem exists_physicalPeriodicRootSpace_eq_top (φ : CoeffPair 2) (z : ℂ) :
    ∃ n : ℕ, physicalPeriodicRootSpace φ z n = physicalPeriodicRootSpaceTop φ z := by
  obtain ⟨n,hn⟩ := exists_periodicRootSpace_eq_top (by simp) (CoeffPair.toMax 2 φ) z
  exact ⟨n,by rw [physicalPeriodicRootSpace_eq_map,physicalPeriodicRootSpaceTop_eq_map,hn]⟩

theorem finiteDimensional_physicalPeriodicRootSpaceTop (φ : CoeffPair 2) (z : ℂ) :
    FiniteDimensional ℂ (physicalPeriodicRootSpaceTop φ z) := by
  rw [physicalPeriodicRootSpaceTop_eq_map]
  let : FiniteDimensional ℂ (periodicRootSpaceTop (by simp) (CoeffPair.toMax 2 φ) z) :=
    finiteDimensional_periodicRootSpaceTop (by simp) (CoeffPair.toMax 2 φ) z
  infer_instance

end NLS.ZakharovShabat
