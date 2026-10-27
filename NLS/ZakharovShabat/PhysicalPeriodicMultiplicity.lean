import NLS.ZakharovShabat.PhysicalPeriodicRootSpaces
import NLS.ZakharovShabat.ClassicalSignedEndpointLabels

/-! # Algebraic multiplicity of the actual physical period-two operator -/
noncomputable section
set_option autoImplicit false
open NLS.FunctionalAnalysis NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- Physical algebraic multiplicity is the dimension of the actual full Jordan-chain space. -/
def physicalPeriodicAlgebraicMultiplicity (φ : CoeffPair 2) (z : ℂ) : ℕ :=
  Module.finrank ℂ (physicalPeriodicRootSpaceTop φ z)

/-- Physical and coefficient multiplicities agree through exact root-chain transport. -/
theorem physicalPeriodicAlgebraicMultiplicity_eq (φ : CoeffPair 2) (z : ℂ) :
    physicalPeriodicAlgebraicMultiplicity φ z =
      periodicAlgebraicMultiplicity (by simp) (CoeffPair.toMax 2 φ) z := by
  rw [physicalPeriodicAlgebraicMultiplicity,physicalPeriodicRootSpaceTop_eq_map]
  exact (Submodule.equivMapOfInjective periodicPhysicalBaseEquiv.toLinearMap
    periodicPhysicalBaseEquiv.injective _).finrank_eq.symm

/-- Positive physical algebraic multiplicity is equivalent to the actual bounded-inverse spectrum. -/
theorem physicalPeriodicAlgebraicMultiplicity_pos_iff (φ : CoeffPair 2) (z : ℂ) :
    0 < physicalPeriodicAlgebraicMultiplicity φ z ↔ z ∈ physicalPeriodicSpectrum φ := by
  rw [physicalPeriodicAlgebraicMultiplicity_eq,physicalPeriodicSpectrum_eq]
  exact periodicAlgebraicMultiplicity_pos_iff (by simp) _ _

theorem physicalPeriodicAlgebraicMultiplicity_eq_zero_iff (φ : CoeffPair 2) (z : ℂ) :
    physicalPeriodicAlgebraicMultiplicity φ z = 0 ↔ z ∈ physicalPeriodicResolventSet φ := by
  have h := physicalPeriodicAlgebraicMultiplicity_pos_iff φ z
  simpa only [physicalPeriodicSpectrum,Set.mem_compl_iff,not_not,Nat.not_lt,Nat.le_zero] using not_congr h

/-- The paired physical endpoint labels count precisely the physical full Jordan-chain dimension. -/
theorem physicalPeriodicEndpoints_count_multiplicity (u : IntervalPairL2) (z : ℂ) :
    (∑ᶠ n : ℤ, ({physicalPeriodicLeft u n,physicalPeriodicRight u n} : Multiset ℂ).count z) =
      physicalPeriodicAlgebraicMultiplicity (periodOnePair (sourcePhysicalL2Equiv.symm u)) z := by
  rw [physicalPeriodicAlgebraicMultiplicity_eq,
    (physicalPeriodicEndpoints_eq_source u).1,(physicalPeriodicEndpoints_eq_source u).2]
  exact (canonicalPeriodicEndpoints_spec (by simp) (by norm_num)
    (periodOnePotential (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _)).1.global_multiplicity z

/-- The analytic characteristic zero order equals the actual physical algebraic multiplicity. -/
theorem analyticOrderAt_l2Discriminant_eq_physicalMultiplicity (u : IntervalPairL2) (z : ℂ) :
    analyticOrderAt (fun w => l2Discriminant u w ^ 2 - 4) z =
      (physicalPeriodicAlgebraicMultiplicity (periodOnePair (sourcePhysicalL2Equiv.symm u)) z : ℕ∞) := by
  rw [physicalPeriodicEndpoints_order,physicalPeriodicEndpoints_count_multiplicity]

theorem analyticOrderNatAt_l2Discriminant_eq_physicalMultiplicity (u : IntervalPairL2) (z : ℂ) :
    analyticOrderNatAt (fun w => l2Discriminant u w ^ 2 - 4) z =
      physicalPeriodicAlgebraicMultiplicity (periodOnePair (sourcePhysicalL2Equiv.symm u)) z := by
  rw [← (physicalPeriodicEndpoints_spec u).multiplicity,physicalPeriodicEndpoints_count_multiplicity]

/-- The free physical operator has algebraic multiplicity two at every signed lattice index. -/
theorem physicalPeriodicAlgebraicMultiplicity_zero (n : ℤ) :
    physicalPeriodicAlgebraicMultiplicity 0 ((Real.pi : ℂ)*n) = 2 := by
  rw [physicalPeriodicAlgebraicMultiplicity_eq,map_zero]
  exact periodicAlgebraicMultiplicity_zero (by simp) n

end NLS.ZakharovShabat
