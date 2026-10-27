import NLS.ZakharovShabat.ClassicalSignedRootSpaces
import NLS.ZakharovShabat.PhysicalPeriodicMultiplicity
import NLS.ZakharovShabat.ClassicalSignedDiscriminant

/-! # Actual classical signed algebraic multiplicities and their physical sum -/
noncomputable section
set_option autoImplicit false
namespace NLS.ZakharovShabat

/-- Actual signed algebraic multiplicity counts the full physical generalized eigenspace. -/
def classicalSignedAlgebraicMultiplicity (u : IntervalPairL2) (r : ℤ) (z : ℂ) : ℕ :=
  Module.finrank ℂ (classicalSignedRootSpaceTop u r z)

/-- The independently defined physical multiplicity equals the original parity root dimension. -/
theorem classicalSignedAlgebraicMultiplicity_eq (u : IntervalPairL2) (r : ℤ) (z : ℂ) :
    classicalSignedAlgebraicMultiplicity u r z =
      parityAlgebraicMultiplicity (by simp) (periodOnePotential (sourcePhysicalL2Equiv.symm u)) r z := by
  rw [classicalSignedAlgebraicMultiplicity,classicalSignedRootSpaceTop_eq_map]
  calc
    _ = Module.finrank ℂ (sourceParityRootSpaceTop (by simp)
        (periodOnePair (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) r z) :=
      (Submodule.equivMapOfInjective (sourceParityUnitEquiv r).toLinearEquiv.toLinearMap
        (sourceParityUnitEquiv r).injective _).finrank_eq.symm
    _ = _ := (sourceParityRootSpaceTopEquiv (by simp)
      (periodOnePair (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) r z).finrank_eq

theorem classicalSignedAlgebraicMultiplicity_pos_iff (u : IntervalPairL2) (r : ℤ) (z : ℂ) :
    0 < classicalSignedAlgebraicMultiplicity u r z ↔ z ∈ classicalSignedSpectrum u r := by
  rw [classicalSignedAlgebraicMultiplicity_eq,mem_classicalSignedSpectrum_iff_multiplicity_pos]

theorem classicalSignedAlgebraicMultiplicity_eq_zero_iff (u : IntervalPairL2) (r : ℤ) (z : ℂ) :
    classicalSignedAlgebraicMultiplicity u r z = 0 ↔ z ∈ classicalSignedResolventSet u r := by
  have h := classicalSignedAlgebraicMultiplicity_pos_iff u r z
  simpa only [classicalSignedSpectrum,Set.mem_compl_iff,not_not,Nat.not_lt,Nat.le_zero] using not_congr h

/-- The actual period-two multiplicity is the sum of the two actual classical signed multiplicities. -/
theorem physicalPeriodicAlgebraicMultiplicity_eq_classicalSigned_sum (u : IntervalPairL2) (z : ℂ) :
    physicalPeriodicAlgebraicMultiplicity (periodOnePair (sourcePhysicalL2Equiv.symm u)) z =
      classicalSignedAlgebraicMultiplicity u 0 z + classicalSignedAlgebraicMultiplicity u 1 z := by
  rw [physicalPeriodicAlgebraicMultiplicity_eq,classicalSignedAlgebraicMultiplicity_eq,
    classicalSignedAlgebraicMultiplicity_eq]
  exact periodicAlgebraicMultiplicity_eq_parity_sum (by simp) _ (periodOnePotential_mem _) z

/-- A periodic spectral point retains the entire physical period-two multiplicity. -/
theorem classicalPeriodicMultiplicity_eq_full_of_mem (u : IntervalPairL2) (z : ℂ)
    (hz : z ∈ classicalSignedSpectrum u 0) :
    classicalSignedAlgebraicMultiplicity u 0 z =
      physicalPeriodicAlgebraicMultiplicity (periodOnePair (sourcePhysicalL2Equiv.symm u)) z := by
  have hzero : classicalSignedAlgebraicMultiplicity u 1 z = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro h
    exact Set.disjoint_left.mp (disjoint_classicalSignedSpectra u) hz
      ((classicalSignedAlgebraicMultiplicity_pos_iff u 1 z).mp h)
  rw [physicalPeriodicAlgebraicMultiplicity_eq_classicalSigned_sum,hzero,add_zero]

/-- An antiperiodic spectral point retains the entire physical period-two multiplicity. -/
theorem classicalAntiperiodicMultiplicity_eq_full_of_mem (u : IntervalPairL2) (z : ℂ)
    (hz : z ∈ classicalSignedSpectrum u 1) :
    classicalSignedAlgebraicMultiplicity u 1 z =
      physicalPeriodicAlgebraicMultiplicity (periodOnePair (sourcePhysicalL2Equiv.symm u)) z := by
  have hzero : classicalSignedAlgebraicMultiplicity u 0 z = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro h
    exact Set.disjoint_left.mp (disjoint_classicalSignedSpectra u)
      ((classicalSignedAlgebraicMultiplicity_pos_iff u 0 z).mp h) hz
  rw [physicalPeriodicAlgebraicMultiplicity_eq_classicalSigned_sum,hzero,zero_add]

/-- At zero potential, each lattice point contributes two to its actual physical parity and zero to the other. -/
theorem classicalSignedAlgebraicMultiplicity_zero (r n : ℤ) :
    classicalSignedAlgebraicMultiplicity 0 r ((Real.pi : ℂ)*n) = if n % 2 = r % 2 then 2 else 0 := by
  rw [classicalSignedAlgebraicMultiplicity_eq]
  have hφ : periodOnePotential (sourcePhysicalL2Equiv.symm (0 : IntervalPairL2)) = 0 := by
    change (CoeffPair.toMax 2) (periodOnePair (sourcePhysicalL2Equiv.symm (0 : IntervalPairL2))) = 0
    simp only [map_zero]
  rw [hφ,parityAlgebraicMultiplicity_zero]

end NLS.ZakharovShabat
