import NLS.ZakharovShabat.PhysicalPeriodicSpectrum
import NLS.ZakharovShabat.PhysicalPeriodicEndpoints

/-! # Actual classical signed spectra are the physical monodromy trace levels -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.ZakharovShabat

/-- The periodic physical operator has spectrum exactly at physical trace level two. -/
theorem mem_classicalPeriodicSpectrum_iff_discriminant (u : IntervalPairL2) (z : ℂ) :
    z ∈ classicalSignedSpectrum u 0 ↔ l2Discriminant u z = 2 := by
  rw [mem_classicalSignedSpectrum_iff_multiplicity_pos]
  have h := (canonicalDiscriminant_parity_levels
    (periodOnePotential (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) z).1
  rw [canonicalDiscriminant_eq_l2_source,sourcePhysicalL2_equiv_symm] at h
  exact h.symm

/-- The antiperiodic physical operator has spectrum exactly at physical trace level minus two. -/
theorem mem_classicalAntiperiodicSpectrum_iff_discriminant (u : IntervalPairL2) (z : ℂ) :
    z ∈ classicalSignedSpectrum u 1 ↔ l2Discriminant u z = -2 := by
  rw [mem_classicalSignedSpectrum_iff_multiplicity_pos]
  have h := (canonicalDiscriminant_parity_levels
    (periodOnePotential (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) z).2
  rw [canonicalDiscriminant_eq_l2_source,sourcePhysicalL2_equiv_symm] at h
  exact h.symm

/-- The two actual signed spectra are disjoint even for complex physical potentials. -/
theorem disjoint_classicalSignedSpectra (u : IntervalPairL2) :
    Disjoint (classicalSignedSpectrum u 0) (classicalSignedSpectrum u 1) := by
  apply Set.disjoint_left.mpr
  intro z he ho
  rw [mem_classicalPeriodicSpectrum_iff_discriminant] at he
  rw [mem_classicalAntiperiodicSpectrum_iff_discriminant,he] at ho
  norm_num at ho

/-- The actual physical period-two spectrum is characterized by its physical discriminant. -/
theorem mem_physicalPeriodicSpectrum_iff_discriminant (u : IntervalPairL2) (z : ℂ) :
    z ∈ physicalPeriodicSpectrum (periodOnePair (sourcePhysicalL2Equiv.symm u)) ↔
      l2Discriminant u z ^ 2 = 4 := by
  rw [physicalPeriodicSpectrum_eq]
  have h := canonicalDiscriminant_sq_eq_four_iff
    (periodOnePotential (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) z
  rw [canonicalDiscriminant_eq_l2_source,sourcePhysicalL2_equiv_symm] at h
  exact h.symm

/-- The intrinsic physical endpoint labels exhaust precisely the actual bounded-inverse spectrum. -/
theorem physicalPeriodicSpectrum_iff_endpoint (u : IntervalPairL2) (z : ℂ) :
    z ∈ physicalPeriodicSpectrum (periodOnePair (sourcePhysicalL2Equiv.symm u)) ↔
      ∃ n : ℤ, physicalPeriodicLeft u n = z ∨ physicalPeriodicRight u n = z := by
  rw [mem_physicalPeriodicSpectrum_iff_discriminant,physicalPeriodicEndpoints_exhaustive]

/-- The original periodic ODE has a nonzero full-domain solution exactly at physical trace level two. -/
theorem mem_classicalPeriodicEigenvalues_iff_discriminant (u : IntervalPairL2) (z : ℂ) :
    z ∈ classicalSignedEigenvalues u 0 ↔ l2Discriminant u z = 2 := by
  rw [← classicalSignedSpectrum_eq_eigenvalues,mem_classicalPeriodicSpectrum_iff_discriminant]

/-- The original antiperiodic ODE has a nonzero full-domain solution exactly at physical trace level minus two. -/
theorem mem_classicalAntiperiodicEigenvalues_iff_discriminant (u : IntervalPairL2) (z : ℂ) :
    z ∈ classicalSignedEigenvalues u 1 ↔ l2Discriminant u z = -2 := by
  rw [← classicalSignedSpectrum_eq_eigenvalues,mem_classicalAntiperiodicSpectrum_iff_discriminant]

end NLS.ZakharovShabat
