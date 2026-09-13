import NLS.ZakharovShabat.ClassicalAuxiliaryOperator
import NLS.ZakharovShabat.ClassicalIntervalResolvent

/-!
# Resolvents of the original physical auxiliary operators

The resolvent set is actual bijectivity of the physical auxiliary pencil.
Phase conjugation proves equivalence with the ordinary physical resolvent set.
The bounded inverse solves both inverse equations in the original spaces, its
base-space realization is compact, and its spectrum is precisely the original
auxiliary eigenvalue set and the actual coefficient auxiliary spectrum.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.ZakharovShabat.BoundaryCondition

/-- The original auxiliary z-L pencil, using actual physical inclusion and operator. -/
def classicalAuxiliaryPencil (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    ClassicalAuxiliaryDomain b →L[ℂ] IntervalPairL2 :=
  z • classicalAuxiliaryInclusion b - classicalAuxiliaryOperator b u

@[simp] theorem classicalAuxiliaryPencil_apply (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (f : ClassicalAuxiliaryDomain b) : classicalAuxiliaryPencil b u z f =
      z • classicalAuxiliaryInclusion b f - classicalAuxiliaryOperator b u f := rfl

theorem classicalAuxiliaryPencil_phase (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (f : ClassicalIntervalDomain b) :
    classicalAuxiliaryPencil b u z (classicalAuxiliaryDomainPhase b f) =
      intervalAuxiliaryPhase (classicalPencil b (intervalAuxiliaryPotential u) z f) := by
  change z • classicalAuxiliaryInclusion b (classicalAuxiliaryDomainPhase b f) -
    classicalAuxiliaryOperator b u (classicalAuxiliaryDomainPhase b f) = _
  rw [classicalAuxiliaryInclusion_phase, classicalAuxiliaryOperator_phase, classicalPencil_apply, map_sub, map_smul]

/-- Actual invertibility of the original physical auxiliary pencil. -/
def classicalAuxiliaryResolventSet (b : BoundaryCondition) (u : IntervalPairL2) : Set ℂ :=
  {z | Function.Bijective (classicalAuxiliaryPencil b u z)}

private theorem bijective_of_phase {A B C D : Type*} (e : A ≃ B) (d : C ≃ D)
    (f : A → C) (g : B → D) (h : ∀ a, g (e a) = d (f a)) : Function.Bijective g ↔ Function.Bijective f := by
  have he : g ∘ e = d ∘ f := funext h
  rw [← e.bijective_comp g, he]
  exact d.comp_bijective f

/-- Actual physical auxiliary invertibility equals ordinary invertibility at the transformed potential. -/
theorem classicalAuxiliaryResolventSet_eq (b : BoundaryCondition) (u : IntervalPairL2) :
    classicalAuxiliaryResolventSet b u = classicalResolventSet b (intervalAuxiliaryPotential u) := by
  ext z
  exact bijective_of_phase (classicalAuxiliaryDomainPhase b).toEquiv intervalAuxiliaryPhase.toEquiv
    (classicalPencil b (intervalAuxiliaryPotential u) z) (classicalAuxiliaryPencil b u z)
    (classicalAuxiliaryPencil_phase b u z)

theorem isOpen_classicalAuxiliaryResolventSet (b : BoundaryCondition) (u : IntervalPairL2) :
    IsOpen (classicalAuxiliaryResolventSet b u) := by
  rw [classicalAuxiliaryResolventSet_eq]
  exact isOpen_classicalResolventSet b _

theorem classicalAuxiliaryResolventSet_nonempty (b : BoundaryCondition) (u : IntervalPairL2) :
    (classicalAuxiliaryResolventSet b u).Nonempty := by
  rw [classicalAuxiliaryResolventSet_eq]
  exact classicalResolventSet_nonempty b _

/-- The actual inverse into the original auxiliary H¹ domain. -/
def classicalAuxiliaryResolventToDomain (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    IntervalPairL2 →L[ℂ] ClassicalAuxiliaryDomain b :=
  (classicalAuxiliaryDomainPhase b).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((classicalResolventToDomain b (intervalAuxiliaryPotential u) z).comp
      intervalAuxiliaryPhase.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The physical auxiliary base-space resolvent. -/
def classicalAuxiliaryResolvent (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    IntervalPairL2 →L[ℂ] IntervalPairL2 :=
  (classicalAuxiliaryInclusion b).comp (classicalAuxiliaryResolventToDomain b u z)

/-- Every L² right-hand side has the asserted auxiliary-domain solution. -/
theorem classicalAuxiliaryPencil_resolventToDomain (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (hz : z ∈ classicalAuxiliaryResolventSet b u) (v : IntervalPairL2) :
    classicalAuxiliaryPencil b u z (classicalAuxiliaryResolventToDomain b u z v) = v := by
  change classicalAuxiliaryPencil b u z (classicalAuxiliaryDomainPhase b
    (classicalResolventToDomain b (intervalAuxiliaryPotential u) z (intervalAuxiliaryPhase.symm v))) = v
  rw [classicalAuxiliaryPencil_phase, classicalPencil_classicalResolventToDomain b _ z
    (by simpa only [classicalAuxiliaryResolventSet_eq] using hz), LinearIsometryEquiv.apply_symm_apply]

/-- The inverse recovers every original auxiliary domain vector. -/
theorem classicalAuxiliaryResolventToDomain_pencil (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (hz : z ∈ classicalAuxiliaryResolventSet b u) (f : ClassicalAuxiliaryDomain b) :
    classicalAuxiliaryResolventToDomain b u z (classicalAuxiliaryPencil b u z f) = f := by
  obtain ⟨g, rfl⟩ := (classicalAuxiliaryDomainPhase b).surjective f
  rw [classicalAuxiliaryPencil_phase]
  change classicalAuxiliaryDomainPhase b (classicalResolventToDomain b (intervalAuxiliaryPotential u) z
    (intervalAuxiliaryPhase.symm (intervalAuxiliaryPhase (classicalPencil b (intervalAuxiliaryPotential u) z g)))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, classicalResolventToDomain_classicalPencil b _ z
    (by simpa only [classicalAuxiliaryResolventSet_eq] using hz)]

/-- The base-space resolvent is phase-conjugate to the ordinary physical resolvent. -/
theorem classicalAuxiliaryResolvent_eq_conjugate (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalAuxiliaryResolvent b u z = intervalAuxiliaryPhase.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((classicalResolvent b (intervalAuxiliaryPotential u) z).comp
        intervalAuxiliaryPhase.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  ext v
  change classicalAuxiliaryInclusion b (classicalAuxiliaryDomainPhase b
    (classicalResolventToDomain b (intervalAuxiliaryPotential u) z (intervalAuxiliaryPhase.symm v))) = _
  rw [classicalAuxiliaryInclusion_phase]
  rfl

/-- The actual physical auxiliary resolvent is compact. -/
theorem isCompactOperator_classicalAuxiliaryResolvent (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    IsCompactOperator (classicalAuxiliaryResolvent b u z) := by
  rw [classicalAuxiliaryResolvent_eq_conjugate]
  exact ((isCompactOperator_classicalResolvent b (intervalAuxiliaryPotential u) z).comp_clm
    intervalAuxiliaryPhase.symm.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      intervalAuxiliaryPhase.toContinuousLinearEquiv.toContinuousLinearMap

/-- Spectrum defined by failure of the physical auxiliary pencil to be invertible. -/
def classicalAuxiliarySpectrum (b : BoundaryCondition) (u : IntervalPairL2) : Set ℂ :=
  (classicalAuxiliaryResolventSet b u)ᶜ

/-- The independently defined physical spectrum consists exactly of original auxiliary eigenvalues. -/
theorem classicalAuxiliarySpectrum_eq_eigenvalues (b : BoundaryCondition) (u : IntervalPairL2) :
    classicalAuxiliarySpectrum b u = classicalAuxiliaryEigenvalues b (intervalL2Representative u) := by
  rw [classicalAuxiliarySpectrum, classicalAuxiliaryResolventSet_eq]
  change classicalSpectrum b (intervalAuxiliaryPotential u) = _
  rw [classicalSpectrum_eq_classicalEigenvalues,
    classicalEigenvalues_congr_ae b (intervalL2Representative_auxiliaryPotential u), classicalAuxiliaryEigenvalues_eq]

theorem isClosed_classicalAuxiliarySpectrum (b : BoundaryCondition) (u : IntervalPairL2) :
    IsClosed (classicalAuxiliarySpectrum b u) := by
  rw [classicalAuxiliarySpectrum_eq_eigenvalues]
  exact isClosed_classicalAuxiliaryEigenvalues b _ (memLp_intervalL2Representative u)

theorem discreteTopology_classicalAuxiliarySpectrum (b : BoundaryCondition) (u : IntervalPairL2) :
    DiscreteTopology (classicalAuxiliarySpectrum b u) := by
  rw [classicalAuxiliarySpectrum_eq_eigenvalues]
  exact discreteTopology_classicalAuxiliaryEigenvalues b _ (memLp_intervalL2Representative u)

/-- The physical auxiliary spectrum equals the actual coefficient spectrum of the Neumann extension. -/
theorem classicalAuxiliarySpectrum_eq_auxiliarySpectrum (b : BoundaryCondition) (u : IntervalPairL2) :
    classicalAuxiliarySpectrum b u = auxiliarySpectrum b (by simp)
      (neumannPotentialCoefficients (intervalL2Representative u) (memLp_intervalL2Representative u))
      (neumannPotentialCoefficients_mem _ _) := by
  rw [classicalAuxiliarySpectrum_eq_eigenvalues, classicalAuxiliaryEigenvalues_eq_auxiliarySpectrum]

end NLS.ZakharovShabat.BoundaryCondition
