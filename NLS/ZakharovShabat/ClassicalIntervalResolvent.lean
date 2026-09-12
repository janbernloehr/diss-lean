import NLS.ZakharovShabat.ClassicalIntervalOperator

/-!
# Original interval resolvents and spectrum

The original resolvent set is defined by bijectivity of the physical pencil
`z - L` on the classical endpoint domain. Intertwining identifies it with the
coefficient boundary resolvent set. Its bounded inverse is transported back to
the original domain, and its base-space resolvent is compact. The complement
is therefore exactly the original classical eigenvalue set already defined.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.ZakharovShabat.BoundaryCondition

/-- The original spectral pencil, formed from physical inclusion and operator maps. -/
def classicalPencil (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    ClassicalIntervalDomain b →L[ℂ] IntervalPairL2 := z • classicalInclusion b - classicalOperator b u

@[simp] theorem classicalPencil_apply (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (f : ClassicalIntervalDomain b) :
    classicalPencil b u z f = z • classicalInclusion b f - classicalOperator b u f := rfl

/-- The domain and base isomorphisms intertwine the full spectral pencils. -/
theorem intervalL2Equiv_classicalPencil (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (f : ClassicalIntervalDomain b) :
    intervalL2Equiv b (classicalPencil b u z f) =
      pencil b (by simp) (intervalPotentialCoefficients u) (intervalPotentialToDirichlet u).property z
        (classicalIntervalEquiv b f) := by
  rw [classicalPencil_apply, map_sub, map_smul, intervalL2Equiv_classicalInclusion, intervalL2Equiv_classicalOperator]
  apply Subtype.ext
  rfl

/-- The original resolvent set is defined using the physical classical-domain pencil. -/
def classicalResolventSet (b : BoundaryCondition) (u : IntervalPairL2) : Set ℂ :=
  {z | Function.Bijective (classicalPencil b u z)}

/-- Physical and coefficient boundary resolvents have exactly the same admissible parameters. -/
theorem mem_classicalResolventSet_iff (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    z ∈ classicalResolventSet b u ↔ z ∈ resolventSet b (by simp) (intervalPotentialCoefficients u)
      (intervalPotentialToDirichlet u).property := by
  have he : (intervalL2Equiv b) ∘ classicalPencil b u z =
      (pencil b (by simp) (intervalPotentialCoefficients u) (intervalPotentialToDirichlet u).property z) ∘
        classicalIntervalEquiv b := funext (intervalL2Equiv_classicalPencil b u z)
  change Function.Bijective (classicalPencil b u z) ↔ Function.Bijective (pencil b _ _ _ z)
  rw [← Function.Bijective.of_comp_iff' (intervalL2Equiv b).bijective (classicalPencil b u z), he]
  exact Function.Bijective.of_comp_iff _ (classicalIntervalEquiv b).bijective

theorem classicalResolventSet_eq (b : BoundaryCondition) (u : IntervalPairL2) :
    classicalResolventSet b u = resolventSet b (by simp) (intervalPotentialCoefficients u)
      (intervalPotentialToDirichlet u).property := Set.ext (mem_classicalResolventSet_iff b u)

theorem isOpen_classicalResolventSet (b : BoundaryCondition) (u : IntervalPairL2) :
    IsOpen (classicalResolventSet b u) := by
  rw [classicalResolventSet_eq]
  exact isOpen_resolventSet b (by simp) _ _

theorem classicalResolventSet_nonempty (b : BoundaryCondition) (u : IntervalPairL2) :
    (classicalResolventSet b u).Nonempty := by
  obtain ⟨z, hz⟩ := ZakharovShabat.resolventSet_nonempty (by simp) (intervalPotentialCoefficients u)
  exact ⟨z, (mem_classicalResolventSet_iff b u z).mpr (mem_resolventSet_of_periodic b (by simp) _ _ z hz)⟩

/-- The original inverse into the classical domain, totalized by zero outside the resolvent set. -/
def classicalResolventToDomain (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    IntervalPairL2 →L[ℂ] ClassicalIntervalDomain b :=
  (classicalIntervalEquiv b).symm.toContinuousLinearMap.comp
    ((resolventToDomain b (by simp) (intervalPotentialCoefficients u) (intervalPotentialToDirichlet u).property z).comp
      (intervalL2Equiv b).toContinuousLinearMap)

/-- The base-space resolvent of the original interval operator. -/
def classicalResolvent (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) : IntervalPairL2 →L[ℂ] IntervalPairL2 :=
  (classicalInclusion b).comp (classicalResolventToDomain b u z)

@[simp] theorem classicalIntervalEquiv_classicalResolventToDomain (b : BoundaryCondition) (u : IntervalPairL2)
    (z : ℂ) (v : IntervalPairL2) :
    classicalIntervalEquiv b (classicalResolventToDomain b u z v) =
      resolventToDomain b (by simp) (intervalPotentialCoefficients u) (intervalPotentialToDirichlet u).property z
        (intervalL2Equiv b v) := (classicalIntervalEquiv b).apply_symm_apply _

/-- The original inverse solves the full inhomogeneous equation for every physical `L²` right-hand side. -/
theorem classicalPencil_classicalResolventToDomain (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (hz : z ∈ classicalResolventSet b u) (v : IntervalPairL2) :
    classicalPencil b u z (classicalResolventToDomain b u z v) = v := by
  apply (intervalL2Equiv b).injective
  rw [intervalL2Equiv_classicalPencil, classicalIntervalEquiv_classicalResolventToDomain]
  exact pencil_resolventToDomain b (by simp) _ _ z ((mem_classicalResolventSet_iff b u z).mp hz) _

/-- The original inverse also recovers every classical domain element. -/
theorem classicalResolventToDomain_classicalPencil (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (hz : z ∈ classicalResolventSet b u) (f : ClassicalIntervalDomain b) :
    classicalResolventToDomain b u z (classicalPencil b u z f) = f := by
  apply (classicalIntervalEquiv b).injective
  rw [classicalIntervalEquiv_classicalResolventToDomain, intervalL2Equiv_classicalPencil]
  exact resolventToDomain_pencil b (by simp) _ _ z ((mem_classicalResolventSet_iff b u z).mp hz) _

/-- Base-space resolvents are conjugate by the actual physical `L²` isomorphism. -/
theorem classicalResolvent_eq_conjugate (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalResolvent b u z = (intervalL2Equiv b).symm.toContinuousLinearMap.comp
      ((resolvent b (by simp) (intervalPotentialCoefficients u) (intervalPotentialToDirichlet u).property z).comp
        (intervalL2Equiv b).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro v
  apply (intervalL2Equiv b).injective
  change intervalL2Equiv b (classicalInclusion b (classicalResolventToDomain b u z v)) =
    intervalL2Equiv b ((intervalL2Equiv b).symm _)
  rw [intervalL2Equiv_classicalInclusion, classicalIntervalEquiv_classicalResolventToDomain,
    (intervalL2Equiv b).apply_symm_apply]
  rfl

/-- The original physical base-space resolvent is compact. -/
theorem isCompactOperator_classicalResolvent (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    IsCompactOperator (classicalResolvent b u z) := by
  rw [classicalResolvent_eq_conjugate]
  exact ((isCompactOperator_resolvent b (by simp) (intervalPotentialCoefficients u)
    (intervalPotentialToDirichlet u).property z).comp_clm (intervalL2Equiv b).toContinuousLinearMap).clm_comp
      (intervalL2Equiv b).symm.toContinuousLinearMap

/-- The original spectrum is defined as failure of invertibility of the physical pencil. -/
def classicalSpectrum (b : BoundaryCondition) (u : IntervalPairL2) : Set ℂ := (classicalResolventSet b u)ᶜ

/-- The independently defined physical spectrum is the selected coefficient boundary spectrum. -/
theorem classicalSpectrum_eq_boundarySpectrum (b : BoundaryCondition) (u : IntervalPairL2) :
    classicalSpectrum b u = spectrum b (by simp) (intervalPotentialCoefficients u)
      (intervalPotentialToDirichlet u).property := by
  rw [classicalSpectrum, classicalResolventSet_eq]
  rfl

/-- Every physical spectral point is an original classical eigenvalue, and conversely. -/
theorem classicalSpectrum_eq_classicalEigenvalues (b : BoundaryCondition) (u : IntervalPairL2) :
    classicalSpectrum b u = classicalEigenvalues b (intervalL2Representative u) := by
  rw [classicalSpectrum_eq_boundarySpectrum, classicalEigenvalues_eq_boundarySpectrum b _ (memLp_intervalL2Representative u)]
  rfl

/-- The original spectrum agrees with the differential-equation eigenvalues of any representative. -/
theorem classicalSpectrum_ofFunction (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    classicalSpectrum b (intervalL2OfFunction φ hφ) = classicalEigenvalues b φ := by
  rw [classicalSpectrum_eq_classicalEigenvalues]
  exact classicalEigenvalues_congr_ae b (intervalL2Representative_ofFunction φ hφ)

end NLS.ZakharovShabat.BoundaryCondition
