import NLS.ZakharovShabat.UnitParityResolvent
import NLS.ZakharovShabat.SourceParitySpectralGeometry

/-! # The classical signed spectra and their exact period-two union -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- Resolvent parameters of the actual classical signed operator, defined by bounded two-sided inverse. -/
def classicalSignedResolventSet (u : IntervalPairL2) (r : ℤ) : Set ℂ :=
  {z | ∃ R : IntervalPairL2 →L[ℂ] (classicalSignedOperator u r).domain,
    (∀ f, linearPMapPencil (classicalSignedOperator u r) z (R f) = f) ∧
    (∀ g, R (linearPMapPencil (classicalSignedOperator u r) z g) = g)}

/-- The classical physical spectrum is defined before comparing it with any coefficient or eigenvalue set. -/
def classicalSignedSpectrum (u : IntervalPairL2) (r : ℤ) : Set ℂ :=
  (classicalSignedResolventSet u r)ᶜ

theorem classicalSignedResolventSet_eq (u : IntervalPairL2) (r : ℤ) :
    classicalSignedResolventSet u r = sourceParityResolventSet (by simp)
      (periodOnePair (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) r :=
  Set.ext (mem_unitParityResolventSet_iff _ _ r)

theorem classicalSignedSpectrum_eq (u : IntervalPairL2) (r : ℤ) :
    classicalSignedSpectrum u r = sourceParitySpectrum (by simp)
      (periodOnePair (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) r := by
  rw [classicalSignedSpectrum,classicalSignedResolventSet_eq]
  rfl

/-- The union of the two actual classical unit-interval spectra is exactly the original period-two spectrum. -/
theorem classicalSignedSpectrum_union_eq_periodic (u : IntervalPairL2) :
    classicalSignedSpectrum u 0 ∪ classicalSignedSpectrum u 1 =
      periodicSpectrum (by simp) (periodOnePotential (sourcePhysicalL2Equiv.symm u)) := by
  rw [classicalSignedSpectrum_eq,classicalSignedSpectrum_eq,← sourceSpectrum_eq_parity_union,
    sourceResolventSet_eq]
  rfl

/-- The source period-one physical potential has exactly the printed combined periodic spectrum. -/
theorem classicalSignedSpectrum_union_sourcePhysicalL2 (φ : CoeffPair 2) :
    classicalSignedSpectrum (sourcePhysicalL2 φ) 0 ∪ classicalSignedSpectrum (sourcePhysicalL2 φ) 1 =
      periodicSpectrum (by simp) (periodOnePotential φ) := by
  simpa only [← sourcePhysicalL2Equiv_apply,LinearIsometryEquiv.symm_apply_apply] using
    classicalSignedSpectrum_union_eq_periodic (sourcePhysicalL2 φ)

/-- Each physical spectrum is closed for every complex L² potential. -/
theorem isClosed_classicalSignedSpectrum (u : IntervalPairL2) (r : ℤ) :
    IsClosed (classicalSignedSpectrum u r) := by
  rw [classicalSignedSpectrum_eq]
  exact isClosed_sourceParitySpectrum _ _ _ _

/-- Every bounded part of either physical signed spectrum is finite. -/
theorem finite_classicalSignedSpectrum_inter_of_isBounded (u : IntervalPairL2) (r : ℤ)
    {K : Set ℂ} (hK : Bornology.IsBounded K) : Set.Finite (classicalSignedSpectrum u r ∩ K) := by
  rw [classicalSignedSpectrum_eq]
  exact finite_sourceParitySpectrum_inter_of_isBounded _ _ _ _ hK

theorem discreteTopology_classicalSignedSpectrum (u : IntervalPairL2) (r : ℤ) :
    DiscreteTopology (classicalSignedSpectrum u r) := by
  rw [classicalSignedSpectrum_eq]
  exact discreteTopology_sourceParitySpectrum _ _ _ _

/-- Either actual classical spectrum is characterized by the original algebraic parity multiplicity. -/
theorem mem_classicalSignedSpectrum_iff_multiplicity_pos (u : IntervalPairL2) (r : ℤ) (z : ℂ) :
    z ∈ classicalSignedSpectrum u r ↔
      0 < parityAlgebraicMultiplicity (by simp) (periodOnePotential (sourcePhysicalL2Equiv.symm u)) r z := by
  rw [classicalSignedSpectrum_eq,mem_sourceParitySpectrum_iff_multiplicity_pos]
  rfl

/-- Every actual physical spectral point is a nonzero kernel vector of the classical partial operator. -/
theorem mem_classicalSignedSpectrum_iff_exists_kernel (u : IntervalPairL2) (r : ℤ) (z : ℂ) :
    z ∈ classicalSignedSpectrum u r ↔
      ∃ a : (classicalSignedOperator u r).domain, (a : IntervalPairL2) ≠ 0 ∧
        linearPMapPencil (classicalSignedOperator u r) z a = 0 := by
  rw [classicalSignedSpectrum_eq,mem_sourceParitySpectrum_iff_exists_kernel]
  constructor
  · rintro ⟨a,hne,ha⟩
    refine ⟨unitParityDomainEquiv r a,?_,?_⟩
    · intro h
      apply hne
      apply unitParityDomainInclusion_injective r
      exact h.trans (map_zero _).symm
    · change linearPMapPencil (unitParityOperator (periodOnePair (sourcePhysicalL2Equiv.symm u))
        (periodOnePotential_mem _) r) z (unitParityDomainEquiv r a) = 0
      rw [unitParityPencil_intertwining,ha,map_zero]
  · rintro ⟨a,hne,ha⟩
    obtain ⟨b,rfl⟩ := (unitParityDomainEquiv r).surjective a
    refine ⟨b,?_,?_⟩
    · intro h
      apply hne
      change unitParityDomainInclusion r b = 0
      rw [h,map_zero]
    · change linearPMapPencil (unitParityOperator (periodOnePair (sourcePhysicalL2Equiv.symm u))
        (periodOnePotential_mem _) r) z (unitParityDomainEquiv r b) = 0 at ha
      rw [unitParityPencil_intertwining] at ha
      exact (sourceParityUnitEquiv r).injective (ha.trans (map_zero _).symm)

/-- The actual physical antiperiodic inverse exists at zero, while the periodic physical operator has zero in its spectrum. -/
theorem zero_mem_classicalOddResolvent_and_evenSpectrum :
    (0 : ℂ) ∈ classicalSignedResolventSet 0 1 ∧ (0 : ℂ) ∈ classicalSignedSpectrum 0 0 := by
  have hφ : periodOnePotential (sourcePhysicalL2Equiv.symm (0 : IntervalPairL2)) = 0 := by
    change (CoeffPair.toMax 2) (periodOnePair (sourcePhysicalL2Equiv.symm (0 : IntervalPairL2))) = 0
    simp only [map_zero]
  have hodd : (0 : ℂ) ∉ classicalSignedSpectrum 0 1 := by
    rw [mem_classicalSignedSpectrum_iff_multiplicity_pos,hφ]
    have h := parityAlgebraicMultiplicity_zero (p := 2) (by simp) 1 0
    norm_num at h
    rw [h]
    norm_num
  refine ⟨by simpa only [classicalSignedSpectrum,mem_compl_iff,not_not] using hodd,?_⟩
  rw [mem_classicalSignedSpectrum_iff_multiplicity_pos,hφ]
  have h := parityAlgebraicMultiplicity_zero (p := 2) (by simp) 0 0
  norm_num at h
  rw [h]
  norm_num

end NLS.ZakharovShabat
