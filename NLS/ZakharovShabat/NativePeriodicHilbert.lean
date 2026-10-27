import NLS.ZakharovShabat.NativePeriodicOperator
import NLS.ZakharovShabat.PhysicalPeriodicSpectrum

/-! # Compatibility of the native distribution operator with the physical Hilbert operator

The exact normalized L² realization preserves the entire operator graph,
including its full H¹ domain. For original period-one potentials, its spectrum
is the union of the two actual classical signed spectra on the unit interval.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.ZakharovShabat.NativePeriodic
open NLS.Fourier SmoothPeriodicTest PeriodicFourierLebesgue

/-- The physical normalized L² realization of the original distribution pair. -/
def hilbertRealization : Space 2 ≃ₗᵢ[ℂ] SourceCirclePairL2 :=
  (coefficients 2).trans sourceCircleSynthesis

theorem hilbertRealization_fst (u : Space 2) :
    (hilbertRealization u).fst = l2Isometry u.fst := rfl

theorem hilbertRealization_snd (u : Space 2) :
    (hilbertRealization u).snd = l2Isometry u.snd := rfl

/-- The physical first component represents the same original distribution. -/
theorem hilbertRealization_fst_represents (u : Space 2) :
    Distribution.ofCircleL1 (hilbertRealization u).fst
      ((MeasureTheory.Lp.memLp (hilbertRealization u).fst).integrable (by norm_num)) = u.fst.val :=
  l2Isometry_represents u.fst

/-- The physical second component represents the same original distribution. -/
theorem hilbertRealization_snd_represents (u : Space 2) :
    Distribution.ofCircleL1 (hilbertRealization u).snd
      ((MeasureTheory.Lp.memLp (hilbertRealization u).snd).integrable (by norm_num)) = u.snd.val :=
  l2Isometry_represents u.snd

theorem hilbertRealization_inclusion (f : Domain 2) :
    hilbertRealization (inclusion f) = physicalPeriodicDomainInclusion (domainCoefficients 2 f) := by
  change sourceCircleSynthesis (coefficients 2 (inclusion f)) = _
  rw [coefficients_inclusion]
  rfl

theorem hilbertRealization_operator (φ : Space 2) (f : Domain 2) :
    hilbertRealization (operator (by simp) φ f) =
      physicalPeriodicOperator (coefficients 2 φ) (physicalPeriodicDomainEquiv (domainCoefficients 2 f)) := by
  change sourceCircleSynthesis (coefficients 2 (operator (by simp) φ f)) = _
  rw [coefficients_operator, physicalPeriodicOperator_apply]

/-- Equality of the whole graphs, including every domain vector in both directions. -/
theorem graph_hilbert_iff (φ x y : Space 2) :
    (x,y) ∈ (unboundedOperator (by simp) φ).graph ↔
      (hilbertRealization x, hilbertRealization y) ∈
        (physicalPeriodicOperator (coefficients 2 φ)).graph := by
  rw [unboundedOperator_graph, mem_graph, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨f, rfl, rfl⟩
    refine ⟨physicalPeriodicDomainEquiv (domainCoefficients 2 f), ?_, ?_⟩
    · exact (hilbertRealization_inclusion f).symm
    · exact (hilbertRealization_operator φ f).symm
  · rintro ⟨g, hg, hL⟩
    obtain ⟨a, rfl⟩ := physicalPeriodicDomainEquiv.surjective g
    obtain ⟨f, rfl⟩ := (domainCoefficients 2).surjective a
    refine ⟨f, hilbertRealization.injective ?_, hilbertRealization.injective ?_⟩
    · rw [hilbertRealization_inclusion]
      exact hg
    · rw [hilbertRealization_operator]
      exact hL

/-- The native and physical operators have the same full bounded-inverse spectrum. -/
theorem spectrum_eq_physical (φ : Space 2) :
    spectrum (by simp) φ = physicalPeriodicSpectrum (coefficients 2 φ) := by
  rw [spectrum_eq, physicalPeriodicSpectrum_eq]

/-- At an original period-one L² potential, both classical signs are recovered. -/
theorem spectrum_eq_classicalSigned_union (u : IntervalPairL2) :
    spectrum (by simp) ((coefficients 2).symm (periodOnePair (sourcePhysicalL2Equiv.symm u))) =
      classicalSignedSpectrum u 0 ∪ classicalSignedSpectrum u 1 := by
  rw [spectrum_eq_physical, LinearIsometryEquiv.apply_symm_apply,
    physicalPeriodicSpectrum_eq_classicalSigned_union]

end NLS.ZakharovShabat.NativePeriodic
