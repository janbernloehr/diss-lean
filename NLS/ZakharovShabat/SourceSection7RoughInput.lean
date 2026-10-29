import NLS.Fourier.NonMeasureFourierCounterexample
import NLS.SequenceSpaces.Reflection
import NLS.ZakharovShabat.SourceRealTypeBanachSpace

/-! # Actual real-type rough sources in the Section 7 overview

The existing original distribution which is not a measure supplies the
first component. Its conjugate reflection supplies the second component,
so the obstruction occurs in the real source space itself.
-/
noncomputable section
set_option autoImplicit false
open NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Above two, an actual real source has a unit-period first component not represented by a measure. -/
theorem exists_real_source_first_component_not_measure (hp2 : 2 < p) :
    ∃ φ : realTypeSourceSubmodule p,
      ¬∃ μ : MeasureTheory.ComplexMeasure (AddCircle (1 : ℝ)),
        SmoothPeriodicTest.Distribution.ofComplexMeasure μ =
          ((PeriodicFourierLebesgue.unweightedCoefficients (L := (1 : ℝ)) p).symm φ.val.fst).val := by
  let u := nonMeasureDistribution (L := (1 : ℝ))
  have hu : u ∈ periodicFourierLebesgueSubmodule Weight.one p :=
    nonMeasureDistribution_mem_fourierLebesgue hp2
  let a : Coeff p := PeriodicFourierLebesgue.unweightedCoefficients p ⟨u,hu⟩
  let φ : CoeffPair p := (CoeffPair.toMax p).symm (a,star (Coeff.reflection a))
  have hφ : IsRealType (CoeffPair.toMax p φ) := by
    rw [ContinuousLinearEquiv.apply_symm_apply]
    intro m
    simp only [lp.star_apply,Coeff.reflection_apply]
    rfl
  refine ⟨⟨φ,hφ⟩,?_⟩
  have he : ((PeriodicFourierLebesgue.unweightedCoefficients (L := (1 : ℝ)) p).symm φ.fst).val = u := by
    change ((PeriodicFourierLebesgue.unweightedCoefficients (L := (1 : ℝ)) p).symm a).val = u
    exact congrArg Subtype.val ((PeriodicFourierLebesgue.unweightedCoefficients p).symm_apply_apply ⟨u,hu⟩)
  rw [he]
  exact nonMeasureDistribution_not_measure

end NLS.ZakharovShabat
