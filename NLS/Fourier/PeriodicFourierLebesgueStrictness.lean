import NLS.Fourier.NonMeasureFourierCounterexample
import NLS.Fourier.PeriodicFourierLebesgueEmbeddings

/-! # Original periodic Fourier-Lebesgue distributions outside L2

This implements the introduction statement on printed p. 10 at every positive period.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

/-- Every actual integrable circle function gives a distribution of order zero. -/
theorem Distribution.ofCircleL1_order (f : AddCircle L → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) : (Distribution.ofCircleL1 f hf).order = 0 := by
  apply (Distribution.order_zero_iff_physical_extension _).mpr
  refine ⟨circleL1Functional f hf,fun _ => rfl,?_⟩
  intro v hv
  apply DFunLike.coe_injective
  apply (denseRange_toContinuousCLM (L := L)).equalizer v.continuous (circleL1Functional f hf).continuous
  exact funext hv

/-- The original FL2=L2 distribution has order zero, with the actual L2 representative retained. -/
theorem order_zero_of_mem_periodicFourierLebesgue_two (u : Distribution L)
    (hu : u ∈ periodicFourierLebesgueSubmodule Weight.one 2) : u.order = 0 := by
  let u2 : PeriodicFourierLebesgue L Weight.one 2 := ⟨u,hu⟩
  change u2.val.order = 0
  rw [← PeriodicFourierLebesgue.l2Isometry_represents u2]
  exact Distribution.ofCircleL1_order _ _

/-- The same original counterexample belongs to all FLp above two but not FL2. -/
theorem nonMeasureDistribution_not_fourierLebesgue_two :
    nonMeasureDistribution (L := L) ∉ periodicFourierLebesgueSubmodule Weight.one 2 := by
  intro h
  exact nonMeasureDistribution_order_ne_zero
    (order_zero_of_mem_periodicFourierLebesgue_two _ h)

/-- At every positive period, all the larger FLp spaces contain an original distribution
outside L2; one witness works simultaneously for every p>2, including infinity. -/
theorem exists_fourierLebesgue_above_two_not_l2 :
    ∃ u : Distribution L,
      (∀ p : ℝ≥0∞, 2 < p → u ∈ periodicFourierLebesgueSubmodule Weight.one p) ∧
      u ∉ periodicFourierLebesgueSubmodule Weight.one 2 := by
  refine ⟨nonMeasureDistribution,?_,nonMeasureDistribution_not_fourierLebesgue_two⟩
  intro p hp
  let : Fact (1 ≤ p) := ⟨(by norm_num : (1:ℝ≥0∞) ≤ 2).trans hp.le⟩
  exact nonMeasureDistribution_mem_fourierLebesgue hp

end NLS.Fourier
