import NLS.Fourier.PeriodTwoRestrictionL2
import NLS.ZakharovShabat.SourceLemma4_3Physical
import NLS.ZakharovShabat.SourcePhaseCompatibility

/-! # Actual period-two input for the unit-interval boundary problems

Apply physical restriction to each raw Fourier component, retaining the
original component-sum norm. The resulting unit-period coefficients are the
input to the already completed ordinary and auxiliary interval extensions.
-/

noncomputable section
open scoped ENNReal
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Restrict the original period-two source to the boundary interval and re-expand with unit frequencies. -/
def sourcePeriodTwoRestriction (hp1 : 1 < p) (hp : p ≠ ⊤) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    (((periodTwoToUnit hp1 hp).prodMap (periodTwoToUnit hp1 hp)).comp
      (CoeffPair.toMax p).toContinuousLinearMap)

@[simp] theorem sourcePeriodTwoRestriction_fst (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    (sourcePeriodTwoRestriction hp1 hp φ).fst = periodTwoToUnit hp1 hp φ.fst := rfl

@[simp] theorem sourcePeriodTwoRestriction_snd (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    (sourcePeriodTwoRestriction hp1 hp φ).snd = periodTwoToUnit hp1 hp φ.snd := rfl

/-- The scalar restriction bound is retained in the exact original pair norm. -/
theorem norm_sourcePeriodTwoRestriction_le (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ‖sourcePeriodTwoRestriction hp1 hp φ‖ ≤ periodTwoToUnitBound hp1 hp * ‖φ‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hC : 0 ≤ periodTwoToUnitBound hp1 hp := by
    have hH := hilbertTransformBound_nonneg hp1 hp
    unfold periodTwoToUnitBound
    positivity
  rw [WithLp.prod_norm_eq_add hp0, sourcePeriodTwoRestriction_fst, sourcePeriodTwoRestriction_snd]
  calc
    _ ≤ ((periodTwoToUnitBound hp1 hp * ‖φ.fst‖)^p.toReal +
        (periodTwoToUnitBound hp1 hp * ‖φ.snd‖)^p.toReal)^(1/p.toReal) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact add_le_add
        (Real.rpow_le_rpow (norm_nonneg _) (norm_periodTwoToUnit_le hp1 hp _) hp0.le)
        (Real.rpow_le_rpow (norm_nonneg _) (norm_periodTwoToUnit_le hp1 hp _) hp0.le)
    _ = _ := by
      rw [Real.mul_rpow hC (norm_nonneg _), Real.mul_rpow hC (norm_nonneg _), ← mul_add,
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hC, mul_one_div_cancel hp0.ne',
        Real.rpow_one, ← WithLp.prod_norm_eq_add hp0]

/-- Restriction commutes with the potential phase used for the auxiliary problems. -/
theorem sourcePeriodTwoRestriction_sourcePhase (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    sourcePeriodTwoRestriction hp1 hp (sourcePhase φ) = sourcePhase (sourcePeriodTwoRestriction hp1 hp φ) := by
  apply (CoeffPair.toMax p).injective
  change (periodTwoToUnit hp1 hp (Complex.I • φ.fst), periodTwoToUnit hp1 hp (-Complex.I • φ.snd)) =
    (Complex.I • periodTwoToUnit hp1 hp φ.fst, -Complex.I • periodTwoToUnit hp1 hp φ.snd)
  simp only [map_smul]

/-- Original raw period-two L² Fourier coefficients of a physical pair. -/
def sourcePeriodTwoL2Coefficients (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) : CoeffPair 2 :=
  WithLp.toLp 2 (periodTwoL2Coefficients (fun x => (f x).1) hf.fst,
    periodTwoL2Coefficients (fun x => (f x).2) hf.snd)

/-- On arbitrary L² data the original pair map is actual restriction to [0,1]. -/
theorem sourcePeriodTwoRestriction_ofFunction (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hf1 : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    sourcePeriodTwoRestriction (by norm_num) (by simp) (sourcePeriodTwoL2Coefficients f hf) =
      sourceUnitIntervalL2Coefficients f hf1 := by
  apply (CoeffPair.toMax 2).injective
  exact Prod.ext
    (periodTwoToUnit_two_eq_unitIntervalCoefficients (fun x => (f x).1) hf.fst hf1.fst)
    (periodTwoToUnit_two_eq_unitIntervalCoefficients (fun x => (f x).2) hf.snd hf1.snd)

/-- The completed extension after restriction reconstructs the literal reflected physical pair. -/
theorem sourcePeriodTwoRestriction_reflection (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hf1 : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    sourceCircleRepresentative (sourceCircleSynthesis
      (sourceIntervalExtensionL2 b (sourcePeriodTwoRestriction (by norm_num) (by simp)
        (sourcePeriodTwoL2Coefficients f hf))))
      =ᵐ[volume.restrict (Ioc 0 2)] BoundaryCondition.intervalExtension b f := by
  rw [sourcePeriodTwoRestriction_ofFunction f hf hf1]
  exact sourceLemma4_3_L2_physical b f hf1

end NLS.ZakharovShabat
