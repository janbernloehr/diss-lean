import NLS.Fourier.HilbertBoundedness
import NLS.SequenceSpaces.PeriodDoubling

/-!
# Restricting period-two coefficients to the unit interval

The unit-interval coefficients of a period-two input are its even samples
plus a shifted Hilbert transform of its odd samples. This bounded map for
1<p<∞ retains the odd input modes; merely reading even coefficients would
not represent physical restriction.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Sampling one parity class is a contraction on coefficients. -/
def paritySample (r : ℤ) : Coeff p →L[ℂ] Coeff p :=
  (show Coeff p →ₗ[ℂ] Coeff p from
    { toFun := fun a => Coeff.periodHalve (Coeff.shift (-r) a)
      map_add' := fun a b => by ext n; rfl
      map_smul' := fun c a => by ext n; rfl }).mkContinuous 1 (by
        intro a
        change ‖Coeff.periodHalve (Coeff.shift (-r) a)‖ ≤ 1 * ‖a‖
        simpa only [one_mul, Coeff.norm_shift] using
          Coeff.norm_periodHalve_le (Coeff.shift (-r) a))

@[simp] theorem paritySample_apply (r : ℤ) (a : Coeff p) (n : ℤ) :
    paritySample r a n = a (2*n+r) := by
  change a (2*n-(-r)) = _
  simp

theorem norm_paritySample_le (r : ℤ) (a : Coeff p) : ‖paritySample r a‖ ≤ ‖a‖ := by
  change ‖Coeff.periodHalve (Coeff.shift (-r) a)‖ ≤ _
  exact (Coeff.norm_periodHalve_le _).trans_eq (Coeff.norm_shift _ _)

/-- Actual restriction and unit-period re-expansion in the original scalar coefficient norm. -/
def periodTwoToUnit (hp1 : 1 < p) (hp : p ≠ ⊤) : Coeff p →L[ℂ] Coeff p :=
  paritySample 0 + Complex.I •
    ((Coeff.shift 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((shiftedHilbertTransform hp1 hp).comp (paritySample 1)))

@[simp] theorem periodTwoToUnit_apply (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) :
    periodTwoToUnit hp1 hp a n = a (2*n) +
      Complex.I * shiftedHilbertTransform hp1 hp (paritySample 1 a) (n-1) := by
  change paritySample 0 a n + Complex.I * Coeff.shift 1 (shiftedHilbertTransform hp1 hp (paritySample 1 a)) n = _
  simp

/-- A sufficient bound for actual unit-interval restriction. -/
def periodTwoToUnitBound (hp1 : 1 < p) (hp : p ≠ ⊤) : ℝ :=
  1 + Real.pi⁻¹ * (hilbertTransformBound hp1 hp + ‖hilbertCorrectionCoeffs‖)

theorem norm_periodTwoToUnit_le (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) :
    ‖periodTwoToUnit hp1 hp a‖ ≤ periodTwoToUnitBound hp1 hp * ‖a‖ := by
  change ‖paritySample 0 a + Complex.I • Coeff.shift 1 (shiftedHilbertTransform hp1 hp (paritySample 1 a))‖ ≤ _
  calc
    _ ≤ ‖paritySample 0 a‖ + ‖Complex.I • Coeff.shift 1 (shiftedHilbertTransform hp1 hp (paritySample 1 a))‖ := norm_add_le _ _
    _ = ‖paritySample 0 a‖ + ‖shiftedHilbertTransform hp1 hp (paritySample 1 a)‖ := by simp [norm_smul]
    _ ≤ ‖a‖ + Real.pi⁻¹ * (hilbertTransformBound hp1 hp + ‖hilbertCorrectionCoeffs‖) * ‖a‖ := by
      have hH := hilbertTransformBound_nonneg hp1 hp
      apply add_le_add (norm_paritySample_le _ _)
      exact (norm_shiftedHilbertTransform_apply_le hp1 hp _).trans
        (mul_le_mul_of_nonneg_left (norm_paritySample_le _ _) (by positivity))
    _ = _ := by unfold periodTwoToUnitBound; ring

/-- Restriction is the identity on the canonically embedded period-one inputs. -/
theorem periodTwoToUnit_periodDouble (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) :
    periodTwoToUnit hp1 hp (Coeff.periodDouble a) = a := by
  have ho : paritySample 1 (Coeff.periodDouble a) = 0 := by ext n; simp
  ext n
  simp [ho]

end NLS.Fourier
