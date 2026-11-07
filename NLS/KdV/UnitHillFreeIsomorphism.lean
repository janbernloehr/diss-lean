import NLS.KdV.SingularHillFreeIsomorphism
import NLS.KdV.PeriodOneHminusOneOriginal
import NLS.Fourier.UnitIntervalDirichlet
import NLS.SequenceSpaces.SobolevModeDualExt

/-! # The free unit-period H1 isomorphism and its full-dual realization

The physical massive Laplacian has symbol 1+(2*pi*n)^2. Even insertion
and the verified original free operator give its forward map; a bounded
inverse gains the exact two Sobolev orders on every coefficient.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open NLS.ZakharovShabat

/-- The original physical massive free operator on the full unit-period domain. -/
def unitHillFreeShift : ScalarDomain 2 →L[ℂ] PeriodOneHminusOne :=
  periodOneOriginalExtract.comp (singularHillFreeShift.comp unitSobolevOriginalH1)

theorem unitHillFreeShift_coefficient (f : ScalarDomain 2) (n : ℤ) :
    (unitHillFreeShift f).val n = ((1+freeHillValue (2*n):ℝ):ℂ)*f.val n := by
  change (periodOneOriginalExtract (singularHillFreeShift (unitSobolevOriginalH1 f))).val n = _
  rw [periodOneOriginalExtract_apply, singularHillFreeShift_coefficient,
    unitSobolevOriginalH1_coefficient, Coeff.periodDouble_even, scalarInclusion_apply]

theorem unitHillFreeMass_ne_zero (n : ℤ) : ((1+freeHillValue (2*n):ℝ):ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  have hv : 0 ≤ freeHillValue (2*n) := by unfold freeHillValue; positivity
  linarith

/-- The inverse physical unit symbol gains two full Sobolev orders. -/
theorem unitHillFreeInverse_weight_bound (n : ℤ) :
    Weight.sobolev 1 n * ‖(((1+freeHillValue (2*n):ℝ)⁻¹):ℂ)‖ ≤
      2*Weight.sobolev (-1) n := by
  have h1 : Weight.sobolev 1 n ≤ Weight.sobolev 1 (2*n) := by
    simp only [Weight.sobolev_apply, Real.rpow_one, Int.cast_mul, Int.cast_ofNat,
      abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [abs_nonneg (n:ℝ)]
  have hm : Weight.sobolev (-1) (2*n) ≤ Weight.sobolev (-1) n := by
    simpa only [periodOneOriginalWeight, Weight.pullback_apply,
      Coeff.parityEmbedding_apply, add_zero] using (periodOneOriginalWeight_bounds n).1
  calc
    _ ≤ Weight.sobolev 1 (2*n)*‖(((1+freeHillValue (2*n):ℝ)⁻¹):ℂ)‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ 2*Weight.sobolev (-1) (2*n) := singularHillFreeInverse_weight_bound (2*n)
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by norm_num)

/-- The exact inverse on the full unit-period H-minus-one space. -/
def unitHillFreeInverse : PeriodOneHminusOne →L[ℂ] ScalarDomain 2 :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun n => (((1+freeHillValue (2*n):ℝ)⁻¹):ℂ))
    2 (by norm_num) unitHillFreeInverse_weight_bound

theorem unitHillFreeInverse_coefficient (a : PeriodOneHminusOne) (n : ℤ) :
    (unitHillFreeInverse a).val n = (((1+freeHillValue (2*n):ℝ)⁻¹):ℂ)*a.val n := rfl

theorem unitHillFreeShift_inverse (a : PeriodOneHminusOne) :
    unitHillFreeShift (unitHillFreeInverse a) = a := by
  apply Subtype.ext
  funext n
  rw [unitHillFreeShift_coefficient, unitHillFreeInverse_coefficient]
  rw [← mul_assoc, mul_inv_cancel₀ (unitHillFreeMass_ne_zero n), one_mul]

theorem unitHillFreeInverse_shift (f : ScalarDomain 2) :
    unitHillFreeInverse (unitHillFreeShift f) = f := by
  apply Subtype.ext
  funext n
  rw [unitHillFreeInverse_coefficient, unitHillFreeShift_coefficient]
  rw [← mul_assoc, inv_mul_cancel₀ (unitHillFreeMass_ne_zero n), one_mul]

/-- The entire unit-period massive free isomorphism, with its actual physical symbol. -/
def unitHillFreeIsomorphism : ScalarDomain 2 ≃L[ℂ] PeriodOneHminusOne where
  toLinearEquiv :=
    { toLinearMap := unitHillFreeShift.toLinearMap
      invFun := unitHillFreeInverse
      left_inv := unitHillFreeInverse_shift
      right_inv := unitHillFreeShift_inverse }
  continuous_toFun := unitHillFreeShift.continuous
  continuous_invFun := unitHillFreeInverse.continuous

/-- The free isomorphism into the FULL continuous unit-period H1 dual. -/
def unitHillFreeDualIsomorphism : ScalarDomain 2 ≃L[ℂ] (ScalarDomain 2 →L[ℂ] ℂ) :=
  unitHillFreeIsomorphism.trans
    (WeightedCoeff.sobolevDualityIsometry (p := 2) (q := 2) 1 (by norm_num)).toContinuousLinearEquiv

/-- Every raw signed mode reads the original massive free coefficient. -/
theorem unitHillFreeDualIsomorphism_mode (f : ScalarDomain 2) (n : ℤ) :
    unitHillFreeDualIsomorphism f (scalarMode n 1) =
      ((1+freeHillValue (2*(-n)):ℝ):ℂ)*f.val (-n) := by
  change WeightedCoeff.sobolevBilinearPairing 1 (scalarMode n 1) (unitHillFreeShift f) = _
  rw [WeightedCoeff.sobolevBilinearPairing_apply]
  simp only [scalarMode_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq]
  exact unitHillFreeShift_coefficient f (-n)

/-- The inverse full-dual solution has its literal physical inverse multiplier. -/
theorem unitHillFreeDualIsomorphism_symm_coefficient
    (F : ScalarDomain 2 →L[ℂ] ℂ) (n : ℤ) :
    (unitHillFreeDualIsomorphism.symm F).val n =
      (((1+freeHillValue (2*n):ℝ)⁻¹):ℂ)*F (scalarMode (-n) 1) := by
  change (unitHillFreeInverse
    ((WeightedCoeff.sobolevDualityIsometry (p := 2) (q := 2) 1 (by norm_num)).symm F)).val n = _
  rw [unitHillFreeInverse_coefficient, WeightedCoeff.sobolevDualityIsometry_symm_apply,
    WeightedCoeff.sobolevCotangent_val, ← scalarMode_eq_ofFinsupp]

end NLS.KdV
