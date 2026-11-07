import NLS.SequenceSpaces.PeriodOneHminusOneRealDensity
import NLS.SequenceSpaces.WeightedRestrictionTwo
import NLS.KdV.SingularHillL2Domain
import NLS.Fourier.RealMeanZeroPeriodOne

/-! Exact period-one H-minus-one coefficients versus the original physical
period-two distributions. The weights are equivalent, not equal. -/
noncomputable section
open Set
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The original H-minus-one weight pulled back to the physical even modes. -/
def periodOneOriginalWeight : Weight := (Weight.sobolev (-1)).pullback (Coeff.parityEmbedding 0)

/-- Exact constants for the change from frequency n to the original mode 2n. -/
theorem periodOneOriginalWeight_bounds (n : ℤ) :
    periodOneOriginalWeight n ≤ Weight.sobolev (-1) n ∧
      Weight.sobolev (-1) n ≤ 2*periodOneOriginalWeight n := by
  simp only [periodOneOriginalWeight, Weight.pullback_apply, Coeff.parityEmbedding_apply, add_zero,
    Weight.sobolev_apply, Real.rpow_neg_one, Int.cast_mul, Int.cast_ofNat, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2)]
  constructor
  · exact inv_anti₀ (by positivity) (by linarith [abs_nonneg (n:ℝ)])
  · have hh : 1/(1+|(n:ℝ)|) ≤ 2/(1+2*|(n:ℝ)|) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by linarith)
    simpa only [one_div, div_eq_mul_inv, one_mul] using hh

/-- Zero insertion at the original even modes, with the correct weighted norm. -/
def periodOneOriginalCoefficients : PeriodOneHminusOne →L[ℂ] WeightedCoeff (Weight.sobolev (-1)) 2 :=
  (WeightedCoeff.insertIsometry (Weight.sobolev (-1)) (Coeff.parityEmbedding 0)).toContinuousLinearMap.comp
    (WeightedCoeff.inclusionCLM (Weight.sobolev (-1)) periodOneOriginalWeight
      (fun n => (periodOneOriginalWeight_bounds n).1))

theorem periodOneOriginalCoefficients_even (q : PeriodOneHminusOne) (n : ℤ) :
    (periodOneOriginalCoefficients q).val (2*n) = q.val n := by
  change (WeightedCoeff.insertIsometry (Weight.sobolev (-1)) (Coeff.parityEmbedding 0)
    (WeightedCoeff.inclusionCLM (Weight.sobolev (-1)) periodOneOriginalWeight
      (fun n => (periodOneOriginalWeight_bounds n).1) q)).val (2*n) = q.val n
  have hh := WeightedCoeff.insertIsometry_image (Weight.sobolev (-1)) (Coeff.parityEmbedding 0)
    (WeightedCoeff.inclusionCLM (Weight.sobolev (-1)) periodOneOriginalWeight
      (fun n => (periodOneOriginalWeight_bounds n).1) q) n
  simpa only [Coeff.parityEmbedding_apply, add_zero, WeightedCoeff.inclusionCLM_apply] using hh

theorem periodOneOriginalCoefficients_odd (q : PeriodOneHminusOne) (n : ℤ) :
    (periodOneOriginalCoefficients q).val (2*n+1) = 0 := by
  change (WeightedCoeff.insertIsometry (Weight.sobolev (-1)) (Coeff.parityEmbedding 0)
    (WeightedCoeff.inclusionCLM (Weight.sobolev (-1)) periodOneOriginalWeight
      (fun n => (periodOneOriginalWeight_bounds n).1) q)).val (2*n+1) = 0
  apply WeightedCoeff.insertIsometry_outside
  rintro ⟨k,hk⟩
  change 2*k+0 = 2*n+1 at hk
  omega

theorem norm_periodOneOriginalCoefficients_le (q : PeriodOneHminusOne) :
    ‖periodOneOriginalCoefficients q‖ ≤ ‖q‖ := by
  change ‖WeightedCoeff.insertIsometry (Weight.sobolev (-1)) (Coeff.parityEmbedding 0)
    (WeightedCoeff.inclusionCLM (Weight.sobolev (-1)) periodOneOriginalWeight
      (fun n => (periodOneOriginalWeight_bounds n).1) q)‖ ≤ ‖q‖
  dsimp only [periodOneOriginalWeight]
  rw [WeightedCoeff.norm_insertIsometry]
  exact WeightedCoeff.norm_inclusionCLM_le _ _ _ q

/-- The literal original H-minus-one distribution, with every physical frequency preserved. -/
def periodOneOriginal : PeriodOneHminusOne →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  (sobolevCoefficients (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp periodOneOriginalCoefficients

theorem periodOneOriginal_even (q : PeriodOneHminusOne) (n : ℤ) :
    (periodOneOriginal q).val (mode (-(2*n))) = q.val n := by
  change ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val (2*n) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact periodOneOriginalCoefficients_even q n

theorem periodOneOriginal_odd (q : PeriodOneHminusOne) (n : ℤ) :
    (periodOneOriginal q).val (mode (-(2*n+1))) = 0 := by
  change ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val (2*n+1) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact periodOneOriginalCoefficients_odd q n

theorem norm_periodOneOriginal_le (q : PeriodOneHminusOne) : ‖periodOneOriginal q‖ ≤ ‖q‖ := by
  change ‖(sobolevCoefficients (-1) 2).symm (periodOneOriginalCoefficients q)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact norm_periodOneOriginalCoefficients_le q

/-- Extract the period-one coefficients from ANY original H-minus-one distribution. -/
def periodOneOriginalExtract : FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] PeriodOneHminusOne :=
  (WeightedCoeff.weightedMultiplierCLM periodOneOriginalWeight (Weight.sobolev (-1))
    (fun _ => (1:ℂ)) 2 (by norm_num)
      (fun n => by simpa only [norm_one, mul_one] using (periodOneOriginalWeight_bounds n).2)).comp
        ((WeightedCoeff.restrictTwoCLM (Weight.sobolev (-1)) (Coeff.parityEmbedding 0)).comp
          (sobolevCoefficients (-1) 2).toContinuousLinearEquiv.toContinuousLinearMap)

theorem periodOneOriginalExtract_apply (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (n : ℤ) :
    (periodOneOriginalExtract q).val n = q.val (mode (-(2*n))) := by
  change (1:ℂ)*(WeightedCoeff.restrictTwoCLM _ _ (sobolevCoefficients (-1) 2 q)).val n = _
  rw [one_mul, WeightedCoeff.restrictTwoCLM_apply]
  simp only [Coeff.parityEmbedding_apply, add_zero]
  rfl

theorem norm_periodOneOriginalExtract_le (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    ‖periodOneOriginalExtract q‖ ≤ 2*‖q‖ := by
  have hm : ∀ n, Weight.sobolev (-1) n*‖(1:ℂ)‖ ≤ 2*periodOneOriginalWeight n :=
    fun n => by simpa only [norm_one, mul_one] using (periodOneOriginalWeight_bounds n).2
  let a := WeightedCoeff.restrictTwoCLM (Weight.sobolev (-1)) (Coeff.parityEmbedding 0)
    (sobolevCoefficients (-1) 2 q)
  change ‖WeightedCoeff.weightedMultiplier periodOneOriginalWeight (Weight.sobolev (-1))
    (fun _ => (1:ℂ)) 2 hm a‖ ≤ 2*‖q‖
  apply (WeightedCoeff.norm_weightedMultiplier_le _ _ _ 2 (by norm_num) hm a).trans
  have hh := WeightedCoeff.norm_restrictTwoCLM_le (Weight.sobolev (-1)) (Coeff.parityEmbedding 0)
    (sobolevCoefficients (-1) 2 q)
  rw [LinearIsometryEquiv.norm_map] at hh
  exact mul_le_mul_of_nonneg_left hh (by norm_num)

/-- The forward map loses no period-one coefficient information. -/
theorem periodOneOriginalExtract_original (q : PeriodOneHminusOne) :
    periodOneOriginalExtract (periodOneOriginal q) = q := by
  apply Subtype.ext
  funext n
  rw [periodOneOriginalExtract_apply, periodOneOriginal_even]

/-- Every original physically period-one H-minus-one distribution is recovered
EXACTLY on every smooth test by extraction followed by insertion. -/
theorem periodOneOriginal_extract (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : IsPeriodicDistribution 1 q.val.toTempered) :
    periodOneOriginal (periodOneOriginalExtract q) = q := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he, periodOneOriginal_even, periodOneOriginalExtract_apply]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he, periodOneOriginal_odd]
    exact ((Distribution.toTempered_period_one_iff_odd q.val).mp hq (k/2)).symm

/-- The period-one realization is injective, with an actual bounded left inverse. -/
theorem periodOneOriginal_injective : Function.Injective periodOneOriginal :=
  Function.LeftInverse.injective periodOneOriginalExtract_original

/-- Both exact norm comparison constants, retaining the original Sobolev weights. -/
theorem norm_periodOneOriginal_bounds (q : PeriodOneHminusOne) :
    ‖periodOneOriginal q‖ ≤ ‖q‖ ∧ ‖q‖ ≤ 2*‖periodOneOriginal q‖ := by
  refine ⟨norm_periodOneOriginal_le q, ?_⟩
  have hh := norm_periodOneOriginalExtract_le (periodOneOriginal q)
  rwa [periodOneOriginalExtract_original] at hh

/-- Every realized potential has physical period one in the original test space. -/
theorem periodOneOriginal_periodic (q : PeriodOneHminusOne) :
    IsPeriodicDistribution 1 (periodOneOriginal q).val.toTempered :=
  (Distribution.toTempered_period_one_iff_odd _).mpr (periodOneOriginal_odd q)

/-- Coefficient reality is exactly reality on every original smooth test. -/
theorem periodOneOriginal_real_iff (q : PeriodOneHminusOne) :
    (periodOneOriginal q).val = (periodOneOriginal q).val.conjugate ↔
      IsRealPeriodOneHminusOne q := by
  rw [Distribution.eq_conjugate_iff_coefficients]
  constructor
  · intro h n
    have hh := h (2*(-n))
    rw [periodOneOriginal_even,
      show 2*(-n) = -(2*n) by ring, periodOneOriginal_even] at hh
    simpa only [Complex.star_def] using hh
  · intro h k
    by_cases hk : k % 2 = 0
    · have he : k = 2*(k/2) := by omega
      rw [he, periodOneOriginal_even,
        show 2*(k/2) = -(2*(-(k/2))) by ring, periodOneOriginal_even]
      simpa only [neg_neg, Complex.star_def] using h (-(k/2))
    · have he : k = 2*(k/2)+1 := by omega
      rw [he, periodOneOriginal_odd,
        show 2*(k/2)+1 = -(2*(-(k/2)-1)+1) by ring, periodOneOriginal_odd]
      exact (map_zero (starRingEnd ℂ)).symm

/-- Extraction of any original real distribution has the original unit-period reality. -/
theorem periodOneOriginalExtract_real (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : q.val = q.val.conjugate) : IsRealPeriodOneHminusOne (periodOneOriginalExtract q) := by
  intro n
  have hh := (Distribution.eq_conjugate_iff_coefficients q.val q.val).mp hq (2*(-n))
  simpa only [periodOneOriginalExtract_apply, mul_neg, neg_neg, Complex.star_def] using hh

/-- Physical mean zero has precisely its raw unit-period coefficient meaning. -/
theorem periodOneOriginal_meanZero_iff (q : PeriodOneHminusOne) :
    (periodOneOriginal q).val (mode 0) = 0 ↔ q.val 0 = 0 := by
  simpa only [mul_zero, neg_zero] using
    (show (periodOneOriginal q).val (mode (-(2*0))) = 0 ↔ q.val 0 = 0 from
      (periodOneOriginal_even q 0).symm ▸ Iff.rfl)

/-- All original physical constraints are equivalent to real unit-period
coefficients and a zero raw constant mode. -/
theorem periodOneOriginal_source_iff (q : PeriodOneHminusOne) :
    (periodOneOriginal q).val.IsRealMeanZeroPeriodOne ↔
      IsRealPeriodOneHminusOne q ∧ q.val 0 = 0 := by
  rw [Distribution.IsRealMeanZeroPeriodOne, periodOneOriginal_real_iff,
    periodOneOriginal_meanZero_iff]
  exact and_congr_right fun _ => and_iff_left (periodOneOriginal_periodic q)

/-- The genuine period-two L2 representative of a unit-period L2 potential. -/
def periodOneL2OriginalCoefficients (a : Coeff 2) : WeightedCoeff SpectralWeight.one.toWeight 2 :=
  (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).symm (Coeff.periodDouble a)

theorem periodOneL2OriginalCoefficients_apply (a : Coeff 2) (k : ℤ) :
    (periodOneL2OriginalCoefficients a).val k = Coeff.periodDouble a k := by
  change Coeff.periodDouble a k / (SpectralWeight.one.toWeight k : ℂ) = _
  simp only [SpectralWeight.one_apply, Complex.ofReal_one, div_one]

theorem periodOneL2OriginalCoefficients_toCoeff (a : Coeff 2) :
    SpectralWeight.one.toCoeff (periodOneL2OriginalCoefficients a) = Coeff.periodDouble a := by
  ext k
  rw [SpectralWeight.toCoeff_apply, periodOneL2OriginalCoefficients_apply]

/-- The H-minus-one realization agrees exactly with the already verified
original L2 operator realization, including every original smooth test. -/
theorem periodOneOriginal_L2 (a : Coeff 2) :
    periodOneOriginal (periodOneL2Inclusion a) = hillL2HminusOne (periodOneL2OriginalCoefficients a) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [hillL2HminusOne_coefficient, periodOneL2OriginalCoefficients_apply]
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he, periodOneOriginal_even, periodOneL2Inclusion_apply, Coeff.periodDouble_even]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he, periodOneOriginal_odd, Coeff.periodDouble_odd]

end NLS.KdV
