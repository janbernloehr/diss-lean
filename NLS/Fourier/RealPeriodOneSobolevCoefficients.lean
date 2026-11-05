import NLS.Fourier.RealPeriodOneSobolevSpace
import NLS.SequenceSpaces.WeightedPeriodHalving
import NLS.SequenceSpaces.FourierRealEquivalentWeights

/-! A coefficient-preserving real Banach equivalence between original
physical real mean-zero period-one distributions and their native
weighted Fourier coefficients. The inverse recovers EVERY smooth-test
action, not merely a selected family of spectral data. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Fourier
open SmoothPeriodicTest PeriodicFourierLebesgue NLS.WeightedCoeff
variable (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

private def rawExtract : realPeriodOneSobolevSubmodule s p →L[ℝ] WeightedCoeff (periodOneSobolevPullback s) p :=
  ((WeightedCoeff.periodHalveCLM (Weight.sobolev s) p).restrictScalars ℝ).comp
    ((((sobolevCoefficients (L := 2) s p).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
      (realPeriodOneSobolevSubmodule s p).subtypeL)

private theorem rawExtract_apply (q : realPeriodOneSobolevSubmodule s p) (n : ℤ) :
    (rawExtract s p q).val n = q.val.val (mode (-(2*n))) := by
  change (WeightedCoeff.periodHalveCLM (Weight.sobolev s) p (sobolevCoefficients s p q.val)).val n = _
  rw [WeightedCoeff.periodHalveCLM_apply,sobolevCoefficients_apply]

private def zeroExtract : realPeriodOneSobolevSubmodule s p →L[ℝ] zeroModeSubmodule (periodOneSobolevPullback s) p :=
  (rawExtract s p).codRestrict ((zeroModeSubmodule (periodOneSobolevPullback s) p).restrictScalars ℝ) (by
    intro q
    change (rawExtract s p q).val 0=0
    rw [rawExtract_apply,mul_zero,neg_zero]
    exact q.property.2.1)

def realPeriodOneSobolevCoefficients : realPeriodOneSobolevSubmodule s p →L[ℝ]
    fourierRealZeroSubmodule (periodOneSobolevPullback s) p :=
  (zeroExtract s p).codRestrict (fourierRealZeroSubmodule (periodOneSobolevPullback s) p) (by
    intro q n
    change (rawExtract s p q).val (-n) = (starRingEnd ℂ) ((rawExtract s p q).val n)
    rw [rawExtract_apply,rawExtract_apply,mul_neg,neg_neg]
    exact realPeriodOneSobolev_real_coefficient s p q (2*n))

theorem realPeriodOneSobolevCoefficients_apply (q : realPeriodOneSobolevSubmodule s p) (n : ℤ) :
    (realPeriodOneSobolevCoefficients s p q).val.val.val n = q.val.val (mode (-(2*n))) :=
  rawExtract_apply s p q n

private def rawOriginal : fourierRealZeroSubmodule (periodOneSobolevPullback s) p →L[ℝ]
    FourierLebesgueSpace (2:ℝ) s p :=
  ((((sobolevCoefficients (L := 2) s p).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ)).comp
    (((WeightedCoeff.insertIsometry (Weight.sobolev s) (Coeff.parityEmbedding 0)).toContinuousLinearMap.restrictScalars ℝ).comp
      ((((zeroModeSubmodule (periodOneSobolevPullback s) p).subtypeL).restrictScalars ℝ).comp
        (fourierRealZeroSubmodule (periodOneSobolevPullback s) p).subtypeL))

private theorem rawOriginal_coefficient (a : fourierRealZeroSubmodule (periodOneSobolevPullback s) p) (n : ℤ) :
    (rawOriginal s p a).val (mode (-n)) =
      (WeightedCoeff.insertIsometry (Weight.sobolev s) (Coeff.parityEmbedding 0) a.val.val).val n := by
  change ((sobolevCoefficients (L := 2) s p) ((sobolevCoefficients (L := 2) s p).symm _)).val n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

private theorem rawOriginal_even (a : fourierRealZeroSubmodule (periodOneSobolevPullback s) p) (n : ℤ) :
    (rawOriginal s p a).val (mode (-(2*n))) = a.val.val.val n := by
  rw [rawOriginal_coefficient]
  simpa only [Coeff.parityEmbedding_apply,add_zero] using
    WeightedCoeff.insertIsometry_image (Weight.sobolev s) (Coeff.parityEmbedding 0) a.val.val n

private theorem rawOriginal_odd (a : fourierRealZeroSubmodule (periodOneSobolevPullback s) p) (n : ℤ) :
    (rawOriginal s p a).val (mode (-(2*n+1))) = 0 := by
  rw [rawOriginal_coefficient]
  apply WeightedCoeff.insertIsometry_outside
  rintro ⟨k,hk⟩
  change 2*k+0 = 2*n+1 at hk
  omega

private theorem rawOriginal_real (a : fourierRealZeroSubmodule (periodOneSobolevPullback s) p) (n : ℤ) :
    (rawOriginal s p a).val (mode n) = star ((rawOriginal s p a).val (mode (-n))) := by
  by_cases hn : n % 2 = 0
  · have he : n = 2*(n/2) := by omega
    have hl := rawOriginal_even s p a (-(n/2))
    have hneg : -(2*(-(n/2))) = 2*(n/2) := by ring
    rw [hneg] at hl
    rw [he,hl,rawOriginal_even]
    exact a.property (n/2)
  · have he : n = 2*(n/2)+1 := by omega
    have hl := rawOriginal_odd s p a (-(n/2)-1)
    have hneg : -(2*(-(n/2)-1)+1) = 2*(n/2)+1 := by ring
    rw [hneg] at hl
    rw [he,hl,rawOriginal_odd]
    exact (map_zero (starRingEnd ℂ)).symm

def realPeriodOneSobolevOriginal : fourierRealZeroSubmodule (periodOneSobolevPullback s) p →L[ℝ]
    realPeriodOneSobolevSubmodule s p :=
  (rawOriginal s p).codRestrict (realPeriodOneSobolevSubmodule s p) (by
    intro a
    apply (Distribution.isRealMeanZeroPeriodOne_iff_coefficients _).mpr
    refine ⟨?_,rawOriginal_real s p a,rawOriginal_odd s p a⟩
    have h := rawOriginal_even s p a 0
    simp only [mul_zero,neg_zero] at h
    exact h.trans a.val.property)

theorem realPeriodOneSobolevOriginal_even (a : fourierRealZeroSubmodule (periodOneSobolevPullback s) p) (n : ℤ) :
    (realPeriodOneSobolevOriginal s p a).val.val (mode (-(2*n))) = a.val.val.val n := rawOriginal_even s p a n

theorem realPeriodOneSobolevOriginal_odd (a : fourierRealZeroSubmodule (periodOneSobolevPullback s) p) (n : ℤ) :
    (realPeriodOneSobolevOriginal s p a).val.val (mode (-(2*n+1))) = 0 := rawOriginal_odd s p a n

theorem realPeriodOneSobolevCoefficients_original (a : fourierRealZeroSubmodule (periodOneSobolevPullback s) p) :
    realPeriodOneSobolevCoefficients s p (realPeriodOneSobolevOriginal s p a) = a := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext n
  rw [realPeriodOneSobolevCoefficients_apply,realPeriodOneSobolevOriginal_even]

theorem realPeriodOneSobolevOriginal_coefficients (q : realPeriodOneSobolevSubmodule s p) :
    realPeriodOneSobolevOriginal s p (realPeriodOneSobolevCoefficients s p q) = q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  by_cases hn : n % 2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he,realPeriodOneSobolevOriginal_even,realPeriodOneSobolevCoefficients_apply]
  · have he : n = 2*(n/2)+1 := by omega
    rw [he,realPeriodOneSobolevOriginal_odd,realPeriodOneSobolev_odd_coefficient]

def realPeriodOneSobolevCoefficientsEquiv : realPeriodOneSobolevSubmodule s p ≃L[ℝ]
    fourierRealZeroSubmodule (periodOneSobolevPullback s) p :=
  ContinuousLinearEquiv.equivOfInverse (realPeriodOneSobolevCoefficients s p) (realPeriodOneSobolevOriginal s p)
    (realPeriodOneSobolevOriginal_coefficients s p) (realPeriodOneSobolevCoefficients_original s p)

def realPeriodOneSignedSobolevEquiv (hs : 0 ≤ s) : realPeriodOneSobolevSubmodule s p ≃L[ℝ]
    fourierRealZeroSubmodule (Weight.signedSobolev s) p :=
  (realPeriodOneSobolevCoefficientsEquiv s p).trans (periodOneSobolevSignedEquiv s hs)

theorem realPeriodOneSignedSobolevEquiv_apply (hs : 0 ≤ s) (q : realPeriodOneSobolevSubmodule s p) (n : ℤ) :
    (realPeriodOneSignedSobolevEquiv s p hs q).val.val.val n = q.val.val (mode (-(2*n))) := by
  change (periodOneSobolevSignedEquiv s hs (realPeriodOneSobolevCoefficients s p q)).val.val.val n = _
  rw [periodOneSobolevSignedEquiv,fourierRealWeightEquiv_apply,realPeriodOneSobolevCoefficients_apply]

end NLS.Fourier
