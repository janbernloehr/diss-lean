import NLS.Fourier.SmoothPeriodicCoefficients
import NLS.Fourier.IntervalBilinearParseval
import NLS.SequenceSpaces.SignedSobolevRealScale
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.SignedSobolevPositiveEquivalence
import NLS.SequenceSpaces.WeightComparison

/-! Arbitrary smooth real mean-zero unit-period fields in the actual
signed Sobolev models. All coefficients are the original Fourier integrals. -/
noncomputable section
open Complex MeasureTheory NLS.WeightedCoeff
open scoped ContDiff ENNReal ComplexConjugate
namespace NLS.Fourier

theorem periodOneCoefficient_zero_of_mean_zero (f : ℝ → ℂ)
    (h0 : (∫ x in (0 : ℝ)..1, f x) = 0) : periodOneCoefficient f 0 = 0 := by
  rw [periodOneCoefficient, ← unitFourierCoefficient_eq_fourierCoeffOn]
  simpa only [unitFourierCoefficient, mul_zero, neg_zero, wave_zero, mul_one] using h0

theorem periodOneCoefficient_reflection_of_real (f : ℝ → ℂ)
    (hr : ∀ x, conj (f x) = f x) (k : ℤ) :
    periodOneCoefficient f (-k) = conj (periodOneCoefficient f k) := by
  have he : (fun x => conj (f x)) = f := funext hr
  have h := unitFourierCoefficient_conj f (-k)
  rw [he, neg_neg] at h
  simpa only [periodOneCoefficient, ← unitFourierCoefficient_eq_fourierCoeffOn] using h

def smoothRealMeanZeroPeriodOneData (s : ℝ) (hs : 0 ≤ s) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hr : ∀ x, conj (f x) = f x) (h0 : periodOneCoefficient f 0 = 0) :
    fourierRealZeroSubmodule (Weight.signedSobolev s) 2 := by
  let b : WeightedCoeff (Weight.sobolev s) 1 := ⟨periodOneCoefficient f,
    memlp_periodOneCoefficient_sobolev_one s hs f hf hp⟩
  let c := WeightedCoeff.exponentInclusion (Weight.sobolev s) (by norm_num : (1 : ℝ≥0∞) ≤ 2) b
  have hw : ∀ k, Weight.signedSobolev s k ≤ 1 * Weight.sobolev s k := by
    intro k
    simpa only [one_mul] using Weight.signedSobolev_le_sobolev s hs k
  let v := WeightComparison.map (Weight.sobolev s) (Weight.signedSobolev s) 1 zero_le_one hw c
  have hv (k : ℤ) : v.val k = periodOneCoefficient f k :=
    (WeightComparison.map_apply _ _ 1 zero_le_one hw c k).trans
      (WeightedCoeff.exponentInclusion_apply _ _ b k)
  exact ⟨⟨v, by change v.val 0 = 0; rw [hv, h0]⟩,
    by intro k; change v.val (-k) = conj (v.val k); rw [hv, hv];
       exact periodOneCoefficient_reflection_of_real f hr k⟩

@[simp] theorem smoothRealMeanZeroPeriodOneData_apply (s : ℝ) (hs : 0 ≤ s) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hr : ∀ x, conj (f x) = f x) (h0 : periodOneCoefficient f 0 = 0) (k : ℤ) :
    (smoothRealMeanZeroPeriodOneData s hs f hf hp hr h0).val.val.val k = periodOneCoefficient f k := by
  unfold smoothRealMeanZeroPeriodOneData
  rw [WeightComparison.map_apply]
  exact WeightedCoeff.exponentInclusion_apply (Weight.sobolev s) _ _ k

end NLS.Fourier
