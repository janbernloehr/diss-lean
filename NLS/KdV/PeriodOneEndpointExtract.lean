import NLS.KdV.PeriodOneEndpointOriginal
import NLS.SequenceSpaces.WeightedReindexInfinity

/-! The bounded inverse adapter for the ACTUAL original physically
period-one endpoint distributions, retaining all original test actions. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

theorem periodOneEndpointWeight_reverse (r : ℝ) (hr : 0 ≤ r) (n : ℤ) :
    Weight.sobolev (-r) n ≤ (2:ℝ)^r*periodOneEndpointWeight r n := by
  have h := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < 1+2*|(n:ℝ)|)
    (by linarith : 1+2*|(n:ℝ)| ≤ 2*(1+|(n:ℝ)|)) (neg_nonpos.mpr hr)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ 1+|(n:ℝ)|)] at h
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) r)
  rw [← mul_assoc,← Real.rpow_add (by norm_num : (0:ℝ) < 2),add_neg_cancel,Real.rpow_zero,one_mul] at hm
  simpa only [periodOneEndpointWeight,Weight.pullback_apply,Coeff.parityEmbedding_apply,add_zero,
    Weight.sobolev_apply,Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)] using hm

def periodOneEndpointExtract (r : ℝ) (hr : 0 ≤ r) :
    FourierLebesgueSpace (2:ℝ) (-r) ⊤ →L[ℂ] WeightedCoeff (Weight.sobolev (-r)) ⊤ :=
  (WeightedCoeff.weightedMultiplierCLM (periodOneEndpointWeight r) (Weight.sobolev (-r))
    (fun _ => (1:ℂ)) ((2:ℝ)^r) (by positivity)
      (fun n => by simpa only [norm_one,mul_one] using periodOneEndpointWeight_reverse r hr n)).comp
    ((WeightedCoeff.reindexInfinityCLM (Weight.sobolev (-r)) (Coeff.parityEmbedding 0)).comp
      (sobolevCoefficients (-r) ⊤).toContinuousLinearEquiv.toContinuousLinearMap)

theorem periodOneEndpointExtract_apply (r : ℝ) (hr : 0 ≤ r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (n : ℤ) :
    (periodOneEndpointExtract r hr q).val n=q.val (mode (-(2*n))) := by
  change (1:ℂ)*(WeightedCoeff.reindexInfinityCLM _ _ (sobolevCoefficients (-r) ⊤ q)).val n=_
  rw [one_mul,WeightedCoeff.reindexInfinityCLM_apply]
  simp only [Coeff.parityEmbedding_apply,add_zero]
  rfl

theorem norm_periodOneEndpointExtract_le (r : ℝ) (hr : 0 ≤ r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) : ‖periodOneEndpointExtract r hr q‖ ≤ (2:ℝ)^r*‖q‖ := by
  have hm : ∀ n, Weight.sobolev (-r) n*‖(1:ℂ)‖ ≤ (2:ℝ)^r*periodOneEndpointWeight r n :=
    fun n => by simpa only [norm_one,mul_one] using periodOneEndpointWeight_reverse r hr n
  let a := WeightedCoeff.reindexInfinityCLM (Weight.sobolev (-r)) (Coeff.parityEmbedding 0)
    (sobolevCoefficients (-r) ⊤ q)
  change ‖WeightedCoeff.weightedMultiplier (periodOneEndpointWeight r) (Weight.sobolev (-r))
    (fun _ => (1:ℂ)) ((2:ℝ)^r) hm a‖ ≤ _
  apply (WeightedCoeff.norm_weightedMultiplier_le _ _ _ _ (by positivity) hm a).trans
  have hh := WeightedCoeff.norm_reindexInfinityCLM_le (Weight.sobolev (-r)) (Coeff.parityEmbedding 0)
    (sobolevCoefficients (-r) ⊤ q)
  rw [LinearIsometryEquiv.norm_map] at hh
  exact mul_le_mul_of_nonneg_left hh (by positivity)

theorem periodOneEndpointExtract_original (r : ℝ) (hr : 0 ≤ r)
    (q : WeightedCoeff (Weight.sobolev (-r)) ⊤) :
    periodOneEndpointExtract r hr (periodOneEndpointOriginal r hr q)=q := by
  apply Subtype.ext
  funext n
  rw [periodOneEndpointExtract_apply,periodOneEndpointOriginal_even]

theorem periodOneEndpointOriginal_extract (r : ℝ) (hr : 0 ≤ r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hp : IsPeriodicDistribution 1 q.val.toTempered) :
    periodOneEndpointOriginal r hr (periodOneEndpointExtract r hr q)=q := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  by_cases hk : k % 2=0
  · have he : k=2*(k/2) := by omega
    rw [he,periodOneEndpointOriginal_even,periodOneEndpointExtract_apply]
  · have he : k=2*(k/2)+1 := by omega
    rw [he,periodOneEndpointOriginal_odd]
    exact ((Distribution.toTempered_period_one_iff_odd q.val).mp hp (k/2)).symm

end NLS.KdV
