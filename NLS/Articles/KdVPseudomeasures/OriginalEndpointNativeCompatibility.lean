import NLS.Articles.KdVPseudomeasures.OriginalHighPairCompatibility
import NLS.KdV.PeriodOneEndpointOriginal

/-! The native endpoint inclusion and the actual original physical
distribution adapter commute on every coefficient, including infinity. -/
noncomputable section
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem exists_endpointNativeInclusion (r : ℝ) (hr : AdmissiblePredualOrder r) :
    ∃ f : WeightedCoeff (Weight.sobolev (-r)) ⊤ →L[ℂ] PeriodOneHminusOne,
      ∀ q n, (f q).val n=q.val n :=
  ⟨WeightedCoeff.endpointLowerInclusion (-r) (-1) (by norm_num)
    (admissible_hminusOne_threshold r hr),fun q n =>
      WeightedCoeff.endpointLowerInclusion_apply _ _ _ _ q n⟩

/-- The unique coefficient-preserving inclusion, packaged through its
verified existence so downstream kernels need not normalize the Holder construction. -/
def endpointNativeInclusion (r : ℝ) (hr : AdmissiblePredualOrder r) :
    WeightedCoeff (Weight.sobolev (-r)) ⊤ →L[ℂ] PeriodOneHminusOne :=
  Classical.choose (exists_endpointNativeInclusion r hr)

theorem endpointNativeInclusion_apply (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeightedCoeff (Weight.sobolev (-r)) ⊤) (n : ℤ) :
    (endpointNativeInclusion r hr q).val n=q.val n :=
  Classical.choose_spec (exists_endpointNativeInclusion r hr) q n

theorem endpointNativeInclusion_eq_lowerInclusion (r : ℝ) (hr : AdmissiblePredualOrder r) :
    endpointNativeInclusion r hr=WeightedCoeff.endpointLowerInclusion (-r) (-1) (by norm_num)
      (admissible_hminusOne_threshold r hr) := by
  apply ContinuousLinearMap.ext
  intro q
  apply Subtype.ext
  funext n
  rw [endpointNativeInclusion_apply,WeightedCoeff.endpointLowerInclusion_apply]

theorem sourceNativePeriodOneCLM_endpointOriginal (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeightedCoeff (Weight.sobolev (-r)) ⊤) :
    sourceNativePeriodOneCLM r hr (periodOneEndpointOriginal r hr.1 q)=endpointNativeInclusion r hr q := by
  apply Subtype.ext
  funext n
  rw [sourceNativePeriodOneCLM_apply,periodOneOriginalExtract_apply,sourceComplexHminusOne_val,
    periodOneEndpointOriginal_even,endpointNativeInclusion_apply]

end NLS.Articles.KdVPseudomeasures
