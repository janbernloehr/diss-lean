import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapPhysicalRealization
import NLS.KdV.NativeHillContinuousSource

/-! # Spectral finite gaps make the canonical native continuous source smooth -/
noncomputable section
set_option autoImplicit false
open NLS.KdV NLS.ZakharovShabat NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- No smoothness is assumed of the original native finite-gap source.
Its canonical continuous representative is everywhere smooth. -/
theorem nativeHillContinuousSource_finiteGap_smooth (m : ℕ) (hm : 1≤m)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 n=0) :
    ContDiff ℝ ∞ (fun x : ℝ => nativeHillContinuousSource m hm q.val (x : AddCircle (2 : ℝ))) := by
  obtain ⟨f,hf,hp,hc⟩ := native_finiteGap_exists_smooth m q S hq
  rw [nativeHillContinuousSource_eq_of_coefficients m hm q.val f hf.continuous hp hc]
  exact hf

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
