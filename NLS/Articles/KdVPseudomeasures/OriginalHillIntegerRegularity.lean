import NLS.Articles.KdVPseudomeasures.OriginalHillSobolevDiffeomorph
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeInjectivity

/-! Exact all-integer inverse regularity for ANY original rough source,
with the same full Fourier coefficients and same actual native map. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

def hillIntegerSourceInclusion (N : ℕ) :
    RealSignedHilbert (signedStepOrder 0 N) →L[ℝ] HillRealMeanZeroSource :=
  hillL2SourceInclusion.comp (signedIteratedInclusion 0 N)

def hillIntegerTargetInclusion (N : ℕ) :
    RealSignedHilbert (signedStepOrder (1/2) N) →L[ℝ] HillRealSignedTarget :=
  hillSignedHalfInclusion.comp (signedIteratedInclusion (1/2) N)

theorem hillIntegerSourceInclusion_apply (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 N)) (k : ℤ) :
    (hillIntegerSourceInclusion N q).val.val.val k=q.val.val.val k := by
  change (hillL2SourceInclusion (signedIteratedInclusion 0 N q)).val.val.val k=_
  rw [hillL2SourceInclusion_apply,signedIteratedInclusion_apply]

theorem hillIntegerTargetInclusion_apply (N : ℕ)
    (z : RealSignedHilbert (signedStepOrder (1/2) N)) (k : ℤ) :
    (hillIntegerTargetInclusion N z).val.val.val k=z.val.val.val k := by
  change (hillSignedHalfInclusion (signedIteratedInclusion (1/2) N z)).val.val.val k=_
  rw [hillSignedHalfInclusion_apply,signedIteratedInclusion_apply]

theorem hillIntegerSourceInclusion_injective (N : ℕ) :
    Function.Injective (hillIntegerSourceInclusion N) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  have he := congrArg (fun q => q.val.val.val k) h
  simpa only [hillIntegerSourceInclusion_apply] using he

theorem hillIntegerTargetInclusion_injective (N : ℕ) :
    Function.Injective (hillIntegerTargetInclusion N) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  have he := congrArg (fun z => z.val.val.val k) h
  simpa only [hillIntegerTargetInclusion_apply] using he

theorem hillIntegerSobolevEquiv_inclusion (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 N)) :
    hillIntegerTargetInclusion N ((hillIntegerSobolevEquiv N).equiv q)=
      hillRealSignedMap (hillIntegerSourceInclusion N q) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillIntegerTargetInclusion_apply,hillIntegerSobolevEquiv_apply]
  rfl

/-- The global inverse on the stronger scale recovers the identical
original rough source; no independent regularity hypothesis is needed. -/
theorem hillIntegerSobolevEquiv_symm_inclusion (N : ℕ) (q : HillRealMeanZeroSource)
    (z : RealSignedHilbert (signedStepOrder (1/2) N))
    (hz : hillIntegerTargetInclusion N z=hillRealSignedMap q) :
    hillIntegerSourceInclusion N ((hillIntegerSobolevEquiv N).equiv.symm z)=q := by
  apply injective_hillRealSignedMap
  rw [← hillIntegerSobolevEquiv_inclusion,(hillIntegerSobolevEquiv N).equiv.apply_symm_apply,hz]

theorem hillReal_integer_source_iff_native (N : ℕ) (q : HillRealMeanZeroSource) :
    (∃ a : RealSignedHilbert (signedStepOrder 0 N), hillIntegerSourceInclusion N a=q) ↔
      ∃ z : RealSignedHilbert (signedStepOrder (1/2) N), hillIntegerTargetInclusion N z=hillRealSignedMap q := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨(hillIntegerSobolevEquiv N).equiv a,hillIntegerSobolevEquiv_inclusion N a⟩
  · rintro ⟨z,hz⟩
    exact ⟨(hillIntegerSobolevEquiv N).equiv.symm z,hillIntegerSobolevEquiv_symm_inclusion N q z hz⟩

end NLS.Articles.KdVPseudomeasures
