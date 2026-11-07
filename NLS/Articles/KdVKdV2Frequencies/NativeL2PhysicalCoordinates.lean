import NLS.Articles.KdVKdV2Frequencies.RealL2ForwardRemainder
import NLS.Articles.KdVKdV2Frequencies.ActualKdVPhaseError
import NLS.SequenceSpaces.PhysicalRealMeanZeroPhaseFlowExponent

/-! Literal native coordinate compatibility for the SAME original L2 flow. -/
noncomputable section
open Set Complex NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies
open GlobalRoughAbelianForwardData

def originalL2NativeNormalization :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0) ≃ₗᵢ[ℝ] physicalRealDeletedSubmodule :=
  (physicalRealMeanZeroWeightedIsometry (Weight.sobolev 0) (Weight.sobolev_neg 0)).symm

def originalL2Coordinates (D : GlobalRoughAbelianForwardData) := D.originalNativeBirkhoff 0 (by norm_num)

def originalL2SignedFrequency (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) : ℤ → ℝ :=
  nativeTargetKdVSignedFrequency 1 (by norm_num) G (D.realNativeForward 1 (by norm_num) (originalL2NativeNormalization q))

theorem originalL2SignedFrequency_odd (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) (j : ℤ) :
    originalL2SignedFrequency D G q (-j)= -originalL2SignedFrequency D G q j :=
  nativeTargetKdVSignedFrequency_odd 1 (by norm_num) G _ j

theorem originalL2NativeSource (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    realNativeSource 1 (by norm_num) (originalL2NativeNormalization q)=
      originalL2MeanZeroSource (physicalRealToComplexMeanZeroWeighted (Weight.sobolev 0) q) := by
  have h := realNativeSource_original_weighted_coordinates 0 (by norm_num) q
  apply Subtype.ext
  funext j
  have hc := congrArg (fun z : PeriodOneHminusOne => z.val j) h
  simpa only [originalL2NativeNormalization,originalL2MeanZeroSource_apply,
    physicalRealToComplexMeanZeroWeighted_val,WeightedCoeff.sobolevInclusion_apply,zero_add] using! hc

theorem originalL2Coordinates_native_coefficient (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) (j : ℤ) :
    (originalL2Coordinates D q).val.val j=
      (D.realNativeTarget 1 (by norm_num) (originalL2NativeNormalization q)).val j := by
  rw [originalL2Coordinates,D.originalNativeBirkhoff_l2_coefficient]
  change _=(D.signed (realNativeSource 1 (by norm_num) (originalL2NativeNormalization q))).val j
  rw [originalL2NativeSource]

theorem originalL2NativeNormalization_flow (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ)
    (t : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    originalL2NativeNormalization (originalKdVBirkhoffFlow D 0 (by norm_num) G t q)=
      nativeKdVSourceFlow D 1 (by norm_num) G t (originalL2NativeNormalization q) := by
  simp only [originalL2NativeNormalization,originalKdVBirkhoffFlow,
    LinearIsometryEquiv.symm_apply_apply,zero_add]

theorem originalL2Coordinates_flow_coefficient (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ)
    (t : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) (j : ℤ) :
    (originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t q)).val.val j=
      Complex.exp (((t*originalL2SignedFrequency D G q j:ℝ):ℂ)*I)*(originalL2Coordinates D q).val.val j := by
  rw [originalL2Coordinates_native_coefficient,originalL2NativeNormalization_flow]
  have h := nativeKdVSourceFlow_raw_target D 1 (by norm_num) G t (originalL2NativeNormalization q)
  have hc := congrArg (fun z : WeightedCoeff (Weight.sobolev ((1:ℝ)-1/2)) 2 => z.val j) h
  simpa only [WeightedCoeff.phaseFlow_apply,←originalL2Coordinates_native_coefficient,originalL2SignedFrequency] using hc

theorem originalL2Coordinates_flow_phase (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ)
    (t : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t q)=
      physicalRealMeanZeroPhaseFlow (Weight.sobolev (0+1/2)) (originalL2SignedFrequency D G q)
        (originalL2SignedFrequency_odd D G q) t (originalL2Coordinates D q) := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  have h := physicalRealMeanZeroPhaseFlow_apply (Weight.sobolev (0+1/2))
    (originalL2SignedFrequency D G q) (originalL2SignedFrequency_odd D G q) t (originalL2Coordinates D q) j
  exact (originalL2Coordinates_flow_coefficient D G t q j).trans h.symm

end NLS.Articles.KdVKdV2Frequencies
