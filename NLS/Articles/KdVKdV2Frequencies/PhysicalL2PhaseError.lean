import NLS.Articles.KdVKdV2Frequencies.NativeL2PhysicalCoordinates
import NLS.SequenceSpaces.PhysicalRealMeanZeroSobolevInclusion
import NLS.SequenceSpaces.SobolevDerivative

/-! The actual phase error in the ORIGINAL physical real mean-zero
h^(3/2) target, with the SAME bound linear in time. -/
noncomputable section
open Set Complex NLS.KdV
open scoped ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies

theorem originalL2RawPhaseError_coefficient (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (t : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) (j : ℤ) :
    (nativeKdVPhaseError D G h t (originalL2NativeNormalization q)).val j=
      (originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t q)).val.val j-
        Complex.exp (((t*airySignedFrequency j:ℝ):ℂ)*I)*(originalL2Coordinates D q).val.val j := by
  have hc := nativeKdVPhaseError_apply D G h t (originalL2NativeNormalization q) j
  rw [←originalL2Coordinates_native_coefficient] at hc
  change _=(Complex.exp (((t*originalL2SignedFrequency D G q j:ℝ):ℂ)*I)-
    Complex.exp (((t*airySignedFrequency j:ℝ):ℂ)*I))*(originalL2Coordinates D q).val.val j at hc
  rw [hc,originalL2Coordinates_flow_coefficient]
  ring

theorem originalL2RawPhaseError_mem (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (t : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    nativeKdVPhaseError D G h t (originalL2NativeNormalization q)∈
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℝ)-1/2+1)) := by
  let A : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (0+1/2)) :=
    ⟨WeightedCoeff.phaseFlow (Weight.sobolev (0+1/2)) airySignedFrequency t (originalL2Coordinates D q).val,
      physicalRealMeanZero_phaseFlow_mem (Weight.sobolev (0+1/2)) airySignedFrequency airySignedFrequency_odd t
        (originalL2Coordinates D q)⟩
  let Q := originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t q)-A
  have hc (j : ℤ) : (nativeKdVPhaseError D G h t (originalL2NativeNormalization q)).val j=Q.val.val j := by
    have hp : A.val.val j=Complex.exp (((t*airySignedFrequency j:ℝ):ℂ)*I)*(originalL2Coordinates D q).val.val j :=
      WeightedCoeff.phaseFlow_apply _ _ _ _ _
    change _=(originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t q)).val.val j-A.val.val j
    exact (originalL2RawPhaseError_coefficient D G h t q j).trans
      (congrArg (fun c : ℂ => (originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t q)).val.val j-c) hp).symm
  constructor
  · intro j
    exact (hc (-j)).trans ((Q.property.1 j).trans (congrArg conj (hc j).symm))
  · exact (hc 0).trans Q.property.2

def originalL2StrongPhaseError (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (t : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (1+1/2)) :=
  physicalRealMeanZeroSobolevInclusion (by norm_num : (1+1/2:ℝ)≤1-1/2+1)
    ⟨nativeKdVPhaseError D G h t (originalL2NativeNormalization q),originalL2RawPhaseError_mem D G h t q⟩

theorem originalL2StrongPhaseError_coefficient (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (t : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) (j : ℤ) :
    (originalL2StrongPhaseError D G h t q).val.val j=
      (originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t q)).val.val j-
        Complex.exp (((t*airySignedFrequency j:ℝ):ℂ)*I)*(originalL2Coordinates D q).val.val j := by
  unfold originalL2StrongPhaseError
  rw [physicalRealMeanZeroSobolevInclusion_coefficient]
  exact originalL2RawPhaseError_coefficient D G h t q j

theorem norm_originalL2StrongPhaseError_le (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (t : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    ‖originalL2StrongPhaseError D G h t q‖≤‖nativeKdVPhaseError D G h t (originalL2NativeNormalization q)‖ := by
  change ‖WeightedCoeff.sobolevInclusion (by norm_num : (1+1/2:ℝ)≤1-1/2+1)
    (nativeKdVPhaseError D G h t (originalL2NativeNormalization q))‖≤_
  exact WeightedCoeff.norm_sobolevInclusion_le _ _

theorem exists_bounded_originalL2StrongPhaseError_bound (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (S : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0))) (hS : Bornology.IsBounded S) :
    ∃ C : ℝ,0≤C ∧ ∀ q∈S,∀ t : ℝ,‖originalL2StrongPhaseError D G h t q‖≤|t| * C := by
  have hSn : Bornology.IsBounded (originalL2NativeNormalization '' S) :=
    originalL2NativeNormalization.isometry.lipschitz.isBounded_image hS
  obtain ⟨C,hC,hb⟩ := exists_bounded_nativeKdVPhaseError_bound D G h _ hSn
  exact ⟨C,hC,fun q hq t => (norm_originalL2StrongPhaseError_le D G h t q).trans
    (hb (originalL2NativeNormalization q) ⟨q,hq,rfl⟩ t)⟩

end NLS.Articles.KdVKdV2Frequencies
