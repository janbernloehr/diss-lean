import NLS.Articles.KdVKdV2Frequencies.NativeActionNormalization
import NLS.SequenceSpaces.RealActionLocalImage

/-! Every actual original native source neighborhood realizes a full
relative neighborhood of its nonnegative Birkhoff action. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem nativeActionCoordinates_local_image
    (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (a₀ : physicalRealDeletedSubmodule) (T : Set physicalRealDeletedSubmodule)
    (hT : IsOpen T) (haT : a₀∈T) :
    ∃ r : ℝ, 0<r ∧ ball (nativeActionCoordinates D t ht a₀) r∩Coeff.nonnegativeLocus 1⊆
      nativeActionCoordinates D t ht '' T := by
  let S : {z : Coeff 2 × Coeff 2 // z∈Coeff.realPairLocus 2} → physicalRealDeletedSubmodule :=
    fun z => ⟨signedPairToDeleted actionIndexEquiv z.val,signedPairToDeleted_real _ _ z.property⟩
  have hS : Continuous S :=
    ((signedPairToDeleted actionIndexEquiv).continuous.comp continuous_subtype_val).subtype_mk _
  let R := fun z => D.realNativeInverse t ht (S z)
  have hR : Continuous R := (D.realNativeInverse_analytic t ht).continuous.comp hS
  let z₀ : {z : Coeff 2 × Coeff 2 // z∈Coeff.realPairLocus 2} :=
    ⟨deletedToSignedPair actionIndexEquiv (D.realNativeForward t ht a₀).val,
      deletedToSignedPair_real _ _ (D.realNativeForward t ht a₀).property⟩
  have hz₀ : R z₀=a₀ := by
    have hsz : S z₀=D.realNativeForward t ht a₀ :=
      Subtype.ext (signedPairToDeleted_apply_inverse actionIndexEquiv _)
    change D.realNativeInverse t ht (S z₀)=a₀
    rw [hsz,D.realNativeInverse_forward]
  have he (z : {z : Coeff 2 × Coeff 2 // z∈Coeff.realPairLocus 2}) :
      nativeActionCoordinates D t ht (R z)=quadraticActionsExponent (q := 1) z.val := by
    unfold nativeActionCoordinates
    change quadraticActionsExponent (q := 1) (deletedToSignedPair actionIndexEquiv
      (D.realNativeForward t ht (D.realNativeInverse t ht (S z))).val)=_
    rw [D.realNativeForward_inverse]
    ext k
    rw [quadraticActions_deletedToSignedPair_apply]
    exact signedPairToDeleted_product actionIndexEquiv z.val k
  have H := Coeff.exists_real_action_ball_in_source_image (nativeActionCoordinates D t ht) R hR he z₀ T hT
    (by rwa [hz₀])
  rwa [hz₀] at H

end NLS.Articles.KdVKdV2Frequencies
