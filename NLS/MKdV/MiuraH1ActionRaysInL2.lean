import NLS.MKdV.MiuraNativePhysicalActionRays
import NLS.MKdV.MiuraFiniteEncodedActionRealization

/-! # Native H¹ action rays retain their raw physical amplitudes in L²

Increasing a selected physical action at H¹ changes the same literal
action by the same amount in the weight-one L² action space.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem exists_H1_profile_on_L2_positive_action_ray (a : MiuraRealSobolevSource 1)
    (n : ℤ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    ∃ b : MiuraRealSobolevSource 1,
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 b) =
        miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 a)+
          (t : ℂ) • (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1,0) := by
  obtain ⟨b,hb⟩ := exists_native_profile_on_positive_action_ray 1 le_rfl a n hn t ht
  refine ⟨b,?_⟩
  apply Prod.ext
  · apply Subtype.ext
    funext k
    have h := congrArg (fun q : MiuraNativeActionMeanTarget 1 => q.1.val k) hb
    change (miuraSobolevActionSequence 1 b.val).val k =
      (miuraSobolevActionSequence 1 a.val).val k+(t : ℂ)*
        (WeightedCoeff.single (p := 1) (miuraSpectralActionWeight 1) n 1).val k at h
    rw [WeightedCoeff.single_val] at h
    change (miuraL2ActionSequence (miuraPhysicalSobolevL2SourceInclusion 1 b).val).val k =
      (miuraL2ActionSequence (miuraPhysicalSobolevL2SourceInclusion 1 a).val).val k+(t : ℂ)*
        (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1).val k
    rw [← miuraSobolevActionSequence_L2_coefficients 1 b k,
      ← miuraSobolevActionSequence_L2_coefficients 1 a k,WeightedCoeff.single_val]
    exact h
  · have h := congrArg Prod.snd hb
    change b.val.val 0 = a.val.val 0+(t : ℂ)*0 at h
    change (miuraPhysicalSobolevL2SourceInclusion 1 b).val 0 =
      (miuraPhysicalSobolevL2SourceInclusion 1 a).val 0+(t : ℂ)*0
    rw [miuraPhysicalSobolevL2SourceInclusion_apply,miuraPhysicalSobolevL2SourceInclusion_apply]
    exact h

end NLS.MKdV
