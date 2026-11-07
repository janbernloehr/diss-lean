import NLS.Articles.KdVPseudomeasures.OriginalHillNativeInjectivity
import NLS.Articles.KdVPseudomeasures.OriginalHillActionRotation

/-! Global source identities for the ACTUAL canonical-action flows.
Native injectivity lifts exact coordinate rotations to commuting,
2*pi-periodic original Hamiltonian flows. These are indexed action
flows, not the KdV evolution. -/
noncomputable section
open Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

private theorem exp_hillActionRotationRate_period (n : ℕ+) (k : ℤ) :
    exp (hillActionRotationRate n k*(2*Real.pi:ℝ))=1 := by
  unfold hillActionRotationRate
  split_ifs
  · have he : I*((2*Real.pi:ℝ):ℂ)=(2*Real.pi:ℂ)*I := by push_cast; ring
    rw [he,exp_two_pi_mul_I]
  · have he : -I*((2*Real.pi:ℝ):ℂ)=-((2*Real.pi:ℂ)*I) := by push_cast; ring
    rw [he,exp_neg,exp_two_pi_mul_I,inv_one]
  · simp

theorem originalHillNativeActionFlow_periodic (n : ℕ+) (q : HillRealMeanZeroSource) :
    Function.Periodic (originalHillNativeActionFlow n q) (2*Real.pi) := by
  intro t
  apply injective_hillRealSignedMap
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillRealSignedMap_coordinate,hillRealSignedMap_coordinate,
    originalHillNativeActionFlow_coordinate,originalHillNativeActionFlow_coordinate]
  have hp := exp_hillActionRotationRate_period n k
  push_cast at hp ⊢
  rw [mul_add,exp_add,hp,mul_one]

theorem originalHillNativeActionFlow_commute (n m : ℕ+) (q : HillRealMeanZeroSource) (s t : ℝ) :
    originalHillNativeActionFlow n (originalHillNativeActionFlow m q t) s=
      originalHillNativeActionFlow m (originalHillNativeActionFlow n q s) t := by
  apply injective_hillRealSignedMap
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillRealSignedMap_coordinate,hillRealSignedMap_coordinate]
  simp_rw [originalHillNativeActionFlow_coordinate]
  ring

end NLS.Articles.KdVPseudomeasures
