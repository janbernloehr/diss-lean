import NLS.Articles.KdVConvexity.BasePhysicalFrequencyReality
import NLS.KdV.HillRoughFourierLebesgueInverseCompatibility
import NLS.SequenceSpaces.WeightedSignedPairActions
import NLS.SequenceSpaces.SobolevHalfWeights

/-! # The original physical actions in their exact negative-order base norm

The fixed weak target normalization supplies an entire quadratic action
map. Its raw positive action is exactly z_n*z_(-n), with no extra weight
or factor. On the physical real slice every action is nonnegative.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

def weakPhysicalActions (z : physicalRealDeletedSubmodule) : BaseActionSpace :=
  WeightedCoeff.signedPairActions baseActionWeight actionIndexEquiv z.val

theorem weakPhysicalActions_nonnegative (z : physicalRealDeletedSubmodule) :
    weakPhysicalActions z∈WeightedCoeff.nonnegativeLocus baseActionWeight 1 :=
  WeightedCoeff.signedPairActions_nonnegative _ _ z.val z.property

theorem continuous_weakPhysicalActions : Continuous weakPhysicalActions := by
  have ha := WeightedCoeff.analyticOnNhd_signedPairActions baseActionWeight actionIndexEquiv
  exact (continuous_iff_continuousAt.mpr (fun b => (ha b (mem_univ _)).continuousAt)).comp
    continuous_subtype_val

def fourierLebesguePhysicalActions (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞)
    (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) : BaseActionSpace :=
  weakPhysicalActions (fourierLebesgueTargetNormalization s hs p hp h2p z)

theorem fourierLebesguePhysicalActions_nonnegative (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞)
    (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) :
    fourierLebesguePhysicalActions s hs p hp h2p z∈WeightedCoeff.nonnegativeLocus baseActionWeight 1 :=
  weakPhysicalActions_nonnegative _

theorem continuous_fourierLebesguePhysicalActions (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞)
    (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    Continuous (fourierLebesguePhysicalActions s hs p hp h2p) :=
  continuous_weakPhysicalActions.comp (fourierLebesgueTargetNormalization s hs p hp h2p).continuous

theorem fourierLebesguePhysicalActions_apply (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞)
    (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p) (k : ℤ) :
    (fourierLebesguePhysicalActions s hs p hp h2p z).val k=
      z.val.val (positiveIndexInjection actionIndexEquiv k)*z.val.val (-positiveIndexInjection actionIndexEquiv k) := by
  have hn : 0<positiveIndexInjection actionIndexEquiv k := by
    change (0 : ℤ)<(actionIndexEquiv k : ℤ)
    exact_mod_cast (actionIndexEquiv k).pos
  change (WeightedCoeff.signedPairActions _ _
    (fourierLebesgueTargetNormalization s hs p hp h2p z).val).val k=_
  rw [WeightedCoeff.signedPairActions_apply,fourierLebesgueTargetNormalization_val,
    WeightedCoeff.meanZeroWeightedProjection_apply_other _ _ _ (by omega),
    WeightedCoeff.meanZeroWeightedProjection_apply_other _ _ _ (by omega),
    fourierLebesgueTargetInclusion_apply,fourierLebesgueTargetInclusion_apply,Weight.sobolev_neg]
  have hw : (Weight.sobolev (-1/2) (positiveIndexInjection actionIndexEquiv k) : ℂ)^2=
      (baseActionWeight k : ℂ) := by
    rw [←ofReal_pow,pow_two,←Weight.sobolev_add,show (-1/2 : ℝ)+(-1/2) = -1 by ring,
      Weight.sobolev_minus_one_apply]
    simp only [baseActionWeight,positiveIndexInjection,Int.cast_natCast,abs_of_pos (show (0 : ℝ)<(actionIndexEquiv k : ℝ) by exact_mod_cast (actionIndexEquiv k).pos)]
  rw [show ((Weight.sobolev (-1/2) (positiveIndexInjection actionIndexEquiv k) : ℂ)*
      z.val.val (positiveIndexInjection actionIndexEquiv k))*
      ((Weight.sobolev (-1/2) (positiveIndexInjection actionIndexEquiv k) : ℂ)*
        z.val.val (-positiveIndexInjection actionIndexEquiv k))=
      (Weight.sobolev (-1/2) (positiveIndexInjection actionIndexEquiv k) : ℂ)^2*
        (z.val.val (positiveIndexInjection actionIndexEquiv k)*z.val.val (-positiveIndexInjection actionIndexEquiv k)) by ring,
    hw,mul_div_cancel_left₀ _ (baseActionWeight.complex_ne_zero k)]

end NLS.Articles.KdVConvexity
