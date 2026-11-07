import NLS.Articles.KdVConvexity.FourierLebesguePhaseEvolution

/-! # The SAME physical evolution in every native order and exponent

Equality of original source coefficients gives equality of the actual
signed Birkhoff coordinates, original actions and physical frequencies.
Injectivity of the already-fixed rough map identifies the evolved sources.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem fourierLebesguePhysicalActions_eq_of_raw_eq
    (s t : ℝ) (hs : -1/2≤s) (ht : -1/2≤t)
    (p r : ℝ≥0∞) (hp : p≠⊤) (hr : r≠⊤) (h2p : 2≤p) (h2r : 2≤r)
    [Fact (1≤p)] [Fact (1≤r)]
    (a : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p)
    (b : physicalRealMeanZeroWeightedExponent (Weight.sobolev (t+1/2)) r)
    (he : ∀ j : ℤ, a.val.val j=b.val.val j) :
    fourierLebesguePhysicalActions s hs p hp h2p a=fourierLebesguePhysicalActions t ht r hr h2r b := by
  apply Subtype.ext
  funext k
  rw [fourierLebesguePhysicalActions_apply,fourierLebesguePhysicalActions_apply,he,he]

end NLS.Articles.KdVConvexity

namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem fourierLebesguePhaseEvolution_signed (D : GlobalRoughAbelianForwardData)
    (B : BasePhysicalFrequencyExtension) (s : ℝ) (hs : -1/2≤s)
    (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] (time : ℝ)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) (j : ℤ) :
    (D.signed (fourierLebesgueSourceInclusion s hs p hp h2p
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p time q).val)).val j=
      Complex.exp (((time*signedPositiveFrequency
        (B.fourierLebesguePhysicalFrequency s hs p hp h2p (D.fourierLebesgueForward s hs p hp h2p q)) j : ℝ) : ℂ)*I)*
          (D.signed (fourierLebesgueSourceInclusion s hs p hp h2p q.val)).val j := by
  rw [←D.fourierLebesgueForward_apply s hs p hp h2p _ j,
    D.fourierLebesguePhaseEvolution_coordinates,B.fourierLebesguePhysicalPhaseFlow_apply,
    D.fourierLebesgueForward_apply]

theorem fourierLebesguePhaseEvolution_compatible (D : GlobalRoughAbelianForwardData)
    (B : BasePhysicalFrequencyExtension)
    (s t : ℝ) (hs : -1/2≤s) (ht : -1/2≤t)
    (p r : ℝ≥0∞) (hp : p≠⊤) (hr : r≠⊤) (h2p : 2≤p) (h2r : 2≤r)
    [Fact (1≤p)] [Fact (1≤r)]
    (a : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (b : physicalRealMeanZeroWeightedExponent (Weight.sobolev t) r)
    (he : ∀ j : ℤ, a.val.val j=b.val.val j) (time : ℝ) : ∀ j : ℤ,
    (D.fourierLebesguePhaseEvolution B s hs p hp h2p time a).val.val j=
      (D.fourierLebesguePhaseEvolution B t ht r hr h2r time b).val.val j := by
  have hq : fourierLebesgueSourceInclusion s hs p hp h2p a.val=
      fourierLebesgueSourceInclusion t ht r hr h2r b.val := by
    apply Subtype.ext
    funext j
    simpa only [fourierLebesgueSourceInclusion_apply] using he j
  have hz (j : ℤ) : (D.fourierLebesgueForward s hs p hp h2p a).val.val j=
      (D.fourierLebesgueForward t ht r hr h2r b).val.val j := by
    rw [D.fourierLebesgueForward_apply,D.fourierLebesgueForward_apply,hq]
  have hacts := fourierLebesguePhysicalActions_eq_of_raw_eq s t hs ht p r hp hr h2p h2r _ _ hz
  have hfreq : B.fourierLebesguePhysicalFrequency s hs p hp h2p (D.fourierLebesgueForward s hs p hp h2p a)=
      B.fourierLebesguePhysicalFrequency t ht r hr h2r (D.fourierLebesgueForward t ht r hr h2r b) := by
    funext n
    unfold BasePhysicalFrequencyExtension.fourierLebesguePhysicalFrequency
    rw [hacts]
  let u := D.fourierLebesguePhaseEvolution B s hs p hp h2p time a
  let v := D.fourierLebesguePhaseEvolution B t ht r hr h2r time b
  have hsign : D.signed (fourierLebesgueSourceInclusion s hs p hp h2p u.val)=
      D.signed (fourierLebesgueSourceInclusion t ht r hr h2r v.val) := by
    apply Subtype.ext
    funext j
    rw [D.fourierLebesguePhaseEvolution_signed,D.fourierLebesguePhaseEvolution_signed,hfreq,hq]
  have hu := D.signed_injective_real_meanZero _ _
    (fourierLebesgueSourceInclusion_real s hs p hp h2p u)
    (fourierLebesgueSourceInclusion_real t ht r hr h2r v)
    (by simpa only [fourierLebesgueSourceInclusion_apply] using u.property.2)
    (by simpa only [fourierLebesgueSourceInclusion_apply] using v.property.2) hsign
  intro j
  simpa only [fourierLebesgueSourceInclusion_apply] using congrArg (fun q => q.val j) hu

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
