import NLS.Articles.KdVConvexity.FourierLebesguePhaseCoordinateDerivatives
import NLS.Articles.KdVConvexity.FourierLebesgueFrequencyRecovery

/-! # Actual phase frequencies and closed coordinates at each time -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity
variable (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
  (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]

theorem fourierLebesguePhaseEvolution_frequency (t : ℝ)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    B.fourierLebesguePhysicalFrequency s hs p hp h2p
      (D.fourierLebesgueForward s hs p hp h2p (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q))=
      B.fourierLebesguePhysicalFrequency s hs p hp h2p (D.fourierLebesgueForward s hs p hp h2p q) := by
  rw [D.fourierLebesguePhaseEvolution_coordinates,B.fourierLebesguePhysicalPhaseFlow_frequency]

theorem fourierLebesguePhaseEvolution_frequency_eq_native (t : ℝ)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (a : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
    (ha : nativeHillSource 1 a.val=fourierLebesgueSourceInclusion s hs p hp h2p
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q).val) (n : ℕ+) :
    B.fourierLebesguePhysicalFrequency s hs p hp h2p (D.fourierLebesgueForward s hs p hp h2p q) n=
      D.nativeSourceHierarchyFrequency 1 3 (by norm_num) a n := by
  have hz (j : ℤ) :
      (D.fourierLebesgueForward s hs p hp h2p (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q)).val.val j=
      (D.signed (nativeHillSource 1 a.val)).val j := by
    rw [D.fourierLebesgueForward_apply,ha]
  have he := B.fourierLebesgueFrequency_eq_native D a s hs p hp h2p _ hz n
  rw [D.fourierLebesguePhaseEvolution_frequency] at he
  exact he

theorem fourierLebesguePhaseEvolution_component_zero_outside (t : ℝ)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (S : Finset ℕ+)
    (hS : ∀ n : ℕ+, n∉S → (D.fourierLebesgueForward s hs p hp h2p q).val.val (n : ℤ)=0)
    (σ : Bool) (n : ℕ+) (hn : n∉S) :
    hillRoughSignedAbelianComponent D.signed σ n
      (fourierLebesgueSourceInclusion s hs p hp h2p (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q).val)=0 := by
  let u := D.fourierLebesguePhaseEvolution B s hs p hp h2p t q
  let z := D.fourierLebesgueForward s hs p hp h2p u
  have hz : z.val.val (n : ℤ)=0 := by
    change (D.fourierLebesgueForward s hs p hp h2p (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q)).val.val (n : ℤ)=0
    rw [D.fourierLebesguePhaseEvolution_coordinates,B.fourierLebesguePhysicalPhaseFlow_positive,hS n hn,mul_zero]
  cases σ
  · change (D.signed (fourierLebesgueSourceInclusion s hs p hp h2p u.val)).val (-(n : ℤ))=0
    rw [←D.fourierLebesgueForward_apply s hs p hp h2p u (-(n : ℤ))]
    change z.val.val (-(n : ℤ))=0
    rw [z.property.1,hz,map_zero]
  · change (D.signed (fourierLebesgueSourceInclusion s hs p hp h2p u.val)).val (n : ℤ)=0
    rw [←D.fourierLebesgueForward_apply s hs p hp h2p u (n : ℤ)]
    exact hz

theorem hasDerivAt_fourierLebesguePhaseEvolution_component_finiteAction (t : ℝ)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (a : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
    (ha : nativeHillSource 1 a.val=fourierLebesgueSourceInclusion s hs p hp h2p
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q).val)
    (S : Finset ℕ+)
    (hS : ∀ n : ℕ+, n∉S → (D.fourierLebesgueForward s hs p hp h2p q).val.val (n : ℤ)=0)
    (σ : Bool) (n : ℕ+) :
    HasDerivAt (fun u : ℝ => hillRoughSignedAbelianComponent D.signed σ n
      (fourierLebesgueSourceInclusion s hs p hp h2p (D.fourierLebesguePhaseEvolution B s hs p hp h2p u q).val))
      (if n∈S then (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) a n : ℂ)*
        (if σ then I else -I)*hillRoughSignedAbelianComponent D.signed σ n
          (fourierLebesgueSourceInclusion s hs p hp h2p (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q).val)
        else 0) t := by
  have hd := D.hasDerivAt_fourierLebesguePhaseEvolution_component B s hs p hp h2p q σ n t
  by_cases hn : n∈S
  · rw [if_pos hn]
    have hfreq := D.fourierLebesguePhaseEvolution_frequency_eq_native B s hs p hp h2p t q a ha n
    cases σ <;> simp only [Bool.false_eq_true,ite_false,ite_true,
      signedPositiveFrequency_neg,signedPositiveFrequency_positive,ofReal_neg,hfreq] at hd ⊢
      <;> convert hd using 1 <;> ring
  · rw [if_neg hn]
    rw [D.fourierLebesguePhaseEvolution_component_zero_outside B s hs p hp h2p t q S hS σ n hn,mul_zero] at hd
    exact hd

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
