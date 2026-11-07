import NLS.Articles.KdVPseudomeasures.OriginalHillRoughCanonicalFlow
import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerRegularity

/-! The SAME canonical KdV flow preserves EVERY genuine nonnegative
integer Sobolev space. Its restriction uses the actual strong native
equivalence and agrees as an ENTIRE original rough distribution. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.WeightedCoeff NLS.LpSequence
namespace NLS.Articles.KdVPseudomeasures

theorem hillIntegerTargetInclusion_phaseFlow (s : ℕ) (freq : ℤ → ℝ)
    (hf : ∀ k, freq (-k)=-freq k) (time : ℝ)
    (z : RealSignedHilbert (signedStepOrder (1/2) s)) :
    hillIntegerTargetInclusion s (fourierRealZeroPhaseFlow (Weight.signedSobolev (signedStepOrder (1/2) s)) freq hf time z)=
      fourierRealZeroPhaseFlow (Weight.signedSobolev (-1/2)) freq hf time (hillIntegerTargetInclusion s z) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillIntegerTargetInclusion_apply,fourierRealZeroPhaseFlow_apply,
    fourierRealZeroPhaseFlow_apply,hillIntegerTargetInclusion_apply]

def hillIntegerCanonicalKdVFlow (s : ℕ) (q : RealSignedHilbert (signedStepOrder 0 s)) (time : ℝ) :
    RealSignedHilbert (signedStepOrder 0 s) :=
  (hillIntegerSobolevEquiv s).equiv.symm
    (fourierRealZeroPhaseFlow (Weight.signedSobolev (signedStepOrder (1/2) s))
      (oddPositiveFrequency (fun n => hillRoughKdVFrequency n (hillIntegerSourceInclusion s q)))
      (oddPositiveFrequency_neg _) time ((hillIntegerSobolevEquiv s).equiv q))

theorem hillIntegerCanonicalKdVFlow_native (s : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 s)) (time : ℝ) :
    (hillIntegerSobolevEquiv s).equiv (hillIntegerCanonicalKdVFlow s q time)=
      fourierRealZeroPhaseFlow (Weight.signedSobolev (signedStepOrder (1/2) s))
        (oddPositiveFrequency (fun n => hillRoughKdVFrequency n (hillIntegerSourceInclusion s q)))
        (oddPositiveFrequency_neg _) time ((hillIntegerSobolevEquiv s).equiv q) :=
  (hillIntegerSobolevEquiv s).equiv.apply_symm_apply _

theorem hillIntegerCanonicalKdVFlow_inclusion (s : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 s)) (time : ℝ) :
    hillIntegerSourceInclusion s (hillIntegerCanonicalKdVFlow s q time)=
      hillRoughCanonicalKdVFlow (hillIntegerSourceInclusion s q) time := by
  apply injective_hillRealSignedMap
  rw [← hillIntegerSobolevEquiv_inclusion,hillIntegerCanonicalKdVFlow_native,
    hillIntegerTargetInclusion_phaseFlow,hillIntegerSobolevEquiv_inclusion,
    hillRoughCanonicalKdVFlow_native]

theorem hillIntegerCanonicalKdVFlow_zero (s : ℕ) (q : RealSignedHilbert (signedStepOrder 0 s)) :
    hillIntegerCanonicalKdVFlow s q 0=q := by
  apply hillIntegerSourceInclusion_injective s
  rw [hillIntegerCanonicalKdVFlow_inclusion,hillRoughCanonicalKdVFlow_zero]

theorem hillIntegerCanonicalKdVFlow_add (s : ℕ) (q : RealSignedHilbert (signedStepOrder 0 s)) (time r : ℝ) :
    hillIntegerCanonicalKdVFlow s (hillIntegerCanonicalKdVFlow s q r) time=
      hillIntegerCanonicalKdVFlow s q (time+r) := by
  apply hillIntegerSourceInclusion_injective s
  rw [hillIntegerCanonicalKdVFlow_inclusion,hillIntegerCanonicalKdVFlow_inclusion,
    hillIntegerCanonicalKdVFlow_inclusion,hillRoughCanonicalKdVFlow_add]

theorem hillIntegerCanonicalKdVFlow_frequency (s : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 s)) (time : ℝ) (n : ℕ+) :
    hillRoughKdVFrequency n (hillIntegerSourceInclusion s (hillIntegerCanonicalKdVFlow s q time))=
      hillRoughKdVFrequency n (hillIntegerSourceInclusion s q) := by
  rw [hillIntegerCanonicalKdVFlow_inclusion,hillRoughCanonicalKdVFlow_frequency]

theorem continuous_hillIntegerCanonicalKdVFlow (s : ℕ) :
    Continuous (fun x : ℝ × RealSignedHilbert (signedStepOrder 0 s) => hillIntegerCanonicalKdVFlow s x.2 x.1) := by
  have hf (k : ℤ) : Continuous (fun x : ℝ × RealSignedHilbert (signedStepOrder 0 s) =>
      oddPositiveFrequency (fun n => hillRoughKdVFrequency n (hillIntegerSourceInclusion s x.2)) k) :=
    continuous_oddPositiveFrequency_family
      (fun x : ℝ × RealSignedHilbert (signedStepOrder 0 s) =>
        fun n => hillRoughKdVFrequency n (hillIntegerSourceInclusion s x.2))
      (fun n => (continuous_hillRoughKdVFrequency n).comp
        ((hillIntegerSourceInclusion s).continuous.comp continuous_snd)) k
  have hmap : Continuous (hillIntegerSobolevEquiv s).equiv :=
    continuous_iff_continuousAt.mpr (fun q => ((hillIntegerSobolevEquiv s).analytic q).continuousAt)
  have hinv : Continuous (hillIntegerSobolevEquiv s).equiv.symm :=
    continuous_iff_continuousAt.mpr (fun z => ((hillIntegerSobolevEquiv s).analytic_symm z).continuousAt)
  exact hinv.comp
    (continuous_fourierRealZeroPhaseFlow_family (Weight.signedSobolev (signedStepOrder (1/2) s)) (by simp)
      (fun x : ℝ × RealSignedHilbert (signedStepOrder 0 s) =>
        oddPositiveFrequency (fun n => hillRoughKdVFrequency n (hillIntegerSourceInclusion s x.2)))
      (fun _ => oddPositiveFrequency_neg _) (fun x => x.1) (fun x => (hillIntegerSobolevEquiv s).equiv x.2)
      hf continuous_fst (hmap.comp continuous_snd))

end NLS.Articles.KdVPseudomeasures
