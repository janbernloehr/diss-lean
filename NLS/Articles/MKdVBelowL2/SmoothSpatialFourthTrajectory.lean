import NLS.Articles.MKdVBelowL2.SmoothPhysicalMKdV
import NLS.ZakharovShabat.SourceNativeSobolevSmoothness

/-! # Spatial smoothness of the actual fourth flow from smooth real data

Represent the original smooth datum at every integer Sobolev order. The
fixed weighted lifts forget to the same original source trajectory, so
Fourier uniqueness identifies all of their physical representatives.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

theorem contDiff_fourthClassicalPhysicalValue_of_smooth_initial (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (hr : ∀ x, (f x).im = 0)
    (h0 : (fun x => (fourthClassicalPhysicalValue a 0 x).1) = f) (time : ℝ) :
    ContDiff ℝ ∞ (fun x => (fourthClassicalPhysicalValue a time x).1) := by
  have hca (k : ℤ) : (originalWeightedRealSource _ a).val.fst k = periodOneCoefficient f k := by
    have h := periodOneCoefficient_fourthClassicalPhysicalValue a 0 k
    rw [fourthClassicalSourceFlow_zero] at h
    exact h.1.symm.trans (congrArg (fun g : ℝ → ℂ => periodOneCoefficient g k) h0)
  apply contDiff_of_all_nativeSobolev_representations _
    (((fourthClassicalPhysicalFlow a time).1).continuous.comp continuous_quotient_mk')
    (fourthClassicalPhysicalValue_periodic a time).1
  intro n
  obtain ⟨b,_,hb⟩ := exists_nativeSobolevSource_of_smooth_real (n+1) f hf hp hr
  have hsame : originalWeightedRealSource _ b = originalWeightedRealSource _ a := by
    apply Subtype.ext
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext k
    · change (originalWeightedRealSource _ b).val.fst k = (originalWeightedRealSource _ a).val.fst k
      exact (hb k).1.trans (hca k).symm
    · change (originalWeightedRealSource _ b).val.snd k = (originalWeightedRealSource _ a).val.snd k
      exact (hb k).2.trans ((hca k).symm.trans (congrArg (fun c : Coeff 2 => c k) ha))
  let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
  let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
  let c := F.sobolevImageFlow D le_rfl (n+1 : ℕ) (Nat.cast_nonneg (n+1)) b time
  have hinc : originalWeightedRealSource _ c = originalWeightedRealSource _ (fourthClassicalSourceFlow a time) := by
    rw [F.originalWeightedRealSource_sobolevImageFlow D le_rfl (n+1 : ℕ) (Nat.cast_nonneg (n+1)) b time,hsame]
    exact (originalWeightedRealSource_fourthClassicalSourceFlow a time).symm
  refine ⟨c,fun k => ?_⟩
  exact (congrArg (fun z : realTypeSourceSubmodule 2 => z.val.fst k) hinc).trans
    (periodOneCoefficient_fourthClassicalPhysicalValue a time k).1.symm

/-- Every smooth real periodic initial field has the actual globally
defined spatially smooth real pointwise mKdV trajectory, with its physical
mass. This is an existence and regularity statement for the fixed flow. -/
theorem exists_spatially_smooth_mKdV_of_smooth_initial (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (hr : ∀ x, (f x).im = 0) :
    ∃ a : FourthClassicalSource,
      (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd ∧
      (fun x => (fourthClassicalPhysicalValue a 0 x).1) = f ∧
      ∀ time : ℝ, ContDiff ℝ ∞ (fun x => (fourthClassicalPhysicalValue a time x).1) ∧
        Function.Periodic (fun x => (fourthClassicalPhysicalValue a time x).1) 1 ∧
        ∀ x : ℝ, ((fourthClassicalPhysicalValue a time x).1).im = 0 ∧
          HasDerivAt (fun r => (fourthClassicalPhysicalValue a r x).1)
            (-deriv (deriv (deriv (fun y => (fourthClassicalPhysicalValue a time y).1))) x+
              6*(((fourthClassicalPhysicalValue a time x).1)^2-(∫ y in (0:ℝ)..1, (f y)^2))*
                deriv (fun y => (fourthClassicalPhysicalValue a time y).1) x) time := by
  obtain ⟨a,ha,h0,hflow⟩ := exists_pointwise_mKdV_of_smooth_initial f hf hp hr
  exact ⟨a,ha,h0,fun time =>
    ⟨contDiff_fourthClassicalPhysicalValue_of_smooth_initial a ha f hf hp hr h0 time,hflow time⟩⟩

end NLS.Articles.MKdVBelowL2
