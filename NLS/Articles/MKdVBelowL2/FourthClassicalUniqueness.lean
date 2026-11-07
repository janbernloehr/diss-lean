import NLS.Articles.MKdVBelowL2.SmoothSpatialFourthTrajectory
import NLS.MKdV.ClassicalUniqueness
import NLS.FunctionalAnalysis.ContinuousMapTimeDerivative

/-! # The actual fourth flow is the unique classical real mKdV trajectory

The uniform time derivative is proved from the continuous physical velocity
and the pointwise equation. The first spatial derivative is the actual
native Sobolev jet, continuous along the fixed Birkhoff source flow.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier NLS.MKdV
open scoped ContDiff
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

/-- The first physical field is differentiable in the full uniform norm. -/
theorem hasDerivAt_fourthClassicalPhysicalFlow_fst (a : FourthClassicalSource) (time : ℝ) :
    HasDerivAt (fun r => (fourthClassicalPhysicalFlow a r).1)
      (fourthClassicalVelocity a (fourthClassicalSourceFlow a time)).1 time := by
  have hc : Continuous (fun r => fourthClassicalSourceFlow a r) :=
    continuous_fourthClassicalSourceFlow.comp (f := fun r : ℝ => (a,r)) (continuous_const.prodMk continuous_id)
  have hv : Continuous (fun r => (fourthClassicalVelocity a (fourthClassicalSourceFlow a r)).1) :=
    (continuous_fourthClassicalVelocity.comp (continuous_const.prodMk hc)).fst
  have hp : ∀ r : ℝ, ∀ x : AddCircle (2:ℝ),
      HasDerivAt (fun s => (fourthClassicalPhysicalFlow a s).1 x)
        ((fourthClassicalVelocity a (fourthClassicalSourceFlow a r)).1 x) r := by
    intro r x
    induction x using QuotientAddGroup.induction_on with
    | H x => exact (hasDerivAt_fourthClassicalPhysicalValue a r x).fst
  exact NLS.FunctionalAnalysis.hasDerivAt_continuousMap_of_pointwise_real_banach
    (fun r => (fourthClassicalPhysicalFlow a r).1)
    (fun r => (fourthClassicalVelocity a (fourthClassicalSourceFlow a r)).1) hv hp time

/-- The native smooth-data trajectory satisfies all classical uniqueness
hypotheses; none is added as an assumption about the Birkhoff flow. -/
theorem isClassicalMKdVTrajectory_fourthClassicalPhysicalFlow (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (hr : ∀ x, (f x).im = 0)
    (h0 : (fun x => (fourthClassicalPhysicalValue a 0 x).1) = f) :
    IsClassicalMKdVTrajectory (fourthClassicalMass a) (fun r => (fourthClassicalPhysicalFlow a r).1) := by
  refine ⟨fun r => (hasDerivAt_fourthClassicalPhysicalFlow_fst a r).differentiableAt,
    fun r => contDiff_fourthClassicalPhysicalValue_of_smooth_initial a ha f hf hp hr h0 r,
    fun r => (fourthClassicalPhysicalValue_periodic a r).1,
    fun r x => fourthClassicalPhysicalValue_im_eq_zero a ha r x,?_,?_⟩
  · refine ⟨fun r => (nativeSobolevPhysicalJetCLM 4 1 (by omega) (fourthClassicalSourceFlow a r)).1,?_,?_⟩
    · exact ((nativeSobolevPhysicalJetCLM 4 1 (by omega)).continuous.comp
        (continuous_fourthClassicalSourceFlow.comp (f := fun r : ℝ => (a,r)) (continuous_const.prodMk continuous_id))).fst
    · intro r x
      exact (hasDerivAt_nativeSobolevPhysicalJet_fst 4 0 (by omega) (fourthClassicalSourceFlow a r) x).deriv.symm
  · intro r x
    have he := (ContinuousMap.evalCLM ℝ (x : AddCircle (2:ℝ))).hasFDerivAt.comp_hasDerivAt r
      (hasDerivAt_fourthClassicalPhysicalFlow_fst a r)
    have hpde := hasDerivAt_fourthClassicalPhysicalValue_mKdV a ha r x
    rw [(hasDerivAt_fourthClassicalPhysicalFlow_fst a r).deriv]
    exact he.unique hpde

/-- Any classical trajectory with the same initial physical field and mass
is exactly the constructed fixed-family fourth trajectory. -/
theorem classicalMKdVTrajectory_eq_fourthClassicalPhysicalFlow
    (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (hr : ∀ x, (f x).im = 0)
    (h0 : (fun x => (fourthClassicalPhysicalValue a 0 x).1) = f)
    (u : ℝ → C(AddCircle (2:ℝ),ℂ))
    (hu : IsClassicalMKdVTrajectory (∫ y in (0:ℝ)..1, (f y)^2) u)
    (hu0 : ∀ x : ℝ, u 0 (x : AddCircle (2:ℝ)) = f x) :
    u = fun r => (fourthClassicalPhysicalFlow a r).1 := by
  have hm : fourthClassicalMass a = ∫ y in (0:ℝ)..1, (f y)^2 := by
    rw [fourthClassicalMass_eq_integral_square a ha]
    apply intervalIntegral.integral_congr
    intro y _
    exact congrArg (fun z : ℂ => z^2) (congrFun h0 y)
  have hv := isClassicalMKdVTrajectory_fourthClassicalPhysicalFlow a ha f hf hp hr h0
  rw [hm] at hv
  apply hu.eq_of_eq_at hv 0
  apply ContinuousMap.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H x => exact (hu0 x).trans (congrFun h0 x).symm

/-- Every smooth real period-one datum has exactly one classical global
renormalized mKdV trajectory, with the original unit-period square mass. -/
theorem existsUnique_classicalMKdVTrajectory (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (hr : ∀ x, (f x).im = 0) :
    ∃! u : ℝ → C(AddCircle (2:ℝ),ℂ),
      IsClassicalMKdVTrajectory (∫ y in (0:ℝ)..1, (f y)^2) u ∧
      ∀ x : ℝ, u 0 (x : AddCircle (2:ℝ)) = f x := by
  obtain ⟨a,ha,h0⟩ := exists_fourthClassicalSource_of_smooth_real f hf hp hr
  have hm : fourthClassicalMass a = ∫ y in (0:ℝ)..1, (f y)^2 := by
    rw [fourthClassicalMass_eq_integral_square a ha]
    apply intervalIntegral.integral_congr
    intro y _
    exact congrArg (fun z : ℂ => z^2) (congrFun h0 y)
  refine ⟨fun r => (fourthClassicalPhysicalFlow a r).1,⟨?_,fun x => congrFun h0 x⟩,?_⟩
  · rw [← hm]
    exact isClassicalMKdVTrajectory_fourthClassicalPhysicalFlow a ha f hf hp hr h0
  · intro u hu
    exact classicalMKdVTrajectory_eq_fourthClassicalPhysicalFlow a ha f hf hp hr h0 u hu.1 hu.2

end NLS.Articles.MKdVBelowL2
