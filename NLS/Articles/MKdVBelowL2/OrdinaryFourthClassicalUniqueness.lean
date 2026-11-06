import NLS.Articles.MKdVBelowL2.SmoothSpatialOrdinaryFourthTrajectory
import NLS.MKdV.ClassicalUniqueness
import NLS.FunctionalAnalysis.ContinuousMapTimeDerivative

/-! # Existence and uniqueness of ordinary smooth periodic mKdV solutions

The mass-restored native flow has its actual derivative in the full uniform
norm, preserves smooth spatial slices, and solves the original physical PDE.
Classical uniqueness with zero translation parameter identifies every smooth
ordinary solution with this constructed flow.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier NLS.MKdV
open scoped ContDiff
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

/-- The first physical field is differentiable in the full uniform norm. -/
theorem hasDerivAt_ordinaryFourthClassicalPhysicalFlow_fst (a : FourthClassicalSource) (time : ℝ) :
    HasDerivAt (fun r => (ordinaryFourthClassicalPhysicalFlow a r).1)
      (fourthClassicalVelocity 0 (ordinaryFourthClassicalSourceFlow a time)).1 time := by
  have hc : Continuous (fun r => ordinaryFourthClassicalSourceFlow a r) :=
    continuous_ordinaryFourthClassicalSourceFlow.comp (f := fun r : ℝ => (a,r)) (continuous_const.prodMk continuous_id)
  have hv : Continuous (fun r => (fourthClassicalVelocity 0 (ordinaryFourthClassicalSourceFlow a r)).1) :=
    (continuous_fourthClassicalVelocity.comp (continuous_const.prodMk hc)).fst
  have hp : ∀ r : ℝ, ∀ x : AddCircle (2:ℝ),
      HasDerivAt (fun s => (ordinaryFourthClassicalPhysicalFlow a s).1 x)
        ((fourthClassicalVelocity 0 (ordinaryFourthClassicalSourceFlow a r)).1 x) r := by
    intro r x
    induction x using QuotientAddGroup.induction_on with
    | H x => exact (hasDerivAt_ordinaryFourthClassicalPhysicalValue a r x).fst
  exact NLS.FunctionalAnalysis.hasDerivAt_continuousMap_of_pointwise
    (fun r => (ordinaryFourthClassicalPhysicalFlow a r).1)
    (fun r => (fourthClassicalVelocity 0 (ordinaryFourthClassicalSourceFlow a r)).1) hv hp time

/-- The native smooth-data trajectory satisfies all classical uniqueness
hypotheses; none is added as an assumption about the Birkhoff flow. -/
theorem isClassicalMKdVTrajectory_ordinaryFourthClassicalPhysicalFlow (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (hr : ∀ x, (f x).im = 0)
    (h0 : (fun x => (ordinaryFourthClassicalPhysicalValue a 0 x).1) = f) :
    IsClassicalMKdVTrajectory (0:ℂ) (fun r => (ordinaryFourthClassicalPhysicalFlow a r).1) := by
  refine ⟨fun r => (hasDerivAt_ordinaryFourthClassicalPhysicalFlow_fst a r).differentiableAt,
    fun r => contDiff_ordinaryFourthClassicalPhysicalValue_of_smooth_initial a ha f hf hp hr h0 r,
    fun r => (ordinaryFourthClassicalPhysicalValue_periodic a r).1,
    fun r x => ordinaryFourthClassicalPhysicalValue_im_eq_zero a ha r x,?_,?_⟩
  · refine ⟨fun r => (nativeSobolevPhysicalJetCLM 4 1 (by omega) (ordinaryFourthClassicalSourceFlow a r)).1,?_,?_⟩
    · exact ((nativeSobolevPhysicalJetCLM 4 1 (by omega)).continuous.comp
        (continuous_ordinaryFourthClassicalSourceFlow.comp (f := fun r : ℝ => (a,r)) (continuous_const.prodMk continuous_id))).fst
    · intro r x
      exact (hasDerivAt_nativeSobolevPhysicalJet_fst 4 0 (by omega) (ordinaryFourthClassicalSourceFlow a r) x).deriv.symm
  · intro r x
    have he := (ContinuousMap.evalCLM ℝ (x : AddCircle (2:ℝ))).hasFDerivAt.comp_hasDerivAt r
      (hasDerivAt_ordinaryFourthClassicalPhysicalFlow_fst a r)
    have hpde := hasDerivAt_ordinaryFourthClassicalPhysicalValue_mKdV a ha r x
    rw [(hasDerivAt_ordinaryFourthClassicalPhysicalFlow_fst a r).deriv]
    exact he.unique hpde

/-- Every ordinary classical solution with this initial field equals the
actual mass-restored native fourth flow. -/
theorem classicalOrdinaryMKdVTrajectory_eq_ordinaryFourthClassicalPhysicalFlow
    (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (hr : ∀ x, (f x).im = 0)
    (h0 : (fun x => (ordinaryFourthClassicalPhysicalValue a 0 x).1) = f)
    (u : ℝ → C(AddCircle (2:ℝ),ℂ)) (hu : IsClassicalMKdVTrajectory (0:ℂ) u)
    (hu0 : ∀ x : ℝ, u 0 (x : AddCircle (2:ℝ)) = f x) :
    u = fun r => (ordinaryFourthClassicalPhysicalFlow a r).1 := by
  apply hu.eq_of_eq_at (isClassicalMKdVTrajectory_ordinaryFourthClassicalPhysicalFlow a ha f hf hp hr h0) 0
  apply ContinuousMap.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H x => exact (hu0 x).trans (congrFun h0 x).symm

/-- Every smooth real period-one datum has exactly one global ordinary
classical mKdV solution, with no renormalizing translation term. -/
theorem existsUnique_classicalOrdinaryMKdVTrajectory (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (hr : ∀ x, (f x).im = 0) :
    ∃! u : ℝ → C(AddCircle (2:ℝ),ℂ), IsClassicalMKdVTrajectory (0:ℂ) u ∧
      ∀ x : ℝ, u 0 (x : AddCircle (2:ℝ)) = f x := by
  obtain ⟨a,ha,h0⟩ := exists_fourthClassicalSource_of_smooth_real f hf hp hr
  have h0' : (fun x => (ordinaryFourthClassicalPhysicalValue a 0 x).1) = f := by
    simpa only [ordinaryFourthClassicalPhysicalValue,ordinaryFourthClassicalPhysicalFlow,
      ordinaryFourthClassicalSourceFlow_zero,fourthClassicalPhysicalValue,fourthClassicalPhysicalFlow,
      fourthClassicalSourceFlow_zero] using h0
  refine ⟨fun r => (ordinaryFourthClassicalPhysicalFlow a r).1,⟨?_,fun x => congrFun h0' x⟩,?_⟩
  · exact isClassicalMKdVTrajectory_ordinaryFourthClassicalPhysicalFlow a ha f hf hp hr h0'
  · intro u hu
    exact classicalOrdinaryMKdVTrajectory_eq_ordinaryFourthClassicalPhysicalFlow a ha f hf hp hr h0' u hu.1 hu.2

end NLS.Articles.MKdVBelowL2
