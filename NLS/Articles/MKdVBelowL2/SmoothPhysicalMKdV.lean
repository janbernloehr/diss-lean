import NLS.Articles.MKdVBelowL2.FourthClassicalMKdV
import NLS.ZakharovShabat.SourceNativeSmoothRealization

/-! # Smooth real physical initial data for the actual scalar fourth trajectory

Every smooth real period-one field is represented in the original native
H⁴ source. Its actual fixed-family trajectory has precisely that initial
field, the unit-period mass, physical reality, and the pointwise mKdV PDE.
Uniqueness among arbitrary classical PDE trajectories remains separate.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

theorem fourthClassicalPhysicalValue_periodic (a : FourthClassicalSource) (time : ℝ) :
    Function.Periodic (fun x => (fourthClassicalPhysicalValue a time x).1) 1 ∧
    Function.Periodic (fun x => (fourthClassicalPhysicalValue a time x).2) 1 :=
  ⟨hierarchySobolevJetContinuous_periodic 4 0 (by omega) _,
    hierarchySobolevJetContinuous_periodic 4 0 (by omega) _⟩

/-- Smooth scalar real data have an actual native source with exactly the
original initial physical field, rather than just matching actions. -/
theorem exists_fourthClassicalSource_of_smooth_real (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (hr : ∀ x, (f x).im = 0) :
    ∃ a : FourthClassicalSource,
      (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd ∧
      (fun x => (fourthClassicalPhysicalValue a 0 x).1) = f := by
  obtain ⟨a,ha,hcoeff⟩ := exists_nativeSobolevSource_of_smooth_real 4 f hf hp hr
  have hj := nativeSobolevPhysicalJet_eq_smooth 4 0 (by omega) a f f hf hf hp hp hcoeff
  refine ⟨a,ha,?_⟩
  funext x
  change (nativeSobolevPhysicalJetCLM 4 0 (by omega) (fourthClassicalSourceFlow a 0)).1 (x : AddCircle (2:ℝ)) = f x
  rw [fourthClassicalSourceFlow_zero]
  exact congrFun hj.1 x

/-- Every smooth real period-one datum has the actual global pointwise
renormalized mKdV trajectory with the exact initial physical square mass. -/
theorem exists_pointwise_mKdV_of_smooth_initial (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (hr : ∀ x, (f x).im = 0) :
    ∃ a : FourthClassicalSource,
      (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd ∧
      (fun x => (fourthClassicalPhysicalValue a 0 x).1) = f ∧
      ∀ time : ℝ, Function.Periodic (fun x => (fourthClassicalPhysicalValue a time x).1) 1 ∧
        ∀ x : ℝ, ((fourthClassicalPhysicalValue a time x).1).im = 0 ∧
          HasDerivAt (fun r => (fourthClassicalPhysicalValue a r x).1)
            (-deriv (deriv (deriv (fun y => (fourthClassicalPhysicalValue a time y).1))) x+
              6*(((fourthClassicalPhysicalValue a time x).1)^2-(∫ y in (0:ℝ)..1, (f y)^2))*
                deriv (fun y => (fourthClassicalPhysicalValue a time y).1) x) time := by
  obtain ⟨a,ha,h0⟩ := exists_fourthClassicalSource_of_smooth_real f hf hp hr
  have hm : fourthClassicalMass a = ∫ y in (0:ℝ)..1, (f y)^2 := by
    rw [fourthClassicalMass_eq_integral_square a ha]
    apply intervalIntegral.integral_congr
    intro y _
    exact congrArg (fun z : ℂ => z^2) (congrFun h0 y)
  refine ⟨a,ha,h0,fun time => ⟨(fourthClassicalPhysicalValue_periodic a time).1,fun x => ?_⟩⟩
  have hd := hasDerivAt_fourthClassicalPhysicalValue_mKdV a ha time x
  dsimp only at hd
  rw [hm] at hd
  exact ⟨fourthClassicalPhysicalValue_im_eq_zero a ha time x,hd⟩

end NLS.Articles.MKdVBelowL2
