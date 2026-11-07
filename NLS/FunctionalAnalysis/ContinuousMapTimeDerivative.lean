import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.Compact

/-! # A continuous uniform velocity determines the uniform time derivative

The pointwise equation and norm continuity of its continuous-function-valued
velocity imply the Banach-valued integral equation, and hence differentiability
in the full uniform norm. No uniform time derivative is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace NLS.FunctionalAnalysis

theorem hasDerivAt_continuousMap_of_pointwise_real_banach
    {K E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (u v : ℝ → C(K,E)) (hv : Continuous v)
    (hpoint : ∀ t : ℝ, ∀ x : K, HasDerivAt (fun r => u r x) (v t x) t)
    (t : ℝ) : HasDerivAt u (v t) t := by
  have hrec (r : ℝ) : u r = u 0+∫ s in (0:ℝ)..r, v s := by
    apply ContinuousMap.ext
    intro x
    have hi := (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm (μ := volume) (hv.intervalIntegrable 0 r)
    have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := r)
      (fun s _ => hpoint s x)
      (((ContinuousMap.evalCLM ℝ x).continuous.comp hv).intervalIntegrable 0 r)
    change (∫ s in (0:ℝ)..r, v s x) = (∫ s in (0:ℝ)..r, v s) x at hi
    change u r x = u 0 x+(∫ s in (0:ℝ)..r, v s) x
    rw [← hi,hp,add_sub_cancel]
  have he : u = fun r => u 0+∫ s in (0:ℝ)..r, v s := funext hrec
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 t)
    hv.stronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt).const_add _

end NLS.FunctionalAnalysis
