import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! A continuous pointwise velocity on a compact domain gives the derivative
of the curve in the uniform norm. The fundamental theorem supplies the
Banach-valued integral identity, so no norm differentiability of the curve
is assumed. -/
noncomputable section
open MeasureTheory intervalIntegral
namespace NLS.FunctionalAnalysis

theorem hasDerivAt_continuousMap_of_pointwise
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (f g : ℝ → C(K, ℂ)) (hg : Continuous g)
    (hd : ∀ t x, HasDerivAt (fun s => f s x) (g t x) t) (t : ℝ) :
    HasDerivAt f (g t) t := by
  have hint (r : ℝ) : f r = f 0 + ∫ s in (0 : ℝ)..r, g s := by
    ext x
    let L : C(K, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ x
    change L (f r) = L (f 0 + ∫ s in (0 : ℝ)..r, g s)
    rw [map_add, ← L.intervalIntegral_comp_comm (hg.intervalIntegrable 0 r)]
    have hi := integral_eq_sub_of_hasDerivAt (fun s _ => hd s x)
      ((L.continuous.comp hg).intervalIntegrable 0 r)
    change f r x = f 0 x + ∫ s in (0 : ℝ)..r, g s x
    rw [hi]
    abel
  have h := (integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add (f 0)
  simpa only [← hint] using h

end NLS.FunctionalAnalysis
