import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem exists_zero_of_continuousOn_integral_eq_zero
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hi : (∫ x in a..b, f x) = 0) :
    ∃ x ∈ Ioo a b, f x = 0 := by
  have hint : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab.le
  have hcont : ContinuousOn (fun x => ∫ t in a..x, f t) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      intervalIntegral.continuousOn_primitive_interval' hint (left_mem_uIcc : a ∈ uIcc a b)
  apply exists_hasDerivAt_eq_zero hab hcont (by simpa only [intervalIntegral.integral_same] using hi.symm)
  intro x hx
  have hc : ContinuousAt f x := hf.continuousAt
    (mem_of_superset (isOpen_Ioo.mem_nhds hx) Ioo_subset_Icc_self)
  have hm : StronglyMeasurableAtFilter f (𝓝 x) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
      (fun y hy => hf.continuousAt
        (mem_of_superset (isOpen_Ioo.mem_nhds hy) Ioo_subset_Icc_self)) x hx
  exact intervalIntegral.integral_hasDerivAt_right
    (hint.mono_set (uIcc_subset_uIcc (left_mem_uIcc : a ∈ uIcc a b)
      (by simpa only [uIcc_of_le hab.le] using Ioo_subset_Icc_self hx))) hm hc

end NLS.ComplexAnalysis
