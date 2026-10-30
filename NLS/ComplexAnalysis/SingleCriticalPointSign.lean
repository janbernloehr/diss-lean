import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Derivative signs around a unique interior critical point

The mean value theorem and continuity of the derivative determine its
signs on both sides of a unique critical point above equal endpoint values.
-/

open Set
namespace NLS.ComplexAnalysis

/-- Equal endpoint values, a strictly higher interior and a unique critical
point force the derivative to be positive on the left and negative on the right. -/
theorem derivative_signs_of_unique_critical
    (f f' : ℝ → ℝ) (a b c : ℝ) (hc : c ∈ Ioo a b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hdc : ContinuousOn f' (Icc a b))
    (hend : f a = f b) (hgt : ∀ x ∈ Ioo a b, f a < f x)
    (hunique : ∀ x ∈ Ioo a b, f' x = 0 → x = c) :
    (∀ x ∈ Ioo a c, 0 < f' x) ∧ (∀ x ∈ Ioo c b, f' x < 0) := by
  constructor
  · intro x hx
    have hxab : x ∈ Ioo a b := ⟨hx.1,hx.2.trans hc.2⟩
    obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope f f' hx.1
      (hf.mono (Icc_subset_Icc_right hxab.2.le))
      (fun y hy => hd y ⟨hy.1,hy.2.trans hxab.2⟩)
    have htpos : 0 < f' t := by
      rw [he]
      exact div_pos (sub_pos.mpr (hgt x hxab)) (sub_pos.mpr hx.1)
    by_contra h
    have hxle : f' x ≤ 0 := le_of_not_gt h
    obtain ⟨y,hy,hyzero⟩ := intermediate_value_Icc' ht.2.le
      (hdc.mono (Icc_subset_Icc ht.1.le hxab.2.le)) ⟨hxle,htpos.le⟩
    have hyc := hunique y ⟨ht.1.trans_le hy.1,hy.2.trans_lt hxab.2⟩ hyzero
    linarith [hy.2,hx.2]
  · intro x hx
    have hxab : x ∈ Ioo a b := ⟨hc.1.trans hx.1,hx.2⟩
    obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope f f' hx.2
      (hf.mono (Icc_subset_Icc_left hxab.1.le))
      (fun y hy => hd y ⟨hxab.1.trans hy.1,hy.2⟩)
    have htneg : f' t < 0 := by
      rw [he,← hend]
      exact div_neg_of_neg_of_pos (sub_neg.mpr (hgt x hxab)) (sub_pos.mpr hx.2)
    by_contra h
    have hxge : 0 ≤ f' x := le_of_not_gt h
    obtain ⟨y,hy,hyzero⟩ := intermediate_value_Icc' ht.1.le
      (hdc.mono (Icc_subset_Icc hxab.1.le ht.2.le)) ⟨htneg.le,hxge⟩
    have hyc := hunique y ⟨hxab.1.trans_le hy.1,hy.2.trans_lt ht.2⟩ hyzero
    linarith [hy.1,hx.1]

end NLS.ComplexAnalysis
