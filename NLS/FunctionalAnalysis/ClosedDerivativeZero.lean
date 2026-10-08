import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Constancy on closed intervals from interior derivatives -/
noncomputable section
open Set MeasureTheory intervalIntegral
namespace NLS.FunctionalAnalysis

/-- Continuity at the endpoints and zero interior derivative imply constancy
on the whole closed interval, including singleton intervals. -/
theorem eq_of_hasDerivAt_zero_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} {f : ℝ → E}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ time ∈ Ioo a b, HasDerivAt f 0 time)
    {time initial : ℝ} (ht : time ∈ Icc a b) (hi : initial ∈ Icc a b) :
    f time = f initial := by
  have he (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) : f y = f x := by
    have h := integral_eq_sub_of_hasDerivAt_of_le hxy
      (hc.mono (Icc_subset_Icc hx.1 hy.2))
      (fun r hr => hd r ⟨hx.1.trans_lt hr.1,hr.2.trans_le hy.2⟩)
      (intervalIntegrable_const (a := x) (b := y) (c := (0 : E)))
    have hz : f y-f x = 0 := by simpa only [intervalIntegral.integral_zero] using h.symm
    exact sub_eq_zero.mp hz
  rcases le_total initial time with h | h
  · exact he initial time hi ht h
  · exact (he time initial ht hi h).symm

end NLS.FunctionalAnalysis
