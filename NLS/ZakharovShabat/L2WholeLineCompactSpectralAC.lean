import NLS.ZakharovShabat.L2WholeLineCompactLocalSpectralAC
import NLS.ZakharovShabat.L2FloquetRepeatedRoots
import NLS.FunctionalAnalysis.RealLocalAbsoluteContinuity

/-! # Absolute continuity of actual physical spectral measures for compact inputs -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The actual real spectral measure of every compactly supported physical
input is absolutely continuous on the entire real line. -/
theorem wholeLineRealSpectralMeasure_absolutelyContinuous_of_compact_input
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u))
    (g : WholeLineL2) (a c : ℝ) (hac : a ≤ c)
    (hleft : ∀ᵐ t : ℝ, t ≤ a → wholeLineL2Pair g t = 0)
    (hright : ∀ᵐ t : ℝ, c ≤ t → wholeLineL2Pair g t = 0) :
    wholeLineRealSpectralMeasure u hu g ≪ (volume : Measure ℝ) := by
  apply absolutelyContinuous_of_local_Icc_off_null _ _
    {x : ℝ | (l2Monodromy u (x : ℂ)).trace ^ 2 - 4 = 0}
  · exact wholeLineRealSpectralMeasure_countable_zero u hu g _
      (countable_l2Monodromy_real_repeated_roots u hu)
  · intro x hx
    exact wholeLineRealSpectralMeasure_exists_local_AC_of_compact_input
      u hu g a c hac hleft hright x hx

/-- In particular every vector in the original dense smooth compact test
domain has an absolutely continuous physical scalar spectral measure. -/
theorem wholeLineRealSpectralMeasure_test_absolutelyContinuous
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u))
    (f : WholeLineTestFunction) :
    wholeLineRealSpectralMeasure u hu (wholeLineTestInclusion f) ≪ (volume : Measure ℝ) := by
  obtain ⟨R,hR,hs⟩ := f.property.2.isBounded.subset_ball_lt 0 (0 : ℝ)
  have hzero : ∀ t : ℝ, R ≤ |t| → f t = 0 := by
    intro t ht
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hb := hs hm
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hb
    linarith
  apply wholeLineRealSpectralMeasure_absolutelyContinuous_of_compact_input
    u hu (wholeLineTestInclusion f) (-R) R (by linarith)
  · filter_upwards [wholeLineTestInclusion_ae f] with t ht hleft
    change ((wholeLineTestInclusion f) t).ofLp = 0
    rw [ht,hzero t ((by linarith : R ≤ -t).trans (neg_le_abs t))]
    rfl
  · filter_upwards [wholeLineTestInclusion_ae f] with t ht hright
    change ((wholeLineTestInclusion f) t).ofLp = 0
    rw [ht,hzero t (hright.trans (le_abs_self t))]
    rfl

end NLS.ZakharovShabat
