import NLS.KdV.NativeRealRoughDensity

/-! Continuous scalar agreement on the actual native H1 sources extends
to EVERY original real mean-zero H-minus-one source in the same rough ball. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

theorem hillRoughScalar_eq_of_native_agreement (δ : ℝ) (F G : PeriodOneHminusOne → ℂ)
    (hF : ContinuousOn F (ball (0 : PeriodOneHminusOne) δ))
    (hG : ContinuousOn G (ball (0 : PeriodOneHminusOne) δ))
    (hnative : ∀ u : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
      nativeHillSource 1 u.val∈ball (0 : PeriodOneHminusOne) δ → F (nativeHillSource 1 u.val)=G (nativeHillSource 1 u.val))
    (q : PeriodOneHminusOne) (hqr : IsRealPeriodOneHminusOne q) (hqm : q.val 0=0)
    (hq : q∈ball (0 : PeriodOneHminusOne) δ) : F q=G q := by
  obtain ⟨u,_,hu⟩ := exists_native_real_meanZero_rough_approximants 1 q hqr hqm
  have hlimF := ((hF q hq).continuousAt (isOpen_ball.mem_nhds hq)).tendsto.comp hu
  have hlimG := ((hG q hq).continuousAt (isOpen_ball.mem_nhds hq)).tendsto.comp hu
  have heq : (fun N => F (nativeHillSource 1 (u N).val)) =ᶠ[atTop]
      (fun N => G (nativeHillSource 1 (u N).val)) := by
    filter_upwards [hu.eventually (isOpen_ball.mem_nhds hq)] with N hN
    exact hnative (u N) hN
  exact tendsto_nhds_unique hlimF (hlimG.congr' heq.symm)

end NLS.KdV
