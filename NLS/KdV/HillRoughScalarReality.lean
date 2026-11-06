import NLS.KdV.NativeRealRoughDensity

/-! Continuous scalar recovery from native physical values determines
reality at EVERY real mean-zero rough input in the same open source ball. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

/-- Reality on all original real native H1 sources transfers to the entire
real mean-zero H-minus-one source ball. No stronger source regularity remains. -/
theorem hillRoughScalar_real_of_native_real (δ : ℝ) (F : PeriodOneHminusOne → ℂ)
    (hF : ContinuousOn F (ball (0 : PeriodOneHminusOne) δ))
    (hnative : ∀ u : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
      nativeHillSource 1 u.val∈ball (0 : PeriodOneHminusOne) δ → (F (nativeHillSource 1 u.val)).im=0)
    (q : PeriodOneHminusOne) (hqr : IsRealPeriodOneHminusOne q) (hqm : q.val 0=0)
    (hq : q∈ball (0 : PeriodOneHminusOne) δ) : (F q).im=0 := by
  obtain ⟨u,_,hu⟩ := exists_native_real_meanZero_rough_approximants 1 q hqr hqm
  have hlim := ((hF q hq).continuousAt (isOpen_ball.mem_nhds hq)).tendsto.comp hu
  have hlimim := Complex.continuous_im.continuousAt.tendsto.comp hlim
  have heq : (fun N => (F (nativeHillSource 1 (u N).val)).im) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
    filter_upwards [hu.eventually (isOpen_ball.mem_nhds hq)] with N hN
    exact hnative (u N) hN
  have hzero : Tendsto (fun N => (F (nativeHillSource 1 (u N).val)).im) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ))).congr' heq.symm
  exact tendsto_nhds_unique hlimim hzero

end NLS.KdV
