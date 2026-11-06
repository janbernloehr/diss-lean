import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapApproximation
import NLS.Articles.KdVKdV2Frequencies.NativeAllGapFrequencyMoments
import NLS.KdV.HillOriginalSecondMomentSeries

/-! The ACTUAL intrinsic KdV frequency is the original absolutely convergent
second-moment series at every native H1 source in one common rough ball.
Density and continuity compare independently defined functions. The result
includes infinite support and all closed selected gaps. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

private theorem original_source_native_physical (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    hillOriginalHminusSource (nativeHillPhysicalSource m q.val q.property.1).val = nativeHillSource m q.val := by
  rw [hillOriginalHminusSource_eq_physical]
  exact (nativeHillSource_eq_physical m q.val q.property.1).symm

/-- An analytic full complex H-minus-one extension of the TRUE intrinsic
KdV frequency correction exists on one rough ball before all indices. At
EVERY native real mean-zero H1 source in that ball, the fixed-source original
moment sum is absolutely convergent and equals the physical action derivative.
There is no finite-gap, open-mode, assumed-frequency or assumed-summability premise. -/
theorem exists_native_kdv_original_moment_frequency_near_zero (D : GlobalRoughAbelianForwardData) :
    ∃ δ : ℝ, ∃ F : ℕ+ → PeriodOneHminusOne → ℂ, 0<δ ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (F n) (ball (0 : PeriodOneHminusOne) δ)) ∧
      ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
        nativeHillSource 1 q.val ∈ ball (0 : PeriodOneHminusOne) δ → ∀ n : ℕ+,
        let p := nativeHillPhysicalSource 1 q.val q.property.1
        Summable (fun k : ℕ => ‖(k : ℂ)*hillIntrinsicFrequencyMoment p.val p.property.1 p.property.2 n n.pos k 2‖) ∧
        F n (nativeHillSource 1 q.val) =
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3 ∧
        (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3 =
          -12*∑' k : ℕ, (k : ℂ)*hillIntrinsicFrequencyMoment p.val p.property.1 p.property.2 n n.pos k 2 := by
  obtain ⟨δ,F,hδ,hF,hseries⟩ := exists_hillOriginal_analytic_second_moment_series
  refine ⟨δ,F,hδ,hF,?_⟩
  intro q hq n
  let p := nativeHillPhysicalSource 1 q.val q.property.1
  have hp := original_source_native_physical 1 q
  have hqseries := hseries p (by rw [hp];exact hq) n
  have hsource : Tendsto (fun N => nativeHillSource 1 (D.nativeFiniteGapApproximation 1 q N).val)
      atTop (𝓝 (nativeHillSource 1 q.val)) :=
    (nativeHillSource 1).continuous.continuousAt.tendsto.comp
      (continuous_subtype_val.continuousAt.tendsto.comp (D.tendsto_nativeFiniteGapApproximation 1 q))
  have hlimF := ((hF n _ hq).continuousAt.tendsto).comp hsource
  have heq : (fun N => F n (nativeHillSource 1 (D.nativeFiniteGapApproximation 1 q N).val)) =ᶠ[atTop]
      (fun N => (D.nativeSourceHierarchyFrequency 1 3 (by norm_num)
        (D.nativeFiniteGapApproximation 1 q N) n : ℂ)-(2*(n : ℂ)*Real.pi)^3) := by
    filter_upwards [hsource.eventually (isOpen_ball.mem_nhds hq)] with N hN
    let u := D.nativeFiniteGapApproximation 1 q N
    let pN := nativeHillPhysicalSource 1 u.val u.property.1
    have hpN := original_source_native_physical 1 u
    have hSN := (hseries pN (by rw [hpN];exact hN) n).2
    rw [hpN] at hSN
    obtain ⟨S,hS⟩ := D.nativeFiniteGapApproximation_finite_gap 1 q N
    exact hSN.trans (D.native_finiteGap_kdv_frequency_moments_all_gaps u S hS n).symm
  have hlimω := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (D.tendsto_nativeFiniteGapApproximation_frequency 1 3 (by norm_num) q n)
  have hident : F n (nativeHillSource 1 q.val) =
      (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3 :=
    tendsto_nhds_unique hlimF ((hlimω.sub tendsto_const_nhds).congr' heq.symm)
  rw [hp] at hqseries
  exact ⟨hqseries.1,hident,hident.symm.trans hqseries.2⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
