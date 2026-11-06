import NLS.KdV.PhysicalMiuraFrequencyChart
import NLS.Articles.KdVConvexity.NativeFiniteGapApproximation
import NLS.Articles.KdVConvexity.FiniteGapPhysicalFrequencyIdentity
import NLS.Articles.KdVKdV2Frequencies.NativeFrequencyContinuity

/-! # Infinite-gap physical frequency recovery on each rough Miura chart

Actual finite-gap approximation converges in the original H1 norm.
Both the intrinsic Hamiltonian frequency and the chart correction are
continuous there, so the exact finite-gap formula extends to every source.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVKdV2Frequencies
namespace NLS.Articles.KdVConvexity

theorem native_physical_frequency_eq_miura_chart (D : GlobalRoughAbelianForwardData)
    (B : PhysicalMiuraFrequencyChart)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
    (hq : hillOriginalHminusSource (nativeHillPhysicalSource 1 q.val q.property.1).val ∈ B.domain)
    (n : ℕ+) :
    (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ) - (2*(n : ℂ)*Real.pi)^3 =
      B.correction n (hillOriginalHminusSource (nativeHillPhysicalSource 1 q.val q.property.1).val) := by
  let Q := nativeFiniteGapApproximation D 1 q
  let R (p : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) :=
    hillOriginalHminusSource (nativeHillPhysicalSource 1 p.val p.property.1).val
  have hR : Continuous R := hillOriginalHminusSource.continuous.comp
    (continuous_subtype_val.comp (continuous_nativeHillPhysicalSource 1))
  have hQ := tendsto_nativeFiniteGapApproximation D 1 q
  have hRQ : Tendsto (fun N => R (Q N)) atTop (𝓝 (R q)) := hR.continuousAt.tendsto.comp hQ
  have hev : ∀ᶠ N in atTop, R (Q N) ∈ B.domain := hRQ (B.domain_open.mem_nhds hq)
  have heq :
      (fun N => (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) (Q N) n : ℂ) - (2*(n : ℂ)*Real.pi)^3)
        =ᶠ[atTop] (fun N => B.correction n (R (Q N))) := by
    filter_upwards [hev] with N hN
    obtain ⟨S,hS⟩ := nativeFiniteGapApproximation_finite_gap D 1 q N
    have he := D.native_finiteGap_kdv_frequency_moments_all_gaps (Q N) S hS n
    rw [B.correction_eq_physical _ hN n]
    rw [tsum_weighted_hillPhysicalFrequencyMoment_eq_intrinsic]
    exact he
  have hleft : Tendsto
      (fun N => (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) (Q N) n : ℂ) - (2*(n : ℂ)*Real.pi)^3)
      atTop (𝓝 ((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ) - (2*(n : ℂ)*Real.pi)^3)) :=
    ((Complex.continuous_ofReal.comp (D.continuous_nativeSourceHierarchyFrequency 1 3 (by norm_num) n)).sub
      continuous_const).continuousAt.tendsto.comp hQ
  have hright : Tendsto (fun N => B.correction n (R (Q N))) atTop (𝓝 (B.correction n (R q))) :=
    (B.analytic_correction n (R q) hq).continuousAt.tendsto.comp hRQ
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

/-- Physical recovery uses the independently defined original energy
derivative, including closed selected modes and infinitely many open gaps. -/
theorem original_physical_frequency_eq_miura_chart (D : GlobalRoughAbelianForwardData)
    (B : PhysicalMiuraFrequencyChart)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
    (hq : hillOriginalHminusSource (nativeHillPhysicalSource 1 q.val q.property.1).val ∈ B.domain)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1)
    (ha : D.nativeSourceActionSequence 1 3 (by norm_num) q = originalPositiveActionInsertion b.val)
    (n : ℕ+) :
    originalPhysicalFrequency b n - (2*(n : ℂ)*Real.pi)^3 =
      B.correction n (hillOriginalHminusSource (nativeHillPhysicalSource 1 q.val q.property.1).val) := by
  have he := native_physical_frequency_eq_miura_chart D B q hq n
  rw [nativeSourceFrequency_eq_originalPhysicalFrequency D q b ha n] at he
  exact he

/-- Every original action point has an actual physical realization and
a common rough analytic chart recovering ALL its nonlinear frequencies. -/
theorem exists_original_physical_frequency_miura_recovery
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) :
    ∃ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)),
      ∃ B : PhysicalMiuraFrequencyChart,
        physicalHilbertActions hillH1SpectralWeight (nativeH1PhysicalRepresentative q) = originalActionInclusion b.val ∧
        hillOriginalHminusSource (nativeHillPhysicalSource 1 q.val q.property.1).val ∈ B.domain ∧
        ∀ n : ℕ+, originalPhysicalFrequency b n - (2*(n : ℂ)*Real.pi)^3 =
          B.correction n (hillOriginalHminusSource (nativeHillPhysicalSource 1 q.val q.property.1).val) := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  let q := nativeOriginalActionSource D b
  let p := nativeHillPhysicalSource 1 q.val q.property.1
  obtain ⟨B,hB,_⟩ := exists_physicalMiuraFrequencyChart (hillOriginalHminusSource p.val)
    (hillOriginalHminusSource_real p.val p.property.2) 0
  exact ⟨q,B,nativeOriginalActionSource_physical_actions D b,hB,
    original_physical_frequency_eq_miura_chart D B q hB b (nativeOriginalActionSource_actions D b)⟩

end NLS.Articles.KdVConvexity
