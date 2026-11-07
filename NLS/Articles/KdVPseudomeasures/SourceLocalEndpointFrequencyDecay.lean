import NLS.Articles.KdVPseudomeasures.SourceEndpointGapSquareBound
import NLS.Articles.KdVPseudomeasures.OriginalHillMomentAllIndexBounds
import NLS.Articles.KdVPseudomeasures.OriginalHillRoughFrequencyReality
import NLS.KdV.HillMomentUniformPowerDecay

/-! Uniform frequency-tail decay on an actual native neighborhood of
each real source, for every original endpoint potential in a fixed norm ball. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem exists_local_source_endpoint_frequency_decay (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (c : HillRealMeanZeroSource) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ hillRealMeanZeroInclusion c ∈ U ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ q : Potential r, ‖q.val‖ ≤ R →
        sourceNativePeriodOneCLM r hr q.val ∈ U → ∀ n : ℕ+, N ≤ (n:ℕ) →
          ‖(hillRoughKdVFrequency n (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q)):ℂ)-
              (2*(Real.pi:ℂ)*(n:ℤ))^3‖ < ε := by
  obtain ⟨C,_,hgap⟩ := source_uniform_canonical_gapSquare_bound r hr R
  obtain ⟨P,D,hc,hfull,_⟩ := originalHill_exists_all_index_frequency_moment_bounds c
  have hcP : hillRealMeanZeroInclusion c ∈ P.source := (D.subset hc).1
  have hcr : IsRealPeriodOneHminusOne (hillRealMeanZeroInclusion c) := by intro k; exact c.property k
  obtain ⟨ρ,a,hρ,ha,hmid⟩ := P.exists_uniform_source_frequency_midpoint_index_lower_bound _ hcP hcr
  have hfull' : ∀ q ∈ D.source, ∀ n m : ℕ+,
      ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 q‖ ≤
        D.constant*‖NLS.ZakharovShabat.sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ)‖^2*
          Coeff.positiveMomentKernel n m := hfull
  obtain ⟨B,_,hlim,hbound⟩ := P.exists_uniform_centeredMomentSeries_power_decay D r hr.2 a C ha hfull'
  refine ⟨D.source ∩ ball (hillRealMeanZeroInclusion c) ρ,D.source_open.inter isOpen_ball,
    ⟨hc,mem_ball_self hρ⟩,?_⟩
  intro ε hε
  have hcast : Tendsto (fun j : ℕ => (j:ℤ)) atTop cofinite :=
    Int.ofNat_injective.tendsto_cofinite.mono_left atTop_le_cofinite
  have hsmall : ∀ᶠ j : ℕ in atTop, B (j:ℤ)<ε/12 :=
    (hlim.comp hcast).eventually (Iio_mem_nhds (by linarith : (0:ℝ)<ε/12))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hsmall
  refine ⟨N,?_⟩
  intro q hq hqU n hn
  have hseries := hbound (sourceNativePeriodOneCLM r hr q.val) hqU.1
    (hmid _ hqU.2) (hgap q hq) n
  have hqd : hillRealMeanZeroInclusion (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q)) ∈ D.source :=
    hqU.1
  rw [hillRoughKdVFrequency_complex_eq_local P D n _ hqd,
    originalHillRealMeanZeroSource_inclusion,originalPeriodOneCoefficients_sourceOriginalPotential]
  rw [show (2*(Real.pi:ℂ)*(n:ℤ))^3-
      12*P.centeredSecondMomentSeries D.ambient n
        (sourceNativePeriodOneCLM r hr q.val)-
        (2*(Real.pi:ℂ)*(n:ℤ))^3 =
      -12*P.centeredSecondMomentSeries D.ambient n
        (sourceNativePeriodOneCLM r hr q.val) by ring,
    norm_mul,norm_neg,Complex.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left hseries (by norm_num : (0:ℝ)≤12)).trans_lt (by
    have h := hN (n:ℕ) hn
    nlinarith)

end NLS.Articles.KdVPseudomeasures
