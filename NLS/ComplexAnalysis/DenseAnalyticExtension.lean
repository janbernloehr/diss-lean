import NLS.ComplexAnalysis.DenseSegmentComplement
import NLS.ComplexAnalysis.ContinuousBoundaryTransfer
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Analytic extension determined on a dense set

Relative limits choose compatible local analytic extensions. If only a
finite set of points remains, a common finite boundary value and the
Cauchy removable-singularity theorem fill those points as well.
-/
noncomputable section
open Set Filter Topology Metric
namespace NLS.ComplexAnalysis

/-- The extension selected by relative limits from a dense domain. -/
def denseLimitExtension (f : ℂ → ℂ) (D : Set ℂ) (z : ℂ) : ℂ :=
  limUnder (𝓝[D] z) f

theorem denseLimitExtension_eq_of_tendsto (f : ℂ → ℂ) (D : Set ℂ)
    (hD : Dense D) (z A : ℂ) (h : Tendsto f (𝓝[D] z) (𝓝 A)) :
    denseLimitExtension f D z = A := by
  let : NeBot (𝓝[D] z) := mem_closure_iff_nhdsWithin_neBot.mp (hD z)
  exact h.limUnder_eq

theorem denseLimitExtension_eqOn_local (f P : ℂ → ℂ) (D B : Set ℂ)
    (hD : Dense D) (hB : IsOpen B) (hP : ContinuousOn P B)
    (hmatch : EqOn P f (B ∩ D)) : EqOn (denseLimitExtension f D) P B := by
  intro z hz
  apply denseLimitExtension_eq_of_tendsto f D hD
  apply ((hP.continuousAt (hB.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (hB.mem_nhds hz)] with w hwD hwB
  exact hmatch ⟨hwB,hwD⟩

/-- Local analytic charts with the same dense exterior data determine
one analytic extension without additional choices of overlap signs. -/
theorem denseLimitExtension_analyticOnNhd (f : ℂ → ℂ) (D Ω : Set ℂ)
    (hD : Dense D)
    (hlocal : ∀ z ∈ Ω, ∃ B : Set ℂ, ∃ P : ℂ → ℂ,
      IsOpen B ∧ z ∈ B ∧ AnalyticOnNhd ℂ P B ∧ EqOn P f (B ∩ D)) :
    AnalyticOnNhd ℂ (denseLimitExtension f D) Ω := by
  intro z hz
  obtain ⟨B,P,hB,hzB,hP,hmatch⟩ := hlocal z hz
  apply (hP z hzB).congr
  filter_upwards [hB.mem_nhds hzB] with w hw
  exact (denseLimitExtension_eqOn_local f P D B hD hB hP.continuousOn hmatch hw).symm

/-- A continuous function holomorphic off a countable set in an open
domain is holomorphic everywhere in that domain. -/
theorem analyticOnNhd_of_continuousOn_off_countable
    (F : ℂ → ℂ) (Ω S : Set ℂ) (hΩ : IsOpen Ω) (hS : S.Countable)
    (hc : ContinuousOn F Ω) (ha : AnalyticOnNhd ℂ F (Ω \ S)) :
    AnalyticOnNhd ℂ F Ω := by
  intro z hz
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hz)
  let R : NNReal := ⟨r/2,by positivity⟩
  have hR : (0 : NNReal) < R := by change 0 < r/2; positivity
  have hsub : closedBall z (R : ℝ) ⊆ Ω :=
    (closedBall_subset_ball (by change r/2 < r; linarith)).trans hball
  exact (Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable hS
    (hc.mono hsub) (fun w hw => (ha w ⟨hsub (ball_subset_closedBall hw.1),hw.2⟩).differentiableAt)
    hR).analyticAt

/-- A dense-limit extension analytic away from finitely many points
is analytic across them if the original data tend to the same value
there. The removed points need not lie in the original dense set. -/
theorem denseLimitExtension_analyticOnNhd_of_finite_boundary
    (f : ℂ → ℂ) (D Ω S : Set ℂ) (A : ℂ)
    (hD : Dense D) (hΩ : IsOpen Ω) (hS : S.Finite)
    (ha : AnalyticOnNhd ℂ (denseLimitExtension f D) (Ω \ S))
    (hmatch : EqOn (denseLimitExtension f D) f ((Ω \ S) ∩ D))
    (hlim : ∀ a ∈ Ω ∩ S, Tendsto f (𝓝[D] a) (𝓝 A)) :
    AnalyticOnNhd ℂ (denseLimitExtension f D) Ω := by
  apply analyticOnNhd_of_continuousOn_off_countable _ Ω S hΩ hS.countable _ ha
  intro a haΩ
  by_cases haS : a ∈ S
  · have hval := denseLimitExtension_eq_of_tendsto f D hD a A (hlim a ⟨haΩ,haS⟩)
    have ht := tendsto_continuous_extension_on_closure f (denseLimitExtension f D)
      D (Ω \ S) a A (hΩ.sdiff hS.isClosed) ha.continuousOn hmatch (hlim a ⟨haΩ,haS⟩)
    rw [hD.closure_eq,inter_univ] at ht
    have hs : Tendsto (denseLimitExtension f D) (𝓝[Ω ∩ S] a) (𝓝 A) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (denseLimitExtension_eq_of_tendsto f D hD z A (hlim z hz)).symm
    change Tendsto (denseLimitExtension f D) (𝓝[Ω] a) (𝓝 (denseLimitExtension f D a))
    rw [hval,← sdiff_union_inter Ω S,nhdsWithin_union]
    exact tendsto_sup.mpr ⟨ht,hs⟩
  · exact ((ha a ⟨haΩ,haS⟩).continuousAt).continuousWithinAt

end NLS.ComplexAnalysis
