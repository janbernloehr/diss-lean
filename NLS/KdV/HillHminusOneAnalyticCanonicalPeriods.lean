import NLS.KdV.HillHminusOneTraceChartRealAgreement
import NLS.KdV.HillHminusOneJointGapPeriodGerms
import NLS.KdV.HillHminusOneGapContourContinuity
import NLS.ComplexAnalysis.NearbyCircleHomotopy

/-! # Actual canonical H^-1 gap periods are locally analytic at every index

Uniform source agreement on a compact contour collar and continuity of the
canonical circle identify the analytic reference integrals with the actual
moving-circle periods for every nearby real potential. One neighborhood
works for all polynomial moments and the shifted cubic period, including
central and collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_analytic_canonical_gap_periods
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ q ∈ W ∧
      ∃ A : ℕ → PeriodOneHminusOne → ℂ, ∃ R : PeriodOneHminusOne → ℂ,
        (∀ m, AnalyticOnNhd ℂ (A m) W) ∧ AnalyticOnNhd ℂ R W ∧
        ∀ p ∈ W, ∀ hp : IsRealPeriodOneHminusOne p,
          (∀ m, A m p = hillHminusRealGapContourMoment p hp n m) ∧
          R p = hillHminusRealGapCubicContourMoment p hp n := by
  obtain ⟨Ω,hΩ,hcircle,V,hV,hq,F,hF,hbase,htrace,A,R,hAformula,hRformula,hA,hR⟩ :=
    exists_hillHminus_analytic_gap_period_germs q hr n
  let c₀ : ℂ := hillHminusRealGapCenter q hr (n : ℕ)
  let r₀ := hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)
  let S := sphere c₀ r₀
  have hr₀ : 0 ≤ r₀ := (hillHminusRealGapContourRadius_pos q hr n).le
  have hS : IsCompact S := isCompact_sphere _ _
  obtain ⟨δ,hδ,hcollar⟩ := hS.exists_cthickening_subset_open hΩ hcircle
  let K := cthickening δ S
  obtain ⟨U,hU,hqU,hUV,hagree⟩ := exists_hillHminus_trace_chart_compact_real_agreement
    q hr Ω V hΩ hV hq F hF hbase htrace K hS.cthickening hcollar
  obtain ⟨T,hT,hqT,hclose⟩ := exists_hillHminus_gap_circle_close_neighborhood q hr (n : ℕ) δ hδ
  let W := U ∩ T
  have hWV : W ⊆ V := fun p hp => hUV hp.1
  refine ⟨W,hU.inter hT,⟨hqU,hqT⟩,A,R,fun m => (hA m).1.mono hWV,hR.1.mono hWV,?_⟩
  intro p hp hpr
  let c₁ : ℂ := hillHminusRealGapCenter p hpr (n : ℕ)
  let r₁ := hillHminusRealGapHalfLength p hpr (n : ℕ)+hillHminusRealGapCollar p hpr (n : ℕ)
  have hdist : dist c₁ c₀ + |r₁-r₀| ≤ δ := (hclose p hp.2 hpr).le
  have hFp : AnalyticOnNhd ℂ (fun z => F (z,p)) Ω := by
    intro z hz
    exact (hF (z,p) ⟨hz,hWV hp⟩).comp (f := fun z : ℂ => (z,p))
      (analyticAt_id.prod analyticAt_const)
  have hpoint (θ : ℝ) : F (circleMap c₁ r₁ θ,p) = hillHminusRealCutPrimitive p (circleMap c₁ r₁ θ) :=
    hagree p hp.1 hpr (circleMap_mem_collar_of_close_centers_radii c₀ c₁ r₀ r₁ δ hr₀ hdist θ)
  constructor
  · intro m
    have hdeform := circleIntegral_eq_of_close_circle_collar
      (fun z => z^m*F (z,p)) Ω ((analyticOnNhd_id.pow m).mul hFp)
      c₀ c₁ r₀ r₁ δ hr₀ hcollar hdist
    have heq := circleIntegral_eq_of_circleMap_eq
      (fun z => z^m*F (z,p)) (fun z => z^m*hillHminusRealCutPrimitive p z) c₁ r₁
      (fun θ => by rw [hpoint θ])
    rw [hAformula m p]
    change -(Real.pi : ℂ)⁻¹ * (∮ z in C(c₀,r₀), z^m*F (z,p)) =
      -(Real.pi : ℂ)⁻¹ * (∮ z in C(c₁,r₁), z^m*hillHminusRealCutPrimitive p z)
    rw [← hdeform,heq]
  · have hdeform := circleIntegral_eq_of_close_circle_collar
      (fun z => (F (z,p)+I*(n : ℂ)*Real.pi)^3) Ω
      ((hFp.add analyticOnNhd_const).pow 3) c₀ c₁ r₀ r₁ δ hr₀ hcollar hdist
    have heq := circleIntegral_eq_of_circleMap_eq
      (fun z => (F (z,p)+I*(n : ℂ)*Real.pi)^3)
      (fun z => (hillHminusRealCutPrimitive p z+I*(n : ℂ)*Real.pi)^3) c₁ r₁
      (fun θ => by rw [hpoint θ])
    rw [hRformula p]
    change (Real.pi : ℂ)⁻¹ * (∮ z in C(c₀,r₀), (F (z,p)+I*(n : ℂ)*Real.pi)^3) =
      (Real.pi : ℂ)⁻¹ * (∮ z in C(c₁,r₁), (hillHminusRealCutPrimitive p z+I*(n : ℂ)*Real.pi)^3)
    rw [← hdeform,heq]

end NLS.KdV
