import NLS.KdV.HillHminusOneHalfPlaneSheets
import NLS.KdV.HillHminusOneRealGapContours
import NLS.ComplexAnalysis.UpperTracePrimitiveExtension

/-! # Actual upper boundary values at every regular real H^-1 Hill energy

The source primitive and root extend across every real point away from
the characteristic zeros, with no high-energy restriction. The resulting
boundary functions have their actual logarithmic derivative and trace
identities on both low bands and low gap interiors.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem analyticOnNhd_hillHminusDiscriminant (q : PeriodOneHminusOne) :
    AnalyticOnNhd ℂ (hillHminusDiscriminant q) univ := by
  intro z _
  exact (analyticOnNhd_hillHminusDiscriminant_joint (z,q) (mem_univ _)).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

structure HillHminusUpperRegularExtension (q : PeriodOneHminusOne) (x ρ : ℝ) (L G : ℂ → ℂ) : Prop where
  root_analytic : AnalyticOnNhd ℂ L (ball (x : ℂ) ρ)
  analytic : AnalyticOnNhd ℂ G (ball (x : ℂ) ρ)
  data : ∀ z ∈ ball (x : ℂ) ρ,
    L z ≠ 0 ∧ L z ^ 2 = hillHminusRadicand q z ∧
      HasDerivAt G (deriv (hillHminusDiscriminant q) z / L z) z ∧
        2 * cosh (G z) = hillHminusDiscriminant q z ∧ 2 * sinh (G z) = L z
  root_source : EqOn L (fun z => hillHminusContinuedRoot (z, q))
    (ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im})
  source : EqOn G (fun z => hillHminusContinuedPrimitive (z, q))
    (ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im})

theorem exists_hillHminusUpperRegularExtension
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q)
    (x : ℝ) (hx : hillHminusRadicand (q) x ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ L G : ℂ → ℂ,
      HillHminusUpperRegularExtension (q) x ρ L G := by
  have hopen : IsOpen {z | hillHminusRadicand (q) z ≠ 0} :=
    isOpen_ne_fun (analyticOnNhd_hillHminusRadicand _).continuous continuous_const
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hx)
  have hroot : AnalyticOnNhd ℂ (fun z => hillHminusContinuedRoot (z, q))
      {z : ℂ | 0 < z.im} := by
    intro z hz
    exact (analyticOnNhd_hillHminusContinuedRoot _
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hz.ne')).comp
      (f := fun z : ℂ => (z, q)) (analyticAt_id.prod analyticAt_const)
  let raw := q
  let D := hillHminusDiscriminant raw
  let S : ℂ → ℂ := fun z => hillHminusContinuedRoot (z, raw)
  let P : ℂ → ℂ := fun z => hillHminusContinuedPrimitive (z, raw)
  have hDa : AnalyticOnNhd ℂ D (ball (x : ℂ) ρ) :=
    (analyticOnNhd_hillHminusDiscriminant raw).mono (subset_univ _)
  have hne : ∀ z ∈ ball (x : ℂ) ρ, D z ^ 2 - 4 ≠ 0 := hball
  have hsq : ∀ z : ℂ, 0 < z.im → S z ^ 2 = D z ^ 2 - 4 := by
    intro z hz
    exact hillHminusContinuedRoot_sq (z, raw)
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hz.ne')
  have hderiv : ∀ z : ℂ, 0 < z.im → HasDerivAt P (deriv D z / S z) z := by
    intro z hz
    exact hasDerivAt_hillHminusContinuedPrimitive (z, raw)
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hz.ne')
  have htr : ∀ z : ℂ, 0 < z.im → 2 * cosh (P z) = D z ∧ 2 * sinh (P z) = S z := by
    intro z hz
    exact hillHminusContinuedPrimitive_trace (z, raw)
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hz.ne')
  obtain ⟨L, G, hL, hG, hdata, hrootsource, hsource⟩ :=
    exists_upper_trace_primitive_extension_on_ball D S P x ρ hρ hDa hne hroot hsq hderiv htr
  refine ⟨ρ, hρ, L, G, ?_⟩
  exact ⟨hL, hG, hdata, hrootsource, hsource⟩

def hillHminusUpperBoundaryPrimitive (q : PeriodOneHminusOne) (x : ℝ) : ℂ :=
  (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)).limUnder (fun z => hillHminusContinuedPrimitive (z, q))

def hillHminusUpperBoundaryRoot (q : PeriodOneHminusOne) (x : ℝ) : ℂ :=
  (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)).limUnder (fun z => hillHminusContinuedRoot (z, q))

theorem HillHminusUpperRegularExtension.primitive_tendsto
    {q : PeriodOneHminusOne} {x ρ : ℝ} {L G : ℂ → ℂ}
    (h : HillHminusUpperRegularExtension q x ρ L G) (y : ℝ) (hy : (y : ℂ) ∈ ball (x : ℂ) ρ) :
    Tendsto (fun z => hillHminusContinuedPrimitive (z, q)) (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ))
      (𝓝 (G y)) := by
  apply ((h.analytic y hy).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (isOpen_ball.mem_nhds hy)] with z hz hzB
  exact h.source ⟨hzB, hz⟩

theorem HillHminusUpperRegularExtension.root_tendsto
    {q : PeriodOneHminusOne} {x ρ : ℝ} {L G : ℂ → ℂ}
    (h : HillHminusUpperRegularExtension q x ρ L G) (y : ℝ) (hy : (y : ℂ) ∈ ball (x : ℂ) ρ) :
    Tendsto (fun z => hillHminusContinuedRoot (z, q)) (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ))
      (𝓝 (L y)) := by
  apply ((h.root_analytic y hy).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (isOpen_ball.mem_nhds hy)] with z hz hzB
  exact h.root_source ⟨hzB, hz⟩

theorem HillHminusUpperRegularExtension.boundary_eq
    {q : PeriodOneHminusOne} {x ρ : ℝ} {L G : ℂ → ℂ}
    (h : HillHminusUpperRegularExtension q x ρ L G) (y : ℝ) (hy : (y : ℂ) ∈ ball (x : ℂ) ρ) :
    hillHminusUpperBoundaryRoot q y = L y ∧ hillHminusUpperBoundaryPrimitive q y = G y := by
  let := real_upper_nhds_neBot y
  exact ⟨(h.root_tendsto y hy).limUnder_eq, (h.primitive_tendsto y hy).limUnder_eq⟩

theorem HillHminusUpperRegularExtension.boundary_hasDerivAt
    {q : PeriodOneHminusOne} {x ρ : ℝ} {L G : ℂ → ℂ}
    (h : HillHminusUpperRegularExtension q x ρ L G) (hρ : 0 < ρ) :
    HasDerivAt (hillHminusUpperBoundaryPrimitive q)
      (deriv (hillHminusDiscriminant q) x / hillHminusUpperBoundaryRoot q x) x := by
  have hx : (x : ℂ) ∈ ball (x : ℂ) ρ := mem_ball_self hρ
  have heq : hillHminusUpperBoundaryPrimitive q =ᶠ[𝓝 x] (fun y : ℝ => G y) := by
    have hnear : ∀ᶠ y : ℝ in 𝓝 x, (y : ℂ) ∈ ball (x : ℂ) ρ :=
      Complex.continuous_ofReal.continuousAt.eventually (isOpen_ball.mem_nhds hx)
    filter_upwards [hnear] with y hy
    exact (h.boundary_eq y hy).2
  rw [(h.boundary_eq x hx).1]
  exact ((h.data x hx).2.2.1.comp_ofReal).congr_of_eventuallyEq heq

theorem hillHminusUpperBoundary_data
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q)
    (x : ℝ) (hx : hillHminusRadicand (q) x ≠ 0) :
    hillHminusUpperBoundaryRoot (q) x ≠ 0 ∧
      hillHminusUpperBoundaryRoot (q) x ^ 2 =
        hillHminusRadicand (q) x ∧
      HasDerivAt (hillHminusUpperBoundaryPrimitive (q))
        (deriv (hillHminusDiscriminant (q)) x /
          hillHminusUpperBoundaryRoot (q) x) x ∧
      2 * cosh (hillHminusUpperBoundaryPrimitive (q) x) =
        hillHminusDiscriminant (q) x ∧
      2 * sinh (hillHminusUpperBoundaryPrimitive (q) x) =
        hillHminusUpperBoundaryRoot (q) x := by
  obtain ⟨ρ, hρ, L, G, h⟩ := exists_hillHminusUpperRegularExtension q hr x hx
  have hxB : (x : ℂ) ∈ ball (x : ℂ) ρ := mem_ball_self hρ
  have hd := h.data x hxB
  have hb := h.boundary_eq x hxB
  exact ⟨hb.1.symm ▸ hd.1, by rw [hb.1]; exact hd.2.1,
    h.boundary_hasDerivAt hρ, by rw [hb.2]; exact hd.2.2.2.1,
    by rw [hb.2, hb.1]; exact hd.2.2.2.2⟩

theorem hillHminusUpperBoundaryPrimitive_re_nonneg
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q)
    (x : ℝ) (hx : hillHminusRadicand (q) x ≠ 0) :
    0 ≤ (hillHminusUpperBoundaryPrimitive (q) x).re := by
  obtain ⟨ρ, hρ, L, G, h⟩ := exists_hillHminusUpperRegularExtension q hr x hx
  have hxB : (x : ℂ) ∈ ball (x : ℂ) ρ := mem_ball_self hρ
  let := real_upper_nhds_neBot x
  rw [(h.boundary_eq x hxB).2]
  apply ge_of_tendsto (continuous_re.continuousAt.tendsto.comp (h.primitive_tendsto x hxB))
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hillHminusContinuedPrimitive_re_pos q hr z hz).le

theorem tendsto_hillHminusUpperBoundaryPrimitive
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q)
    (x : ℝ) (hx : hillHminusRadicand (q) x ≠ 0) :
    Tendsto (fun z => hillHminusContinuedPrimitive (z, q))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (hillHminusUpperBoundaryPrimitive (q) x)) := by
  obtain ⟨ρ, hρ, L, G, h⟩ := exists_hillHminusUpperRegularExtension q hr x hx
  have hxB : (x : ℂ) ∈ ball (x : ℂ) ρ := mem_ball_self hρ
  rw [(h.boundary_eq x hxB).2]
  exact h.primitive_tendsto x hxB

end NLS.KdV
