import NLS.KdV.HillL2HalfPlaneSheets
import NLS.ComplexAnalysis.UpperTracePrimitiveExtension

/-! # Actual upper boundary values at every regular real Hill energy

The source primitive and root extend across every real point away from
the characteristic zeros, with no high-energy restriction. The resulting
boundary functions have their actual logarithmic derivative and trace
identities on both low bands and low gap interiors.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

structure HillL2UpperRegularExtension (q : Coeff 2) (x ρ : ℝ) (L G : ℂ → ℂ) : Prop where
  root_analytic : AnalyticOnNhd ℂ L (ball (x : ℂ) ρ)
  analytic : AnalyticOnNhd ℂ G (ball (x : ℂ) ρ)
  data : ∀ z ∈ ball (x : ℂ) ρ,
    L z ≠ 0 ∧ L z ^ 2 = hillL2Radicand q z ∧
      HasDerivAt G (deriv (hillL2Discriminant q) z / L z) z ∧
        2 * cosh (G z) = hillL2Discriminant q z ∧ 2 * sinh (G z) = L z
  root_source : EqOn L (fun z => hillL2ContinuedRoot (z, q))
    (ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im})
  source : EqOn G (fun z => hillL2ContinuedPrimitive (z, q))
    (ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im})

theorem exists_hillL2UpperRegularExtension
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (x : ℝ) (hx : hillL2Radicand (SpectralWeight.one.toCoeff q) x ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ L G : ℂ → ℂ,
      HillL2UpperRegularExtension (SpectralWeight.one.toCoeff q) x ρ L G := by
  have hopen : IsOpen {z | hillL2Radicand (SpectralWeight.one.toCoeff q) z ≠ 0} :=
    isOpen_ne_fun (analyticOnNhd_hillL2Radicand _).continuous continuous_const
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hx)
  have hroot : AnalyticOnNhd ℂ (fun z => hillL2ContinuedRoot (z, SpectralWeight.one.toCoeff q))
      {z : ℂ | 0 < z.im} := by
    intro z hz
    exact (analyticOnNhd_hillL2ContinuedRoot _
      (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne')).comp
      (f := fun z : ℂ => (z, SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  let raw := SpectralWeight.one.toCoeff q
  let D := hillL2Discriminant raw
  let S : ℂ → ℂ := fun z => hillL2ContinuedRoot (z, raw)
  let P : ℂ → ℂ := fun z => hillL2ContinuedPrimitive (z, raw)
  have hDa : AnalyticOnNhd ℂ D (ball (x : ℂ) ρ) :=
    (analyticOnNhd_hillL2Discriminant raw).mono (subset_univ _)
  have hne : ∀ z ∈ ball (x : ℂ) ρ, D z ^ 2 - 4 ≠ 0 := hball
  have hsq : ∀ z : ℂ, 0 < z.im → S z ^ 2 = D z ^ 2 - 4 := by
    intro z hz
    exact hillL2ContinuedRoot_sq (z, raw)
      (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne')
  have hderiv : ∀ z : ℂ, 0 < z.im → HasDerivAt P (deriv D z / S z) z := by
    intro z hz
    exact hasDerivAt_hillL2ContinuedPrimitive (z, raw)
      (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne')
  have htr : ∀ z : ℂ, 0 < z.im → 2 * cosh (P z) = D z ∧ 2 * sinh (P z) = S z := by
    intro z hz
    exact hillL2ContinuedPrimitive_trace (z, raw)
      (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne')
  obtain ⟨L, G, hL, hG, hdata, hrootsource, hsource⟩ :=
    exists_upper_trace_primitive_extension_on_ball D S P x ρ hρ hDa hne hroot hsq hderiv htr
  refine ⟨ρ, hρ, L, G, ?_⟩
  exact ⟨hL, hG, hdata, hrootsource, hsource⟩

def hillL2UpperBoundaryPrimitive (q : Coeff 2) (x : ℝ) : ℂ :=
  (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)).limUnder (fun z => hillL2ContinuedPrimitive (z, q))

def hillL2UpperBoundaryRoot (q : Coeff 2) (x : ℝ) : ℂ :=
  (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)).limUnder (fun z => hillL2ContinuedRoot (z, q))

theorem HillL2UpperRegularExtension.primitive_tendsto
    {q : Coeff 2} {x ρ : ℝ} {L G : ℂ → ℂ}
    (h : HillL2UpperRegularExtension q x ρ L G) (y : ℝ) (hy : (y : ℂ) ∈ ball (x : ℂ) ρ) :
    Tendsto (fun z => hillL2ContinuedPrimitive (z, q)) (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ))
      (𝓝 (G y)) := by
  apply ((h.analytic y hy).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (isOpen_ball.mem_nhds hy)] with z hz hzB
  exact h.source ⟨hzB, hz⟩

theorem HillL2UpperRegularExtension.root_tendsto
    {q : Coeff 2} {x ρ : ℝ} {L G : ℂ → ℂ}
    (h : HillL2UpperRegularExtension q x ρ L G) (y : ℝ) (hy : (y : ℂ) ∈ ball (x : ℂ) ρ) :
    Tendsto (fun z => hillL2ContinuedRoot (z, q)) (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ))
      (𝓝 (L y)) := by
  apply ((h.root_analytic y hy).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (isOpen_ball.mem_nhds hy)] with z hz hzB
  exact h.root_source ⟨hzB, hz⟩

theorem HillL2UpperRegularExtension.boundary_eq
    {q : Coeff 2} {x ρ : ℝ} {L G : ℂ → ℂ}
    (h : HillL2UpperRegularExtension q x ρ L G) (y : ℝ) (hy : (y : ℂ) ∈ ball (x : ℂ) ρ) :
    hillL2UpperBoundaryRoot q y = L y ∧ hillL2UpperBoundaryPrimitive q y = G y := by
  let := real_upper_nhds_neBot y
  exact ⟨(h.root_tendsto y hy).limUnder_eq, (h.primitive_tendsto y hy).limUnder_eq⟩

theorem HillL2UpperRegularExtension.boundary_hasDerivAt
    {q : Coeff 2} {x ρ : ℝ} {L G : ℂ → ℂ}
    (h : HillL2UpperRegularExtension q x ρ L G) (hρ : 0 < ρ) :
    HasDerivAt (hillL2UpperBoundaryPrimitive q)
      (deriv (hillL2Discriminant q) x / hillL2UpperBoundaryRoot q x) x := by
  have hx : (x : ℂ) ∈ ball (x : ℂ) ρ := mem_ball_self hρ
  have heq : hillL2UpperBoundaryPrimitive q =ᶠ[𝓝 x] (fun y : ℝ => G y) := by
    have hnear : ∀ᶠ y : ℝ in 𝓝 x, (y : ℂ) ∈ ball (x : ℂ) ρ :=
      Complex.continuous_ofReal.continuousAt.eventually (isOpen_ball.mem_nhds hx)
    filter_upwards [hnear] with y hy
    exact (h.boundary_eq y hy).2
  rw [(h.boundary_eq x hx).1]
  exact ((h.data x hx).2.2.1.comp_ofReal).congr_of_eventuallyEq heq

theorem hillL2UpperBoundary_data
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (x : ℝ) (hx : hillL2Radicand (SpectralWeight.one.toCoeff q) x ≠ 0) :
    hillL2UpperBoundaryRoot (SpectralWeight.one.toCoeff q) x ≠ 0 ∧
      hillL2UpperBoundaryRoot (SpectralWeight.one.toCoeff q) x ^ 2 =
        hillL2Radicand (SpectralWeight.one.toCoeff q) x ∧
      HasDerivAt (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q))
        (deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) x /
          hillL2UpperBoundaryRoot (SpectralWeight.one.toCoeff q) x) x ∧
      2 * cosh (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x) =
        hillL2Discriminant (SpectralWeight.one.toCoeff q) x ∧
      2 * sinh (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x) =
        hillL2UpperBoundaryRoot (SpectralWeight.one.toCoeff q) x := by
  obtain ⟨ρ, hρ, L, G, h⟩ := exists_hillL2UpperRegularExtension q hq hr x hx
  have hxB : (x : ℂ) ∈ ball (x : ℂ) ρ := mem_ball_self hρ
  have hd := h.data x hxB
  have hb := h.boundary_eq x hxB
  exact ⟨hb.1.symm ▸ hd.1, by rw [hb.1]; exact hd.2.1,
    h.boundary_hasDerivAt hρ, by rw [hb.2]; exact hd.2.2.2.1,
    by rw [hb.2, hb.1]; exact hd.2.2.2.2⟩

theorem hillL2UpperBoundaryPrimitive_re_nonneg
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (x : ℝ) (hx : hillL2Radicand (SpectralWeight.one.toCoeff q) x ≠ 0) :
    0 ≤ (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).re := by
  obtain ⟨ρ, hρ, L, G, h⟩ := exists_hillL2UpperRegularExtension q hq hr x hx
  have hxB : (x : ℂ) ∈ ball (x : ℂ) ρ := mem_ball_self hρ
  let := real_upper_nhds_neBot x
  rw [(h.boundary_eq x hxB).2]
  apply ge_of_tendsto (continuous_re.continuousAt.tendsto.comp (h.primitive_tendsto x hxB))
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hillL2ContinuedPrimitive_re_pos q hq hr z hz).le

theorem tendsto_hillL2UpperBoundaryPrimitive
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (x : ℝ) (hx : hillL2Radicand (SpectralWeight.one.toCoeff q) x ≠ 0) :
    Tendsto (fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x)) := by
  obtain ⟨ρ, hρ, L, G, h⟩ := exists_hillL2UpperRegularExtension q hq hr x hx
  have hxB : (x : ℂ) ∈ ball (x : ℂ) ρ := mem_ball_self hρ
  rw [(h.boundary_eq x hxB).2]
  exact h.primitive_tendsto x hxB

end NLS.KdV
