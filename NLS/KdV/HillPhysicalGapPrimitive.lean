import NLS.KdV.HillEnergyRootIdentification
import NLS.KdV.HillDeflatedTraceCharts
import NLS.KdV.HillL2EndpointContinuity
import NLS.ComplexAnalysis.QuadraticPrimitiveIdentification

/-! # The actual endpoint-normalized Hill primitive in a quadratic gap chart -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hasDerivAt_hillShiftedGapPrimitive (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain q hq hr) :
    HasDerivAt (fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w+I*(n : ℂ)*Real.pi)
      (hillDeflatedTraceNumerator q hq hr n z /
        endpointRoot (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ) z) z := by
  have hd := (hasDerivAt_hillL2RealCutPrimitive_energyProduct q hq hr z hz).add_const (I*(n : ℂ)*Real.pi)
  rw [hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated q hq hr n hn z]
    at hd
  convert! hd using 1
  rw [hillDeflatedTraceNumerator,div_div]
  congr 1
  ring

theorem tendsto_hillShiftedGapPrimitive_left (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun z => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z+I*(n : ℂ)*Real.pi)
      (𝓝 (hillRealLabels q hq hr (2*n-1) : ℂ)) (𝓝 0) := by
  have hc := (continuousAt_hillL2RealCutPrimitive_label q hq hr (2*n-1)).add_const (I*(n : ℂ)*Real.pi)
  have hvalue : hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)
      (hillRealLabels q hq hr (2*n-1) : ℂ)+I*(n : ℂ)*Real.pi=0 := by
    simp only [hillL2RealCutPrimitive,ofReal_im,if_true,ofReal_re]
    rw [(hillL2UpperBoundaryPrimitive_pair_indexed q hq hr n hn).1]
    ring
  simpa only [hvalue] using hc.tendsto

/-- The deflated logarithmic differential has zero cosine mean on every
actual gap, including collapsed gaps and low spectral indices. -/
theorem integral_hillDeflatedTraceNumerator_cosine_eq_zero
    (n : ℕ) (hn : 1 ≤ n) :
    (∫ θ in (0 : ℝ)..Real.pi, hillDeflatedTraceNumerator q hq hr n
      (cosineGapPoint (hillRealGapCenter q hq hr n) (hillRealGapHalfLength q hq hr n) (θ : ℂ)))=0 := by
  let τ := hillRealGapCenter q hq hr n
  let δ := hillRealGapHalfLength q hq hr n
  let η := hillRealGapCollar q hq hr n
  have hgeo := hillRealGapContour_geometry q hq hr n hn
  have hδ : 0 ≤ δ := hgeo.1
  have hη : 0 < η := hgeo.2.1
  have hleft : (τ : ℂ)-(δ : ℂ)=(hillRealLabels q hq hr (2*n-1) : ℂ) := by
    rw [←ofReal_sub,hgeo.2.2.1]
  have hright : (τ : ℂ)+(δ : ℂ)=(hillRealLabels q hq hr (2*n) : ℂ) := by
    rw [←ofReal_add,hgeo.2.2.2.1]
  have hg : AnalyticOnNhd ℂ (hillDeflatedTraceNumerator q hq hr n)
      (closedBall (τ : ℂ) (δ+η)) :=
    (analyticOnNhd_hillDeflatedTraceNumerator q hq hr n hn).mono
      (hillRealGapContour_closedBall_subset_filledDomain q hq hr n hn)
  apply cosine_mean_eq_zero_of_primitive (hillDeflatedTraceNumerator q hq hr n)
    (fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w+I*(n : ℂ)*Real.pi)
    (τ : ℂ) (δ : ℂ) (δ+η/2) (δ+η)
    (by rw [norm_real,Real.norm_eq_abs,abs_of_nonneg hδ];linarith) (by linarith) hg
  intro z hz
  have hzr : z ∉ segment ℝ ((τ : ℂ)-δ) ((τ : ℂ)+δ) := by
    intro hk
    have hm : z ∈ ball (τ : ℂ) (δ+η/2) :=
      (convex_ball (τ : ℂ) (δ+η/2)).segment_subset
        (by simp only [mem_ball,dist_eq_norm,sub_sub_cancel_left,norm_neg,norm_real,
          Real.norm_eq_abs,abs_of_nonneg hδ];linarith)
        (by simp only [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_real,
          Real.norm_eq_abs,abs_of_nonneg hδ];linarith) hk
    exact sphere_disjoint_ball.le_bot ⟨hz,hm⟩
  have hzcut : z ∈ hillL2RealCutDomain q hq hr := hgeo.2.2.2.2 ⟨
    closedBall_subset_ball (by linarith : δ+η/2 < δ+2*η) (sphere_subset_closedBall hz),
    by simpa only [hleft,hright] using hzr⟩
  simpa only [hleft,hright] using hasDerivAt_hillShiftedGapPrimitive q hq hr n hn z hzcut

/-- Every regular amplitude solving the ACTUAL deflated trace equation is
the actual shifted physical primitive, with its exact fixed sheet sign. -/
theorem hillShiftedGapPrimitive_eq_root_amplitude
    (n : ℕ) (hn : 1 ≤ n) (H : ℂ → ℂ) (R : ℝ)
    (hδ : hillRealGapHalfLength q hq hr n < R)
    (hR : R ≤ hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n)
    (hH : AnalyticOnNhd ℂ H (ball (hillRealGapCenter q hq hr n : ℂ) R))
    (he : ∀ z ∈ ball (hillRealGapCenter q hq hr n : ℂ) R,
      ((z-(hillRealGapCenter q hq hr n : ℂ))^2-(hillRealGapHalfLength q hq hr n : ℂ)^2)*deriv H z+
        (z-(hillRealGapCenter q hq hr n : ℂ))*H z=hillDeflatedTraceNumerator q hq hr n z) :
    ∀ z ∈ ball (hillRealGapCenter q hq hr n : ℂ) R \
        segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ),
      hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z+I*(n : ℂ)*Real.pi =
        H z*endpointRoot (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ) z := by
  obtain ⟨hd,hη,hl,hu,hsub⟩ := hillRealGapContour_geometry q hq hr n hn
  have hleft : (hillRealGapCenter q hq hr n : ℂ)-(hillRealGapHalfLength q hq hr n : ℂ)=
      (hillRealLabels q hq hr (2*n-1) : ℂ) := by rw [←ofReal_sub,hl]
  have hright : (hillRealGapCenter q hq hr n : ℂ)+(hillRealGapHalfLength q hq hr n : ℂ)=
      (hillRealLabels q hq hr (2*n) : ℂ) := by rw [←ofReal_add,hu]
  have hdR : ‖(hillRealGapHalfLength q hq hr n : ℂ)‖ < R := by
    simpa only [norm_real,Real.norm_eq_abs,abs_of_nonneg hd] using hδ
  have hsub' : ball (hillRealGapCenter q hq hr n : ℂ) R \
      segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ) ⊆
        hillL2RealCutDomain q hq hr := fun z hz => hsub ⟨
          ball_subset_ball (by linarith) hz.1,hz.2⟩
  have hF := fun z hz => hasDerivAt_hillShiftedGapPrimitive q hq hr n hn z (hsub' hz)
  have hzero := (tendsto_hillShiftedGapPrimitive_left q hq hr n hn).mono_left
    (nhdsWithin_le_nhds : 𝓝[ball (hillRealGapCenter q hq hr n : ℂ) R \
      segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ)]
        (hillRealLabels q hq hr (2*n-1) : ℂ) ≤ 𝓝 _)
  have hid := root_amplitude_eq_normalized_primitive H (hillDeflatedTraceNumerator q hq hr n)
    (fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w+I*(n : ℂ)*Real.pi)
    (hillRealGapCenter q hq hr n : ℂ) (hillRealGapHalfLength q hq hr n : ℂ) R hdR hH he
    (by simpa only [hleft,hright] using hF) (by simpa only [hleft,hright] using hzero)
  simpa only [Set.EqOn,hleft,hright] using! hid

end NLS.KdV
