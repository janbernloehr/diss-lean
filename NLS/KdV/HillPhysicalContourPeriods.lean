import NLS.ComplexAnalysis.ConvexCutCirclePeriod
import NLS.ComplexAnalysis.RealCenteredCircleHomotopy
import NLS.KdV.HillFreeContourPhysicalBandBounds
import NLS.KdV.HillFilledGapCutDomain
import NLS.KdV.HillEnergyRootAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillPhysicalContour_period_eq_free_contour
    (ε D : ℝ) (hc : HillComplexPeriodControl h0q h0r ε D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ ε) (k : ℕ) (hk : 1 ≤ k)
    (N : ℂ → ℂ) (hN : AnalyticOnNhd ℂ N univ) :
    (∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
      hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      N E/hillEnergyCanonicalRootProduct q hq hr E) =
    ∮ E in C((hillRealGapCenter q hq hr k : ℂ),
      hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      N E/hillEnergyCanonicalRootProduct q hq hr E := by
  let Ω : Set ℂ := {z | z.re ∈ Ioo (hillRealLabels q hq hr (2*k-2)) (hillRealLabels q hq hr (2*k+1))}
  let K := segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ)
  have hΩ : IsOpen Ω := isOpen_Ioo.preimage continuous_re
  have hconv : Convex ℝ Ω := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
  have hK : IsClosed K := by
    apply IsCompact.isClosed
    rw [show K = segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ)
      (hillRealLabels q hq hr (2*k) : ℂ) from rfl,segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hball₀ : closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ⊆ Ω := by
    intro z hz
    have hb := hillFreeContour_physical_band_bounds_of_control h0q h0r ε D hc q hq hr hp k hk
    have hre := re_bounds_of_mem_realCenteredClosedBall hz
    exact ⟨by linarith [hb.1,hre.1],by linarith [hb.2,hre.2]⟩
  have hball₁ : closedBall (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) ⊆ Ω :=
    fun z hz => hillRealGapContour_closedBall_real_bounds q hq hr k hk z hz
  have hf : DifferentiableOn ℂ (fun E => N E/hillEnergyCanonicalRootProduct q hq hr E) (Ω \ K) := by
    intro E hE
    have he := mem_hillL2RealCutDomain_of_filled_not_gap q hq hr k hk E (Or.inr hE.1) hE.2
    exact ((hN E (mem_univ _)).div (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr E he)
      (hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr E he)).differentiableAt.differentiableWithinAt
  exact circleIntegral_eq_of_convex_cut_domain _ Ω K _ _ _ _ hΩ hconv hK
    (add_nonneg (hillRealGapContour_geometry 0 h0q h0r k hk).1
      (hillRealGapContour_geometry 0 h0q h0r k hk).2.1.le)
    (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
      (hillRealGapContour_geometry q hq hr k hk).2.1.le)
    hball₀ hball₁ (hillRealGap_mem_free_contour_ball_of_control h0q h0r ε D hc q hq hr hp k hk)
    (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk) hf

end NLS.KdV
