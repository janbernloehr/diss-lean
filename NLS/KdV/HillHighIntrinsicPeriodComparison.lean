import NLS.KdV.HillHighFreeContourBandBounds
import NLS.KdV.HillPhysicalContourPeriods

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillHighPhysicalContour_period_eq_free_contour
    (Ncut : ℕ) (hNcut : 1 ≤ Ncut) (B D : ℝ) (hc : HillComplexTailPeriodControl h0q h0r Ncut B D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B) (k : ℕ) (hk : Ncut ≤ k)
    (N : ℂ → ℂ) (hN : AnalyticOnNhd ℂ N univ) :
    (∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
      hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      N E/hillEnergyCanonicalRootProduct q hq hr E) =
    ∮ E in C((hillRealGapCenter q hq hr k : ℂ),
      hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      N E/hillEnergyCanonicalRootProduct q hq hr E := by
  have hk1 : 1 ≤ k := hNcut.trans hk
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
    have hb := hillHighFreeContour_physical_band_bounds_of_control h0q h0r Ncut hNcut B D hc q hq hr hp k hk
    have hre := re_bounds_of_mem_realCenteredClosedBall hz
    exact ⟨by linarith [hb.1,hre.1],by linarith [hb.2,hre.2]⟩
  have hball₁ : closedBall (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) ⊆ Ω :=
    fun z hz => hillRealGapContour_closedBall_real_bounds q hq hr k hk1 z hz
  have hf : DifferentiableOn ℂ (fun E => N E/hillEnergyCanonicalRootProduct q hq hr E) (Ω \ K) := by
    intro E hE
    have he := mem_hillL2RealCutDomain_of_filled_not_gap q hq hr k hk1 E (Or.inr hE.1) hE.2
    exact ((hN E (mem_univ _)).div (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr E he)
      (hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr E he)).differentiableAt.differentiableWithinAt
  exact circleIntegral_eq_of_convex_cut_domain _ Ω K _ _ _ _ hΩ hconv hK
    (add_nonneg (hillRealGapContour_geometry 0 h0q h0r k hk1).1
      (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1.le)
    (add_nonneg (hillRealGapContour_geometry q hq hr k hk1).1
      (hillRealGapContour_geometry q hq hr k hk1).2.1.le)
    hball₀ hball₁ (hillRealGap_mem_high_free_contour_ball_of_control h0q h0r Ncut hNcut B D hc q hq hr hp k hk)
    (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk1) hf


theorem hillHighAbelianComplexPeriod_eq_intrinsic_physical
    (Ncut : ℕ) (hNcut : 1 ≤ Ncut) (B D : ℝ) (hc : HillComplexTailPeriodControl h0q h0r Ncut B D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B) (n k : ℕ) (hk : Ncut ≤ k) (a : Coeff 2) :
    hillAbelianComplexPeriod 0 h0q h0r n k (a,SpectralWeight.one.toCoeff q) =
      (2*(Real.pi:ℂ))⁻¹ * ∮ E in C((hillRealGapCenter q hq hr k : ℂ),
        hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
        hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct q hq hr E := by
  have hk1 : 1 ≤ k := hNcut.trans hk
  have hN : AnalyticOnNhd ℂ (fun E => hillAbelianHilbertPsi n (E,a)) univ := by
    intro E _
    exact (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).comp
      (f := fun E : ℂ => (E,a)) (analyticAt_id.prod analyticAt_const)
  unfold hillAbelianComplexPeriod
  congr 1
  calc
    _ = ∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
      hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct q hq hr E := by
        apply circleIntegral.integral_congr
          (add_nonneg (hillRealGapContour_geometry 0 h0q h0r k hk1).1
            (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1.le)
        intro E hE
        dsimp only []
        rw [(hillHighFreeGapContour_physical_root_matching h0q h0r Ncut hNcut B D hc q hq hr hp k hk E hE).2]
    _ = _ := hillHighPhysicalContour_period_eq_free_contour h0q h0r Ncut hNcut B D hc q hq hr hp k hk _ hN

end NLS.KdV
