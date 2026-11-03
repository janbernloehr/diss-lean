import NLS.KdV.HillFreeContourPhysicalBandBounds
import NLS.KdV.HillDeflatedCanonicalRootPhase
import NLS.KdV.HillHilbertNumeratorReality
import NLS.ComplexAnalysis.RealGapZeroPeriod

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillAbelianHilbertPsi_zero_on_physical_gap_of_period_zero
    (ε D : ℝ) (hc : HillComplexPeriodControl h0q h0r ε D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ ε) (n k : ℕ) (hk : 1 ≤ k)
    (a : Coeff 2) (ha : star a = a)
    (hperiod : hillAbelianComplexPeriod 0 h0q h0r n k (a,SpectralWeight.one.toCoeff q) = 0) :
    ∃ E ∈ segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ)
        (hillRealLabels q hq hr (2*k) : ℂ), hillAbelianHilbertPsi n (E,a) = 0 := by
  let c := (hillRealGapCenter 0 h0q h0r k : ℂ)
  let r := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let N : ℂ → ℂ := fun E => hillAbelianHilbertPsi n (E,a)
  let U := hillDeflatedEnergyCanonicalRoot q hq hr k
  have hrad : 0 < r := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  obtain ⟨R,hrR,hR⟩ := exists_hillFreeContour_enlarged_disc_in_filledDomain
    h0q h0r ε D hc q hq hr hp k hk
  have hgap := hillRealGap_mem_free_contour_ball_of_control h0q h0r ε D hc q hq hr hp k hk
  have hN : AnalyticOnNhd ℂ N (closedBall c R) := by
    intro E _
    exact (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).comp
      (f := fun E : ℂ => (E,a)) (analyticAt_id.prod analyticAt_const)
  have hU : AnalyticOnNhd ℂ U (closedBall c R) :=
    (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k).mono hR
  have hUne : ∀ E ∈ closedBall c R, U E ≠ 0 :=
    fun E hE => hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk E (hR hE)
  have hreal : ∀ E ∈ segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ)
      (hillRealLabels q hq hr (2*k) : ℂ), (Complex.I*(N E/U E)).im = 0 := by
    intro E hE
    have hEi := im_eq_zero_of_mem_real_segment _ _ E hE
    have he : E = (E.re:ℂ) := by apply Complex.ext <;> simp [hEi]
    have hx := re_mem_Icc_of_mem_real_segment _ _
      (monotone_hillRealLabels q hq hr (by omega : 2*k-1 ≤ 2*k)) E hE
    dsimp only [N,U]
    rw [he]
    exact im_I_mul_div_hillDeflatedEnergyCanonicalRoot_eq_zero_on_gap q hq hr k hk E.re hx
      _ (hillAbelianHilbertPsi_im_eq_zero_of_real_roots n a ha E.re)
  have hcoef : (2*(Real.pi:ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero))
  unfold hillAbelianComplexPeriod at hperiod
  have hpzero := (mul_eq_zero.mp hperiod).resolve_left hcoef
  have hphysical : (∮ E in C(c,r), N E/(endpointRoot
      (hillRealLabels q hq hr (2*k-1)) (hillRealLabels q hq hr (2*k)) E*U E)) = 0 := by
    calc
      _ = ∮ E in C(c,r), N E/hillAbelianComplexRoot 0 h0q h0r (E,SpectralWeight.one.toCoeff q) := by
        apply circleIntegral.integral_congr hrad.le
        intro E hE
        dsimp only [U]
        rw [← hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated q hq hr k hk E,
          (hillFreeGapContour_physical_root_matching h0q h0r ε D hc q hq hr hp k hk E hE).2]
      _ = 0 := hpzero
  exact exists_segment_zero_of_deflated_root_period N U
    (hillRealLabels q hq hr (2*k-1)) (hillRealLabels q hq hr (2*k)) c Complex.I r R
    (by norm_num) hrad hrR hgap hN hU hUne hphysical hreal

end NLS.KdV
