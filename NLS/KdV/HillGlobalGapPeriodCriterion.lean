import NLS.KdV.HillFilledGapCutDomain
import NLS.KdV.HillGapBoxNumeratorReality
import NLS.ComplexAnalysis.RealGapZeroPeriod

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillIntrinsicContour_enlarged_disc_in_filledDomain (n : ℕ) (hn : 1 ≤ n) :
    ∃ R : ℝ, hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n < R ∧
      closedBall (hillRealGapCenter q hq hr n : ℂ) R ⊆ hillGapFilledDomain q hq hr n := by
  let c := hillRealGapCenter q hq hr n
  let r := hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n
  have hb := hillRealGapContour_band_bounds q hq hr n hn
  have hm : r < min (c-hillRealLabels q hq hr (2*n-2)) (hillRealLabels q hq hr (2*n+1)-c) :=
    lt_min (by linarith [hb.1]) (by linarith [hb.2])
  obtain ⟨R,hrR,hR⟩ := exists_between hm
  refine ⟨R,hrR,?_⟩
  intro z hz
  have hd : ‖z-(c:ℂ)‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hre := abs_le.mp ((abs_re_le_norm (z-(c:ℂ))).trans hd)
  simp only [Complex.sub_re,Complex.ofReal_re] at hre
  have hmR := lt_min_iff.mp hR
  exact Or.inr ⟨by linarith [hre.1,hmR.1],by linarith [hre.2,hmR.2]⟩

theorem exists_zero_on_hillRealGap_of_intrinsic_period_zero
    (N : ℂ → ℂ) (hN : AnalyticOnNhd ℂ N univ) (k : ℕ) (hk : 1 ≤ k)
    (hrealN : ∀ x ∈ Icc (hillRealLabels q hq hr (2*k-1)) (hillRealLabels q hq hr (2*k)),
      (N (x:ℂ)).im = 0)
    (hperiod : (2*(Real.pi:ℂ))⁻¹ * ∮ E in C((hillRealGapCenter q hq hr k : ℂ),
      hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      N E/hillEnergyCanonicalRootProduct q hq hr E = 0) :
    ∃ E ∈ segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ),
      N E = 0 := by
  let c := (hillRealGapCenter q hq hr k : ℂ)
  let r := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  let U := hillDeflatedEnergyCanonicalRoot q hq hr k
  have hrad : 0 < r := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1
  obtain ⟨R,hrR,hR⟩ := exists_hillIntrinsicContour_enlarged_disc_in_filledDomain q hq hr k hk
  have hNdisc : AnalyticOnNhd ℂ N (closedBall c R) := hN.mono (subset_univ _)
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
    dsimp only [U]
    rw [he]
    exact im_I_mul_div_hillDeflatedEnergyCanonicalRoot_eq_zero_on_gap q hq hr k hk E.re hx
      _ (hrealN E.re hx)
  have hcoef : (2*(Real.pi:ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hpzero := (mul_eq_zero.mp hperiod).resolve_left hcoef
  have hphysical : (∮ E in C(c,r), N E/(endpointRoot
      (hillRealLabels q hq hr (2*k-1)) (hillRealLabels q hq hr (2*k)) E*U E)) = 0 := by
    simpa only [U,hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated q hq hr k hk] using hpzero
  exact exists_segment_zero_of_deflated_root_period N U
    (hillRealLabels q hq hr (2*k-1)) (hillRealLabels q hq hr (2*k)) c Complex.I r R
    (by norm_num) hrad hrR (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk)
    hNdisc hU hUne hphysical hreal

theorem exists_hillAbelianPsiCandidate_zero_of_intrinsic_period_zero
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n k : ℕ) (hk : 1 ≤ k)
    (hperiod : hillAbelianCandidatePeriod q hq hr roots n k = 0) :
    ∃ E ∈ segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ),
      hillAbelianPsiCandidate roots n E = 0 := by
  exact exists_zero_on_hillRealGap_of_intrinsic_period_zero q hq hr
    (hillAbelianPsiCandidate roots n) (analyticOnNhd_hillAbelianPsiCandidate q hq hr roots hroots n)
    k hk (fun x _ => hillAbelianPsiCandidate_im_eq_zero q hq hr roots hroots n x) hperiod

end NLS.KdV
