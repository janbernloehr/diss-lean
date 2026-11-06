import NLS.KdV.HillUniformComplexGapPairs
import NLS.KdV.HillAllGapSymmetricData
import NLS.KdV.HillHighFreeContourBandBounds
import NLS.KdV.HillLocalGapPhysicalMatching

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGap_bounded_complex_analytic_symmetric_data (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ, N ≤ k →
      AnalyticOnNhd ℂ (hillLocalGapMidpoint 0 h0q h0r k) (ball (0 : Coeff 2) B) ∧
      AnalyticOnNhd ℂ (hillLocalGapSquare 0 h0q h0r k) (ball (0 : Coeff 2) B) ∧
      ∀ p ∈ ball (0 : Coeff 2) B,
        (∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ) (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k), hillL2Radicand p E ≠ 0) ∧
        ∃ a ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ) (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        ∃ b ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ) (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
          hillL2Radicand p a = 0 ∧ hillL2Radicand p b = 0 ∧
          (∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ) (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
            analyticOrderNatAt (hillL2Radicand p) E = ({a,b} : Multiset ℂ).count E) ∧
          hillLocalGapMidpoint 0 h0q h0r k p = (a+b)/2 ∧ hillLocalGapSquare 0 h0q h0r k p = (b-a)^2 := by
  obtain ⟨N,hN,hpair⟩ := exists_hillFreeGapContour_bounded_complex_gap_pairs h0q h0r B
  refine ⟨N,hN,?_⟩
  intro k hk
  have hk1 := hN.trans hk
  have hR := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hpB (p : Coeff 2) (hp : p ∈ ball (0 : Coeff 2) B) : ‖p‖ ≤ B :=
    (show ‖p‖ < B by simpa only [mem_ball,dist_zero_right] using hp).le
  have hm (j : ℕ) := analyticOnNhd_logarithmicCircleMoment
    (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1) analyticOnNhd_hillL2Radicand_joint
    (hillRealGapCenter 0 h0q h0r k : ℂ)
    (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) hR.le j isOpen_ball
    (fun p hp => (hpair p (hpB p hp) k hk).1)
  refine ⟨(hm 1).div_const (c := 2),(analyticOnNhd_const.mul (hm 2)).sub ((hm 1).pow 2),?_⟩
  intro p hp
  obtain ⟨hboundary,a,ha,b,hb,haz,hbz,horders⟩ := hpair p (hpB p hp) k hk
  have hsymmetric := hillLocalGapSymmetricData_eq_of_pair 0 h0q h0r k hk1 p hboundary ha hb horders
  exact ⟨hboundary,a,ha,b,hb,haz,hbz,horders,hsymmetric⟩

theorem exists_hillFreeGap_bounded_real_symmetric_data_matching (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0,
      ∀ hr : IsRealHillPotential (SpectralWeight.one.toCoeff q), ‖SpectralWeight.one.toCoeff q‖ ≤ B →
        ∀ k : ℕ, N ≤ k →
          hillLocalGapMidpoint 0 h0q h0r k (SpectralWeight.one.toCoeff q) = (hillRealGapCenter q hq hr k : ℂ) ∧
          hillLocalGapSquare 0 h0q h0r k (SpectralWeight.one.toCoeff q) = (2*(hillRealGapHalfLength q hq hr k : ℂ))^2 := by
  obtain ⟨N,hN,D,hD,hcontrol⟩ := exists_hillComplexTailPeriodControl h0q h0r B
  refine ⟨N,hN,?_⟩
  intro q hq hr hp k hk
  exact hillLocalGapSymmetricData_eq_physical_of_geometry 0 h0q h0r q hq hr k (hN.trans hk)
    (hillHighFreeContour_physical_band_bounds_of_control h0q h0r N hN B D hcontrol q hq hr hp k hk)
    (hillRealGap_mem_high_free_contour_ball_of_control h0q h0r N hN B D hcontrol q hq hr hp k hk)

end NLS.KdV
