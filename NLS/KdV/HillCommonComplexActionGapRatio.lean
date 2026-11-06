import NLS.KdV.HillCommonComplexDeflatedTrace
import NLS.KdV.HillUniformComplexGapLocalization
import NLS.ComplexAnalysis.QuadraticGapActionRatioDisc

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillComplexActionGapRatio (k : ℕ) : Coeff 2 → ℂ :=
  quadraticGapActionRatio (hillComplexDeflatedTraceNumerator h0q h0r k)
    (hillLocalGapMidpoint 0 h0q h0r k) (fun p => hillLocalGapSquare 0 h0q h0r k p/4)

theorem exists_hillComplexActionGapRatio_common_analytic (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ k : ℕ, N≤k →
      AnalyticOnNhd ℂ (hillComplexActionGapRatio h0q h0r k) (ball (0 : Coeff 2) B) := by
  obtain ⟨Nh,hNh,hh⟩ := exists_hillComplexDeflatedTraceNumerator_common_analytic h0q h0r B
  obtain ⟨Ns,hNs,hs⟩ := exists_hillFreeGap_bounded_complex_analytic_symmetric_data h0q h0r B
  obtain ⟨Nl,hNl,hl⟩ := exists_hillFreeGap_bounded_complex_midpoint_halfgap_localization h0q h0r (1/16) (by norm_num) (by norm_num) B
  refine ⟨Nh+Ns+Nl,hNh.trans (by omega),?_⟩
  intro k hk p hp
  have hkh : Nh≤k := by omega
  have hks : Ns≤k := by omega
  have hkl : Nl≤k := by omega
  have hk1 := hNh.trans hkh
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let M := hillLocalGapMidpoint 0 h0q h0r k p
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hpB : ‖p‖≤B := (show ‖p‖<B by simpa only [mem_ball,dist_zero_right] using hp).le
  obtain ⟨hM,hS⟩ := hl p hpB k hkl
  apply analyticAt_quadraticGapActionRatio_of_disc _ _ _ p ((hs k hks).1 p hp) (((hs k hks).2.1 p hp).div_const)
    (R/4) (by dsimp only [R] at *;linarith)
  intro E hE
  apply hh k hkh (E,p) ⟨?_,hp⟩
  have hEM : ‖E-M‖≤R/4 := by simpa only [mem_closedBall,dist_eq_norm] using hE
  have htri := norm_sub_le_norm_sub_add_norm_sub E M c
  rw [mem_closedBall,dist_eq_norm]
  dsimp only [M,c,R] at *
  linarith

end NLS.KdV
