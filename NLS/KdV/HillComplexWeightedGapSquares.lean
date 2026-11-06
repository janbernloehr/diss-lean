import NLS.KdV.HillComplexWeightedEmbedding
import NLS.KdV.HillLocalizedComplexGapPairs
import NLS.KdV.HillUniformComplexGapData

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillNativeComplexGapSquare (w : SpectralWeight) (n : ℕ)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : ℂ :=
  hillLocalGapSquare 0 h0q h0r n (hillPeriodOneCoefficientMap w q)

theorem exists_hillNativeComplexGapSquare_common_analytic (w : SpectralWeight) (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ n : ℕ, N≤n →
      AnalyticOnNhd ℂ (hillNativeComplexGapSquare h0q h0r w n)
        (ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) := by
  obtain ⟨N,hN,ha⟩ := exists_hillFreeGap_bounded_complex_analytic_symmetric_data h0q h0r B
  refine ⟨N,hN,?_⟩
  intro n hn q hq
  have hqB : hillPeriodOneCoefficientMap w q∈ball (0 : Coeff 2) B := by
    rw [mem_ball,dist_zero_right]
    exact (norm_hillPeriodOneCoefficientMap_le w q).trans_lt (by simpa only [mem_ball,dist_zero_right] using hq)
  exact ((ha n hn).2.1 _ hqB).comp (f := hillPeriodOneCoefficientMap w)
    ((hillPeriodOneCoefficientMap w).analyticAt q)

theorem exists_hillNativeComplexGapSquare_weighted_pointwise_bound (w : SpectralWeight) (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖≤B →
      ∀ n : ℕ, N≤n → 8*‖q‖≤(n:ℝ) →
        (w (2*(n:ℤ)))^2*‖hillNativeComplexGapSquare h0q h0r w n q‖ ≤
          9*((w (2*(n:ℤ)))^2*‖q.val n‖^2+(w (2*(n:ℤ)))^2*‖q.val (-(n:ℤ))‖^2)+
            1152*‖q‖^4/(n:ℝ)^2 := by
  obtain ⟨N,hN,hpairs⟩ := exists_hillFreeGap_bounded_complex_localized_pairs h0q h0r (1/16) (by norm_num) (by norm_num) B
  refine ⟨N,hN,?_⟩
  intro q hq n hn hcut
  have hn1 := hN.trans hn
  let p := hillPeriodOneCoefficientMap w q
  have hp : ‖p‖≤B := (norm_hillPeriodOneCoefficientMap_le w q).trans hq
  let c : ℂ := hillRealGapCenter 0 h0q h0r n
  let R := hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r n hn1).1
    (hillRealGapContour_geometry 0 h0q h0r n hn1).2.1
  obtain ⟨hboundary,a,ha,b,hb,haz,hbz,horders⟩ := hpairs p hp n hn
  have haK : a∈closedBall c (R/16) := by
    rw [show R/16=(1/16)*R by ring]
    exact ball_subset_closedBall ha
  have hbK : b∈closedBall c (R/16) := by
    rw [show R/16=(1/16)*R by ring]
    exact ball_subset_closedBall hb
  have has := hillFreeGap_smallClosedBall_subset_reducedStrip h0q h0r n hn1 haK
  have hbs := hillFreeGap_smallClosedBall_subset_reducedStrip h0q h0r n hn1 hbK
  have haB : a∈ball c R := ball_subset_ball (by linarith : (1/16)*R≤R) ha
  have hbB : b∈ball c R := ball_subset_ball (by linarith : (1/16)*R≤R) hb
  have hS := (hillLocalGapSymmetricData_eq_of_pair 0 h0q h0r n hn1 p hboundary haB hbB horders).2
  have hpar : w.toCoeff (hillPeriodOnePotential w q)∈Coeff.paritySubspace 0 := by
    rw [toCoeff_hillPeriodOnePotential]
    exact Coeff.periodDouble_mem _
  have hc : 8*‖hillPeriodOnePotential w q‖≤(n:ℝ) := by simpa only [norm_hillPeriodOnePotential] using hcut
  have hza : hillL2Discriminant (w.toCoeff (hillPeriodOnePotential w q)) a^2=4 := by
    exact sub_eq_zero.mp haz
  have hzb : hillL2Discriminant (w.toCoeff (hillPeriodOnePotential w q)) b^2=4 := by
    exact sub_eq_zero.mp hbz
  have hda := (hillReduced_weighted_zero_iff_l2Discriminant w _ hpar n hn1 a has hc).mpr hza
  have hdb := (hillReduced_weighted_zero_iff_l2Discriminant w _ hpar n hn1 b hbs hc).mpr hzb
  have he : ‖hillNativeComplexGapSquare h0q h0r w n q‖=‖a-b‖^2 := by
    rw [hillNativeComplexGapSquare,hS,norm_pow,norm_sub_rev]
  rw [he]
  exact hillPeriodOne_roots_weighted_separation w q n hn1 hcut a b has hbs hda hdb

end NLS.KdV
