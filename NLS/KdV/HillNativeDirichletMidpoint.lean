import NLS.KdV.HillDirichletPeriodicDistance
import NLS.KdV.HillNativeDirichletDefect
import NLS.KdV.HillUniformComplexGapLocalization

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The actual periodic midpoint minus the actual Dirichlet root, in the
source's native period-one convention. -/
def hillNativeComplexDirichletMidpointDifference (w : SpectralWeight) (n : ℕ)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : ℂ :=
  hillLocalGapMidpoint 0 h0q h0r n (hillPeriodOneCoefficientMap w q)-
    hillScaledDirichletRoot h0q h0r (1/16) n (hillPeriodOneCoefficientMap w q)

/-- A common weighted Fourier bound for the original complex periodic
midpoint minus Dirichlet root, including collapsed periodic pairs. -/
theorem exists_hillNativeComplexDirichletMidpointDifference_weighted_bound
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ w : SpectralWeight,
      ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖ ≤ B → ∀ n : ℕ, N ≤ n →
      w (2*(n : ℤ))*‖hillNativeComplexDirichletMidpointDifference h0q h0r w n q‖ ≤
        (4*B+10)*(w (2*(n : ℤ))*‖q.val n‖+w (2*(n : ℤ))*‖q.val (-(n : ℤ))‖+
          16*‖q‖^2/(n : ℝ)) := by
  obtain ⟨Nd,hNd,hNd8,hbound⟩ := exists_hillDirichlet_periodic_distance_weighted_bound B hB
  obtain ⟨Ne,hNe,hshift⟩ := exists_hillScaledDirichletRoot_energy_displacement_bound h0q h0r B
  obtain ⟨Nr,hNr,hchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart
    h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨Np,hNp,hpairs⟩ := exists_hillFreeGap_bounded_complex_localized_pairs
    h0q h0r (1/16) (by norm_num) (by norm_num) B
  refine ⟨max Nd (max Ne (max Nr Np)),hNd.trans (le_max_left _ _),?_⟩
  intro w q hq n hn
  have hnD : Nd ≤ n := (le_max_left _ _).trans hn
  have hnE : Ne ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnR : Nr ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnP : Np ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hn1 : 1 ≤ n := hNd.trans hnD
  let Q := hillPeriodOnePotential w q
  let p := hillPeriodOneCoefficientMap w q
  let E := hillScaledDirichletRoot h0q h0r (1/16) n p
  let c : ℂ := hillRealGapCenter 0 h0q h0r n
  let R := hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n
  have hR : 0 < R := add_pos_of_nonneg_of_pos
    (hillRealGapContour_geometry 0 h0q h0r n hn1).1 (hillRealGapContour_geometry 0 h0q h0r n hn1).2.1
  have hpB : ‖p‖ ≤ B := (norm_hillPeriodOneCoefficientMap_le w q).trans hq
  have hQB : ‖Q‖ ≤ B := by simpa only [Q,norm_hillPeriodOnePotential] using hq
  have hc : 8*‖Q‖ ≤ (n : ℝ) := (mul_le_mul_of_nonneg_left hQB (by norm_num : (0 : ℝ) ≤ 8)).trans
    (hNd8.trans (by exact_mod_cast hnD))
  have hpar : w.toCoeff Q ∈ Coeff.paritySubspace 0 := by
    rw [show Q=hillPeriodOnePotential w q from rfl,toCoeff_hillPeriodOnePotential]
    exact Coeff.periodDouble_mem _
  obtain ⟨hEball,hzero,_⟩ := (hchart n hnR).2 p hpB
  have hsmall (z : ℂ) (hz : z ∈ ball c ((1/16)*R)) : z ∈ reducedHillStrip n := by
    apply hillFreeGap_smallClosedBall_subset_reducedStrip h0q h0r n hn1
    rw [mem_closedBall]
    calc
      _ ≤ (1/16)*R := (show dist z c < _ from hz).le
      _ = _ := by dsimp only [R]; ring
  have hE : E ∈ reducedHillStrip n := hsmall E hEball
  have hnear : ‖E-(freeHillValue n : ℂ)‖ ≤ 24*(Real.exp (1/2))^2*B :=
    (hshift p hpB n hnE).trans (mul_le_mul_of_nonneg_left hpB (by positivity))
  obtain ⟨hb,a,ha,b,hb',haz,hbz,horders⟩ := hpairs p hpB n hnP
  have haR : a ∈ ball c R := ball_subset_ball (mul_le_of_le_one_left hR.le (by norm_num : (1/16 : ℝ) ≤ 1)) ha
  have hbR : b ∈ ball c R := ball_subset_ball (mul_le_of_le_one_left hR.le (by norm_num : (1/16 : ℝ) ≤ 1)) hb'
  have hM := (hillLocalGapSymmetricData_eq_of_pair 0 h0q h0r n hn1 p hb haR hbR horders).1
  have hroot (z : ℂ) (hz : z ∈ reducedHillStrip n) (hzero : hillL2Radicand p z=0) :
      hillReducedDeterminant w n (Q,z)=0 := by
    apply (hillReduced_weighted_zero_iff_l2Discriminant w Q hpar n hn1 z hz hc).mpr
    exact sub_eq_zero.mp hzero
  have had := hbound w Q hQB hpar n hnD E a hE (hsmall a ha) hzero hnear (hroot a (hsmall a ha) haz)
  have hbd := hbound w Q hQB hpar n hnD E b hE (hsmall b hb') hzero hnear (hroot b (hsmall b hb') hbz)
  have hmid : ‖(a+b)/2-E‖ ≤ (‖a-E‖+‖b-E‖)/2 := by
    rw [show (a+b)/2-E=((a-E)+(b-E))/2 by ring,norm_div]
    norm_num only [norm_ofNat]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hmid (w.positive (2*(n : ℤ))).le
  change w (2*(n : ℤ))*‖hillLocalGapMidpoint 0 h0q h0r n p-E‖ ≤ _
  rw [hM]
  have hfinal : w (2*(n : ℤ))*‖(a+b)/2-E‖ ≤
      (4*B+10)*(w (2*(n : ℤ))*‖Q.val (2*(n : ℤ))‖+
        w (2*(n : ℤ))*‖Q.val (-(2*(n : ℤ)))‖+16*‖Q‖^2/(n : ℝ)) := by
    nlinarith only [hm,had,hbd]
  simpa only [Q,hillPeriodOnePotential_even,show -(2*(n : ℤ))=2*(-(n : ℤ)) by ring,
    norm_hillPeriodOnePotential] using hfinal

/-- The actual midpoint difference has a common complex scalar analytic
chart on each bounded native weighted source ball. -/
theorem exists_hillNativeComplexDirichletMidpointDifference_common_analytic (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ w : SpectralWeight, ∀ n : ℕ, N ≤ n →
      AnalyticOnNhd ℂ (hillNativeComplexDirichletMidpointDifference h0q h0r w n)
        (ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) := by
  obtain ⟨Nm,hNm,hmid⟩ := exists_hillFreeGap_bounded_complex_analytic_symmetric_data h0q h0r B
  obtain ⟨Nd,hNd,hdir⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart
    h0q h0r (1/16) (by norm_num) (by norm_num) B
  refine ⟨max Nm Nd,hNm.trans (le_max_left _ _),?_⟩
  intro w n hn q hq
  have hnM : Nm ≤ n := (le_max_left _ _).trans hn
  have hnD : Nd ≤ n := (le_max_right _ _).trans hn
  have hp : hillPeriodOneCoefficientMap w q ∈ ball (0 : Coeff 2) B := by
    rw [mem_ball,dist_zero_right]
    exact (norm_hillPeriodOneCoefficientMap_le w q).trans_lt
      (show ‖q‖ < B by simpa only [mem_ball,dist_zero_right] using hq)
  exact (((hmid n hnM).1 _ hp).comp ((hillPeriodOneCoefficientMap w).analyticAt q)).sub
    (((hdir n hnD).1 _ hp).comp ((hillPeriodOneCoefficientMap w).analyticAt q))

end NLS.KdV
