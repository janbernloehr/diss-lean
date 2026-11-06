import NLS.KdV.HillWeightedDirichletDiagonal
import NLS.KdV.HillComplexWeightedEmbedding

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The actual high Dirichlet root evaluated in the original equal-diagonal
Schur operator, in the source's native period-one coefficient convention. -/
def hillNativeComplexDirichletDefect (w : SpectralWeight) (n : ℕ)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : ℂ :=
  (hillReducedFamily w n (hillPeriodOnePotential w q,
    hillScaledDirichletRoot h0q h0r (1/16) n (hillPeriodOneCoefficientMap w q)) (1,0)).1

/-- A genuinely weighted bound for the actual complex Dirichlet Schur
diagonal. The Fourier indices, weight, quartic-tail precursor and uniform
cutoff retain the period-one source normalization. -/
theorem exists_hillNativeComplexDirichletDefect_weighted_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ w : SpectralWeight,
      ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖ ≤ B → ∀ n : ℕ, N ≤ n →
      w (2*(n : ℤ))*‖hillNativeComplexDirichletDefect h0q h0r w n q‖ ≤
        (2*B+4)*(w (2*(n : ℤ))*‖q.val n‖+w (2*(n : ℤ))*‖q.val (-(n : ℤ))‖+
          16*‖q‖^2/(n : ℝ)) := by
  obtain ⟨N,hN,hN8,hweighted⟩ := exists_hillDirichlet_weighted_diagonal_bound B hB
  obtain ⟨M,hM,hshift⟩ := exists_hillScaledDirichletRoot_energy_displacement_bound h0q h0r B
  obtain ⟨L,hL,hchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart
    h0q h0r (1/16) (by norm_num) (by norm_num) B
  refine ⟨max N (max M L),hN.trans (le_max_left _ _),?_⟩
  intro w q hq n hn
  have hnN : N ≤ n := (le_max_left N (max M L)).trans hn
  have hnM : M ≤ n := (le_max_left M L).trans ((le_max_right N (max M L)).trans hn)
  have hnL : L ≤ n := (le_max_right M L).trans ((le_max_right N (max M L)).trans hn)
  have hn1 : 1 ≤ n := hN.trans hnN
  let Q := hillPeriodOnePotential w q
  let p := hillPeriodOneCoefficientMap w q
  let E := hillScaledDirichletRoot h0q h0r (1/16) n p
  have hpB : ‖p‖ ≤ B := (norm_hillPeriodOneCoefficientMap_le w q).trans hq
  obtain ⟨hball,hzero,_⟩ := (hchart n hnL).2 p hpB
  have hz : E ∈ reducedHillStrip n := by
    apply hillFreeGap_smallClosedBall_subset_reducedStrip h0q h0r n hn1
    rw [mem_closedBall]
    calc
      _ ≤ (1/16)*(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n) :=
        (show dist E (hillRealGapCenter 0 h0q h0r n : ℂ) < _ from hball).le
      _ = _ := by ring
  have hnear : ‖E-(freeHillValue n : ℂ)‖ ≤ 24*(Real.exp (1/2))^2*B :=
    (hshift p hpB n hnM).trans (mul_le_mul_of_nonneg_left hpB (by positivity))
  have hQB : ‖Q‖ ≤ B := by simpa only [Q,norm_hillPeriodOnePotential] using hq
  have hc : 8*‖Q‖ ≤ (n : ℝ) := (mul_le_mul_of_nonneg_left hQB (by norm_num : (0 : ℝ) ≤ 8)).trans
    (hN8.trans (by exact_mod_cast hnN))
  have hpar : w.toCoeff Q ∈ Coeff.paritySubspace 0 := by
    rw [show Q=hillPeriodOnePotential w q from rfl,toCoeff_hillPeriodOnePotential]
    exact Coeff.periodDouble_mem _
  have hd : hillNativeComplexDirichletDefect h0q h0r w n q =
      E-(freeHillValue n : ℂ)-hillDiagonal w Q n hn1 E hz hc := by
    change (hillReducedFamily w n (Q,E) (1,0)).1 = _
    rw [hillReducedFamily_eq w n hn1 (Q,E) hz hc,hillReducedOperator_apply]
    simp only [mul_one,mul_zero,sub_zero]
  have hb := hweighted w Q hQB hpar n hnN hn1 E hz hzero hnear hc
  rw [hd]
  simpa only [Q,hillPeriodOnePotential_even,show -(2*(n : ℤ))=2*(-(n : ℤ)) by ring,
    norm_hillPeriodOnePotential] using hb

/-- The same original Dirichlet defect has a common complex analytic chart
on every bounded native weighted source ball. -/
theorem exists_hillNativeComplexDirichletDefect_common_analytic (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ w : SpectralWeight, ∀ n : ℕ, N ≤ n →
      AnalyticOnNhd ℂ (hillNativeComplexDirichletDefect h0q h0r w n)
        (ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) := by
  obtain ⟨N,hN,hchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart
    h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨M,hM⟩ := exists_nat_gt (8*B)
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro w n hn q hq
  have hnN : N ≤ n := (le_max_left N M).trans hn
  have hn1 : 1 ≤ n := hN.trans hnN
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hqB : ‖q‖ < B := by simpa only [mem_ball,dist_zero_right] using hq
  let Q := hillPeriodOnePotential w q
  let p := hillPeriodOneCoefficientMap w q
  let E := hillScaledDirichletRoot h0q h0r (1/16) n p
  have hpball : p ∈ ball (0 : Coeff 2) B := by
    rw [mem_ball,dist_zero_right]
    exact (norm_hillPeriodOneCoefficientMap_le w q).trans_lt hqB
  have hpB : ‖p‖ ≤ B := (norm_hillPeriodOneCoefficientMap_le w q).trans hqB.le
  have hc : 8*‖Q‖ ≤ (n : ℝ) := by
    have hBn : 8*B ≤ (n : ℝ) := hM.le.trans (by exact_mod_cast (le_max_right N M).trans hn)
    rw [show Q=hillPeriodOnePotential w q from rfl,norm_hillPeriodOnePotential]
    linarith
  have hball := ((hchart n hnN).2 p hpB).1
  have hrad : (1/16)*(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n) ≤ (n : ℝ) := by
    rw [hillFreeGapHalfLength h0q h0r n hn1,hillFreeGapCollar h0q h0r n hn1,zero_add]
    have hpi : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_pos,Real.pi_lt_four]
    have hh := mul_le_mul_of_nonneg_left hpi (by linarith : (0 : ℝ) ≤ 2*(n : ℝ)-1)
    nlinarith
  have hclose : ‖E-(freeHillValue n : ℂ)‖ < (n : ℝ) := by
    have hh : ‖E-(freeHillValue n : ℂ)‖ <
        (1/16)*(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n) := by
      simpa only [mem_ball,dist_eq_norm,hillFreeGapCenter h0q h0r n hn1] using hball
    exact hh.trans_le hrad
  have hopen : E ∈ openHillStrip n := by
    have hh := abs_re_le_norm (E-(freeHillValue n : ℂ))
    simp only [sub_re,ofReal_re] at hh
    exact hh.trans_lt (hclose.trans_le (by linarith : (n : ℝ) ≤ 6*(n : ℝ)))
  have hE := ((hchart n hnN).1 p hpball).comp (f := hillPeriodOneCoefficientMap w)
    ((hillPeriodOneCoefficientMap w).analyticAt q)
  have hQ := (hillPeriodOnePotential w).toContinuousLinearMap.analyticAt q
  have hR := (analyticAt_hillReducedFamily w n hn1 (Q,E) hopen hc).comp
    (f := fun a => (hillPeriodOnePotential w a,
      hillScaledDirichletRoot h0q h0r (1/16) n (hillPeriodOneCoefficientMap w a))) (hQ.prod hE)
  have hev := ((ContinuousLinearMap.apply ℂ (ℂ × ℂ) ((1,0) : ℂ × ℂ)).analyticAt _).comp hR
  exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).comp hev

end NLS.KdV
