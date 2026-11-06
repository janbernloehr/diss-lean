import NLS.KdV.HillWeightedDirichletJump
import NLS.KdV.HillComplexWeightedEmbedding

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.Fourier
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The original boundary derivative jump evaluated at the actual common
Dirichlet root in the native period-one convention. -/
def hillNativeComplexDirichletJump (w : SpectralWeight) (n : ℕ)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : ℂ :=
  hillL2DirichletBoundaryJump (hillPeriodOneCoefficientMap w q)
    (hillScaledDirichletRoot h0q h0r (1/16) n (hillPeriodOneCoefficientMap w q)) n

/-- A weighted Fourier estimate for the original boundary jump at the
actual common Dirichlet roots, retaining the native source normalization. -/
theorem exists_hillNativeComplexDirichletJump_weighted_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ w : SpectralWeight,
      ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖ ≤ B → ∀ n : ℕ, N ≤ n →
      (n : ℝ)*w (2*(n : ℤ))*‖hillNativeComplexDirichletJump h0q h0r w n q‖ ≤
        (8*Real.exp (1/2)*(2*B+5))*(w (2*(n : ℤ))*‖q.val n‖+w (2*(n : ℤ))*‖q.val (-(n : ℤ))‖+
          16*‖q‖^2/(n : ℝ)) := by
  obtain ⟨N,hN,hN8,hweighted⟩ := exists_hillDirichlet_boundary_jump_weighted_bound B hB
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
  have hpar : w.toCoeff Q ∈ Coeff.paritySubspace 0 := by
    rw [show Q=hillPeriodOnePotential w q from rfl,toCoeff_hillPeriodOnePotential]
    exact Coeff.periodDouble_mem _
  have hb := hweighted w Q hQB hpar n hnN E hz hzero hnear
  change (n : ℝ)*w (2*(n : ℤ))*‖hillL2DirichletBoundaryJump (w.toCoeff Q) E n‖ ≤ _
  simpa only [Q,hillPeriodOnePotential_even,show -(2*(n : ℤ))=2*(-(n : ℤ)) by ring,
    norm_hillPeriodOnePotential] using hb

/-- The original boundary jump has a common complex scalar analytic chart. -/
theorem exists_hillNativeComplexDirichletJump_common_analytic (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ w : SpectralWeight, ∀ n : ℕ, N ≤ n →
      AnalyticOnNhd ℂ (hillNativeComplexDirichletJump h0q h0r w n)
        (ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) := by
  obtain ⟨N,hN,hchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart
    h0q h0r (1/16) (by norm_num) (by norm_num) B
  refine ⟨N,hN,?_⟩
  intro w n hn q hq
  have hp : hillPeriodOneCoefficientMap w q ∈ ball (0 : Coeff 2) B := by
    rw [mem_ball,dist_zero_right]
    exact (norm_hillPeriodOneCoefficientMap_le w q).trans_lt
      (show ‖q‖ < B by simpa only [mem_ball,dist_zero_right] using hq)
  let p := hillPeriodOneCoefficientMap w q
  let E := hillScaledDirichletRoot h0q h0r (1/16) n p
  have hmu := ((hchart n hn).1 p hp).comp ((hillPeriodOneCoefficientMap w).analyticAt q)
  have hpair := hmu.prod ((hillPeriodOneCoefficientMap w).analyticAt q)
  have hs := (analyticOnNhd_hillL2DirichletSlope_joint (E,p) (mem_univ _)).comp
    (f := fun a => (hillScaledDirichletRoot h0q h0r (1/16) n (hillPeriodOneCoefficientMap w a),
      hillPeriodOneCoefficientMap w a)) hpair
  exact (AnalyticAt.mul hs analyticAt_const).sub analyticAt_const

/-- The actual original derivative jump is uniformly near its free value
at a common high cutoff, independently of the auxiliary weight. -/
theorem exists_hillNativeComplexDirichletJump_uniform_small (B : ℝ) (hB : 0 ≤ B) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ w : SpectralWeight,
      ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖ ≤ B → ∀ n : ℕ, N ≤ n →
      ‖hillNativeComplexDirichletJump h0q h0r w n q‖ ≤ 1/2 := by
  obtain ⟨N,hN,hjump⟩ := exists_hillNativeComplexDirichletJump_weighted_bound h0q h0r B hB
  let A : ℝ := 8*Real.exp (1/2)*(2*B+5)
  let K : ℝ := A*(2*B+16*B^2)
  have hA : 0 ≤ A := by dsimp only [A];positivity
  obtain ⟨M,hM⟩ := exists_nat_gt (2*K)
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro w q hq n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := hN.trans hnN
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  have hlarge : 2*K ≤ (n : ℝ) := hM.le.trans (by exact_mod_cast (le_max_right N M).trans hn)
  have hcoef (k : ℤ) : w (2*k)*‖q.val k‖ ≤ B := by
    have hh := (le_div_iff₀ (w.doubleIndex.toWeight.positive k)).mp
      (WeightedCoeff.norm_apply_le w.doubleIndex.toWeight 2 q k)
    simpa only [SpectralWeight.toWeight_apply,SpectralWeight.doubleIndex_apply,mul_comm] using hh.trans hq
  have hp := hcoef n
  have hm : w (2*(n : ℤ))*‖q.val (-(n : ℤ))‖ ≤ B := by
    simpa only [mul_neg,SpectralWeight.apply_neg] using hcoef (-(n : ℤ))
  have htail : 16*‖q‖^2/(n : ℝ) ≤ 16*B^2 := by
    exact (div_le_self (by positivity : 0 ≤ 16*‖q‖^2) hnR).trans
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg q) hB).mpr hq) (by norm_num))
  have hbound : (n : ℝ)*w (2*(n : ℤ))*‖hillNativeComplexDirichletJump h0q h0r w n q‖ ≤ K :=
    (hjump w q hq n hnN).trans (mul_le_mul_of_nonneg_left (by linarith :
      w (2*(n : ℤ))*‖q.val n‖+w (2*(n : ℤ))*‖q.val (-(n : ℤ))‖+16*‖q‖^2/(n : ℝ) ≤
        2*B+16*B^2) hA)
  have hweight : (n : ℝ)*‖hillNativeComplexDirichletJump h0q h0r w n q‖ ≤
      (n : ℝ)*w (2*(n : ℤ))*‖hillNativeComplexDirichletJump h0q h0r w n q‖ := by
    have hh := mul_le_mul_of_nonneg_right (w.one_le (2*(n : ℤ)))
      (mul_nonneg hnpos.le (norm_nonneg (hillNativeComplexDirichletJump h0q h0r w n q)))
    nlinarith only [hh]
  nlinarith

end NLS.KdV
