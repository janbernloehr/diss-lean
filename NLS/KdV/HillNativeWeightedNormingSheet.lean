import NLS.KdV.HillNativeDirichletJump
import NLS.KdV.HillDirichletSheetJump
import NLS.KdV.HillFilledRootIndexInverseBound
import NLS.KdV.HillComplexDirichletTerminal

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The original scaled norming sheet, in the source's native convention. -/
def hillNativeComplexDirichletGapTerminal (w : SpectralWeight) (n : ℕ)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : ℂ :=
  hillComplexDirichletGapTerminal h0q h0r n (hillPeriodOneCoefficientMap w q)

/-- The actual scaled Dirichlet norming sheet has a genuine weighted
Fourier estimate on each bounded complex source ball. -/
theorem exists_hillNativeComplexDirichletGapTerminal_weighted_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, 1≤N ∧ ∀ w : SpectralWeight,
      ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖≤B → ∀ n : ℕ, N≤n →
      w (2*(n : ℤ))*‖hillNativeComplexDirichletGapTerminal h0q h0r w n q‖ ≤
        C*(w (2*(n : ℤ))*‖q.val n‖+w (2*(n : ℤ))*‖q.val (-(n : ℤ))‖+
          16*‖q‖^2/(n : ℝ)) := by
  obtain ⟨Cf,hCf,hinverse⟩ := exists_hillFilledFreeGapRoot_index_inverse_bound h0q h0r
  obtain ⟨Ni,hNi,hinv⟩ := hinverse B
  obtain ⟨Nj,hNj,hjump⟩ := exists_hillNativeComplexDirichletJump_weighted_bound h0q h0r B hB
  obtain ⟨Ns,hNs,hsmall⟩ := exists_hillNativeComplexDirichletJump_uniform_small h0q h0r B hB
  obtain ⟨Nm,hNm,hchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart
    h0q h0r (1/16) (by norm_num) (by norm_num) B
  let A : ℝ := 8*Real.exp (1/2)*(2*B+5)
  refine ⟨5*Cf*A,by dsimp only [A];positivity,
    max Ni (max Nj (max Ns Nm)),hNi.trans (le_max_left _ _),?_⟩
  intro w q hq n hn
  have hnI : Ni≤n := (le_max_left _ _).trans hn
  have hnJ : Nj≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnS : Ns≤n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnM : Nm≤n := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hn1 : 1≤n := hNi.trans hnI
  let p := hillPeriodOneCoefficientMap w q
  let E := hillScaledDirichletRoot h0q h0r (1/16) n p
  let J := hillNativeComplexDirichletJump h0q h0r w n q
  let W := w (2*(n : ℤ))
  let T := W*‖q.val n‖+W*‖q.val (-(n : ℤ))‖+16*‖q‖^2/(n : ℝ)
  have hW : 0≤W := (w.positive _).le
  have hpB : ‖p‖≤B := (norm_hillPeriodOneCoefficientMap_le w q).trans hq
  obtain ⟨hball,hzero,_⟩ := (hchart n hnM).2 p hpB
  have hR : 0≤hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n := by
    have hh := hillRealGapContour_geometry 0 h0q h0r n hn1
    linarith [hh.1,hh.2.1]
  have hE : E ∈ closedBall (hillRealGapCenter 0 h0q h0r n : ℂ)
      (hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n) :=
    closedBall_subset_closedBall (by linarith : (1/16)*(hillRealGapHalfLength 0 h0q h0r n+
      hillRealGapCollar 0 h0q h0r n)≤hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n)
      (ball_subset_closedBall hball)
  have hi := hinv p hpB n hnI E hE
  have hs : ‖hillDirichletSheetRoot p E‖≤5*‖J‖ :=
    norm_hillDirichletSheetRoot_le_five_jump p E hzero n (hsmall w q hq n hnS)
  have hj : (n : ℝ)*W*‖J‖≤A*T := hjump w q hq n hnJ
  change W*‖hillDirichletSheetRoot p E/hillFilledFreeGapRoot h0q h0r n (E,p)‖≤_
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ W*((5*‖J‖)*(Cf*(n : ℝ))) := by gcongr
    _ = 5*Cf*((n : ℝ)*W*‖J‖) := by ring
    _ ≤ 5*Cf*(A*T) := mul_le_mul_of_nonneg_left hj (by positivity)
    _ = _ := by dsimp only [T,W];ring

/-- The same original scaled sheet has a common scalar complex analytic chart. -/
theorem exists_hillNativeComplexDirichletGapTerminal_common_analytic (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ w : SpectralWeight, ∀ n : ℕ, N≤n →
      AnalyticOnNhd ℂ (hillNativeComplexDirichletGapTerminal h0q h0r w n)
        (ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) := by
  obtain ⟨N,hN,hchart⟩ := exists_hillComplexDirichletGapTerminal_analytic_bound h0q h0r B
  refine ⟨N,hN,?_⟩
  intro w n hn q hq
  have hp : hillPeriodOneCoefficientMap w q ∈ ball (0 : Coeff 2) B := by
    rw [mem_ball,dist_zero_right]
    exact (norm_hillPeriodOneCoefficientMap_le w q).trans_lt
      (show ‖q‖<B by simpa only [mem_ball,dist_zero_right] using hq)
  exact ((hchart n hn).1 _ hp).comp ((hillPeriodOneCoefficientMap w).analyticAt q)

end NLS.KdV
