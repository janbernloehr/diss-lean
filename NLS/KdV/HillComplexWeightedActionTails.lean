import NLS.KdV.HillComplexGapActions
import NLS.KdV.HillComplexWeightedGapTails
import NLS.KdV.HillUniformComplexActionRatioBounds
import NLS.KdV.HillWeightedActionContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillNativeComplexWeightedActionTerm (w : SpectralWeight) (n : ℕ)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : ℂ :=
  (((w (2*(n:ℤ)))^2*(2*Real.pi*(n:ℝ)):ℝ):ℂ)*
    hillComplexGapAction h0q h0r n (hillPeriodOneCoefficientMap w q)

theorem hillNativeComplexWeightedActionTerm_zero (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : hillNativeComplexWeightedActionTerm h0q h0r w 0 q=0 := by
  simp only [hillNativeComplexWeightedActionTerm,Nat.cast_zero,mul_zero,ofReal_zero,zero_mul]

theorem exists_hillNativeComplexWeightedActionTerm_common_analytic (w : SpectralWeight) (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ n : ℕ, N≤n →
      AnalyticOnNhd ℂ (hillNativeComplexWeightedActionTerm h0q h0r w n)
        (ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) := by
  obtain ⟨N,hN,ha⟩ := exists_hillComplexGapAction_common_analytic h0q h0r B
  refine ⟨N,hN,?_⟩
  intro n hn q hq
  have hp : hillPeriodOneCoefficientMap w q∈ball (0 : Coeff 2) B := by
    rw [mem_ball,dist_zero_right]
    exact (norm_hillPeriodOneCoefficientMap_le w q).trans_lt (by simpa only [mem_ball,dist_zero_right] using hq)
  exact analyticAt_const.mul ((ha n hn _ hp).comp (f := hillPeriodOneCoefficientMap w)
    ((hillPeriodOneCoefficientMap w).analyticAt q))

theorem norm_hillNativeComplexWeightedActionTerm_le (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) (n : ℕ) (hn : 1≤n) (C : ℝ)
    (hr : ‖hillComplexActionGapRatio h0q h0r n (hillPeriodOneCoefficientMap w q)‖≤C/(n:ℝ)) :
    ‖hillNativeComplexWeightedActionTerm h0q h0r w n q‖≤
      (Real.pi*C/2)*((w (2*(n:ℤ)))^2*‖hillNativeComplexGapSquare h0q h0r w n q‖) := by
  have hnpos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  let A := (w (2*(n:ℤ)))^2*(2*Real.pi*(n:ℝ))
  have hA : 0≤A := by dsimp only [A];positivity
  change ‖(A:ℂ)*(hillComplexActionGapRatio h0q h0r n (hillPeriodOneCoefficientMap w q)*
      (hillLocalGapSquare 0 h0q h0r n (hillPeriodOneCoefficientMap w q)/4))‖≤_
  rw [norm_mul,norm_real,Real.norm_eq_abs,abs_of_nonneg hA,norm_mul,norm_div,norm_ofNat]
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr (by positivity)) hA).trans_eq
    (by dsimp only [A,hillNativeComplexGapSquare];field_simp;ring)

theorem exists_hillNativeComplexWeightedActionTerm_uniform_tail_bound :
    ∃ C : ℝ, 0<C ∧ ∀ w : SpectralWeight, ∀ B : ℝ, ∃ N0 : ℕ, 1≤N0 ∧
      ∀ N : ℕ, N0≤N → ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖≤B →
        Summable (fun k : ℕ => ‖hillNativeComplexWeightedActionTerm h0q h0r w (k+N) q‖) ∧
        (∑' k : ℕ, ‖hillNativeComplexWeightedActionTerm h0q h0r w (k+N) q‖)≤C*(9*B^2+2304*B^4) := by
  obtain ⟨C,hC,hbound⟩ := exists_hillComplexActionGapRatio_uniform_inverse_index_bound h0q h0r
  refine ⟨Real.pi*C/2,by positivity,?_⟩
  intro w B
  obtain ⟨Nr,hNr,hr⟩ := hbound B
  obtain ⟨Ng,hNg,hg⟩ := exists_hillNativeComplexGapSquare_weighted_uniform_bound h0q h0r w B
  refine ⟨Nr+Ng,hNr.trans (by omega),?_⟩
  intro N hN q hq
  obtain ⟨hs,hb⟩ := hg N (by omega) q hq
  have hmajor := hs.mul_left (Real.pi*C/2)
  have hp : ‖hillPeriodOneCoefficientMap w q‖≤B := (norm_hillPeriodOneCoefficientMap_le w q).trans hq
  have hpoint (k : ℕ) : ‖hillNativeComplexWeightedActionTerm h0q h0r w (k+N) q‖≤
      (Real.pi*C/2)*((w (2*((k+N:ℕ):ℤ)))^2*‖hillNativeComplexGapSquare h0q h0r w (k+N) q‖) :=
    norm_hillNativeComplexWeightedActionTerm_le h0q h0r w q (k+N) (hNr.trans (by omega)) C (hr _ hp (k+N) (by omega))
  have hf := Summable.of_nonneg_of_le (fun k => norm_nonneg _) hpoint hmajor
  refine ⟨hf,?_⟩
  apply (hf.tsum_le_tsum hpoint hmajor).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem exists_hillNativeComplexWeightedActionTerm_bounded_real_physical_matching (w : SpectralWeight) (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ q : RealHillWeightedPotential w, ‖q.val‖≤B → ∀ n : ℕ, N≤n →
      hillNativeComplexWeightedActionTerm h0q h0r w n q.val=(hillWeightedActionTerm w q n:ℂ) := by
  obtain ⟨N,hN,hmatch⟩ := exists_hillComplexGapAction_bounded_real_physical_matching h0q h0r B
  refine ⟨N,hN,?_⟩
  intro q hq n hn
  have hp : ‖SpectralWeight.one.toCoeff (hillPeriodOneUnitPotential w q.val)‖≤B := by
    rw [← hillPeriodOneCoefficientMap_eq_unit]
    exact (norm_hillPeriodOneCoefficientMap_le w q.val).trans hq
  rw [hillNativeComplexWeightedActionTerm,hillPeriodOneCoefficientMap_eq_unit,
    hmatch _ (hillPeriodOneUnitPotential_even w q.val) (hillPeriodOneUnitPotential_real w q.val q.property) hp n hn]
  simp only [hillWeightedActionTerm,hillPeriodOneAction,ofReal_mul]

end NLS.KdV
