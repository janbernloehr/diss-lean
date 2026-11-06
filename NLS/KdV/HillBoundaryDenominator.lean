import NLS.KdV.HillDirichletScalarBalance
import NLS.KdV.HillDirichletEnergyDisplacement

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



private theorem unit_coefficient_norm_le (a : WeightedCoeff SpectralWeight.one.toWeight 2) (k : ℤ) :
    ‖a.val k‖ ≤ ‖a‖ := by
  simpa only [SpectralWeight.one_apply,div_one] using WeightedCoeff.norm_apply_le SpectralWeight.one.toWeight 2 a k

/-- Every raw coefficient of the corrected unit-weight modes has the same
uniform bound, including both diagonal and off-diagonal effective entries. -/
theorem hillUnitCorrectedMode_coefficient_le
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (E : ℂ) (hz : E ∈ reducedHillStrip n) (hc : 8*‖q‖ ≤ (n : ℝ)) (j k : ℤ) :
    ‖(hillCorrectedMode SpectralWeight.one q n hn E hz hc j).val k‖ ≤ 2*‖q‖ := by
  have h0 := shiftedNorm_coefficient_le SpectralWeight.one (-j) k
    (hillCorrectedMode SpectralWeight.one q n hn E hz hc j)
  simp only [SpectralWeight.one_apply,one_mul] at h0
  exact h0.trans (shiftedNorm_hillCorrectedMode_le SpectralWeight.one q n hn E hz hc j)

/-- A common high cutoff separates the actual boundary denominator from
zero on every bounded complex potential ball and every localized energy.
The cutoff is independent of the auxiliary spectral weight. -/
theorem exists_hillBoundaryScalarDenominator_uniform_lower_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ N : ℕ, 1 ≤ N ∧ 8*B ≤ (N : ℝ) ∧
      ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2, ‖q‖ ≤ B →
      ∀ n : ℕ, N ≤ n → ∀ hn1 : 1 ≤ n, ∀ E : ℂ, ∀ hz : E ∈ reducedHillStrip n,
      ‖E-(freeHillValue n : ℂ)‖ ≤ 24*(Real.exp (1/2))^2*B →
      ∀ hc : 8*‖q‖ ≤ (n : ℝ),
        1 ≤ ‖hillBoundaryScalarDenominator q n hn1 E hz hc‖ ∧
        ‖1+(hillBoundaryGreenPotential q n hn1 n E hz hc).val n‖ ≤ 2 ∧
        ‖1+(hillBoundaryGreenPotential q n hn1 n E hz hc).val (-(n : ℤ))‖ ≤ 2 ∧
        ‖hillReconstructionBoundaryRow SpectralWeight.one n (q,E) (1,0)‖ ≤ 2 ∧
        ‖hillReconstructionBoundaryRow SpectralWeight.one n (q,E) (0,1)‖ ≤ 2 ∧
        ‖hillBoundaryGreenTrace q n hn1 n E hz hc‖ ≤ 1 := by
  let C : ℝ := 24*(Real.exp (1/2))^2
  let K : ℝ := (C+2)*B
  let τ : ℝ := 1/(8*(K+1))
  have hC : 0 ≤ C := by dsimp only [C];positivity
  have hK : 0 ≤ K := mul_nonneg (by dsimp only [C];positivity) hB
  have hτpos : 0 < τ := by dsimp only [τ];positivity
  have hτ : τ ≤ 1/8 := by
    dsimp only [τ]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 8*(K+1))).mpr (by nlinarith)
  have hτK : τ*K ≤ 1/8 := by
    calc
      _ = K/(8*(K+1)) := by dsimp only [τ];ring
      _ ≤ 1/8 := (div_le_iff₀ (by positivity : (0 : ℝ) < 8*(K+1))).mpr (by nlinarith)
  obtain ⟨N,hN,hN8,hsmall⟩ := exists_hillBoundaryGreen_uniform_small B τ hτpos
  obtain ⟨M,hM⟩ := exists_nat_gt (64*B)
  refine ⟨max N M,hN.trans (le_max_left _ _),hN8.trans (by exact_mod_cast le_max_left N M),?_⟩
  intro q hq n hn hn1 E hz hnear hc
  have hnN : N ≤ n := (le_max_left N M).trans hn
  have hn64 : 64*B ≤ (n : ℝ) := hM.le.trans (by exact_mod_cast (le_max_right N M).trans hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have herr : 8*‖q‖/(n : ℝ) ≤ 1/8 := (div_le_iff₀ hnpos).mpr (by nlinarith)
  obtain ⟨hP,_,ht⟩ := hsmall q hq n hnN hn1 n E hz hc
  have hap : ‖(1+(hillBoundaryGreenPotential q n hn1 n E hz hc).val n)-1‖ ≤ 1/8 := by
    rw [add_sub_cancel_left]
    exact (unit_coefficient_norm_le _ _).trans (hP.le.trans hτ)
  have ham : ‖(1+(hillBoundaryGreenPotential q n hn1 n E hz hc).val (-(n : ℤ)))-1‖ ≤ 1/8 := by
    rw [add_sub_cancel_left]
    exact (unit_coefficient_norm_le _ _).trans (hP.le.trans hτ)
  have hBp : ‖hillReconstructionBoundaryRow SpectralWeight.one n (q,E) (1,0)-1‖ ≤ 1/8 := by
    have hh := norm_hillReconstructionBoundaryRow_error_le SpectralWeight.one n hn1 (q,E) hz hc (1,0)
    have hb : ‖hillReconstructionBoundaryRow SpectralWeight.one n (q,E) (1,0)-1‖ ≤ 8*‖q‖/(n : ℝ) := by
      simpa using hh
    exact hb.trans herr
  have hBm : ‖hillReconstructionBoundaryRow SpectralWeight.one n (q,E) (0,1)-1‖ ≤ 1/8 := by
    have hh := norm_hillReconstructionBoundaryRow_error_le SpectralWeight.one n hn1 (q,E) hz hc (0,1)
    have hb : ‖hillReconstructionBoundaryRow SpectralWeight.one n (q,E) (0,1)-1‖ ≤ 8*‖q‖/(n : ℝ) := by
      simpa using hh
    exact hb.trans herr
  have hd : ‖E-(freeHillValue n : ℂ)-hillDiagonal SpectralWeight.one q n hn1 E hz hc‖ ≤ K := by
    have hdiag : ‖hillDiagonal SpectralWeight.one q n hn1 E hz hc‖ ≤ 2*‖q‖ :=
      hillUnitCorrectedMode_coefficient_le q n hn1 E hz hc n n
    have hh := norm_sub_le (E-(freeHillValue n : ℂ)) (hillDiagonal SpectralWeight.one q n hn1 E hz hc)
    dsimp only [K,C]
    nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 2)]
  have htd : ‖hillBoundaryGreenTrace q n hn1 n E hz hc*
      (E-(freeHillValue n : ℂ)-hillDiagonal SpectralWeight.one q n hn1 E hz hc)‖ ≤ 1/8 := by
    rw [norm_mul]
    exact (mul_le_mul ht.le hd (norm_nonneg _) hτpos.le).trans hτK
  obtain ⟨hden,ha,hb,hA,hB'⟩ := norm_augmented_boundary_denominator_ge_one _ _ _ _ _ _ hap ham hBp hBm htd
  refine ⟨hden,ha,hb,hA,hB',?_⟩
  exact ht.le.trans (hτ.trans (by norm_num))

end NLS.KdV
