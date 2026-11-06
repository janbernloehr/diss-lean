import NLS.KdV.HillNativeWeightedNormingSheet

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The original complex Dirichlet sheet terminal is bounded uniformly
in the high gap index and the native spectral weight on every bounded source ball. -/
theorem exists_hillNativeComplexDirichletGapTerminal_uniform_bound (B : ℝ) (hB : 0≤B) :
    ∃ T : ℝ, ∃ N : ℕ, 0<T ∧ 1≤N ∧ ∀ w : SpectralWeight,
      ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖≤B → ∀ k : ℕ, N≤k →
        ‖hillNativeComplexDirichletGapTerminal h0q h0r w k q‖≤T := by
  obtain ⟨C,hC,N,hN,hbound⟩ := exists_hillNativeComplexDirichletGapTerminal_weighted_bound h0q h0r B hB
  refine ⟨C*(2*B+16*B^2)+1,N,by positivity,hN,?_⟩
  intro w q hq k hk
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hN.trans hk
  have hc (m : ℤ) : w (2*m)*‖q.val m‖≤‖q‖ := by
    have hh := (le_div_iff₀ (w.doubleIndex.toWeight.positive m)).mp (WeightedCoeff.norm_apply_le w.doubleIndex.toWeight 2 q m)
    change ‖q.val m‖*w.doubleIndex m≤‖q‖ at hh
    rw [SpectralWeight.doubleIndex_apply] at hh
    simpa only [mul_comm] using hh
  have hpos := (hc (k : ℤ)).trans hq
  have hneg := (hc (-(k : ℤ))).trans hq
  rw [mul_neg,SpectralWeight.apply_neg] at hneg
  have hquad : ‖q‖^2≤B^2 := sq_le_sq₀ (norm_nonneg q) hB |>.mpr hq
  have htail : 16*‖q‖^2/(k : ℝ)≤16*B^2 :=
    (div_le_self (by positivity) hk1).trans (mul_le_mul_of_nonneg_left hquad (by norm_num))
  have hh := hbound w q hq k hk
  have hw : ‖hillNativeComplexDirichletGapTerminal h0q h0r w k q‖≤
      w (2*(k : ℤ))*‖hillNativeComplexDirichletGapTerminal h0q h0r w k q‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (w.one_le (2*(k : ℤ))) (norm_nonneg _)
  have hm : C*(w (2*(k : ℤ))*‖q.val k‖+w (2*(k : ℤ))*‖q.val (-(k : ℤ))‖+16*‖q‖^2/(k : ℝ))≤C*(2*B+16*B^2) := by
    gcongr
    linarith
  exact (hw.trans (hh.trans hm)).trans (by linarith)

end NLS.KdV
