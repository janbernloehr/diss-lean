import NLS.KdV.HillUniformDeflatedInverseBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The already proved filled-root inverse estimate has an explicit linear
coordinate-index gain, uniformly on each bounded complex source ball. -/
theorem exists_hillFilledFreeGapRoot_index_inverse_bound :
    ∃ C : ℝ, 0<C ∧ ∀ B : ℝ, ∃ N : ℕ, 1≤N ∧ ∀ p : Coeff 2, ‖p‖≤B →
      ∀ n : ℕ, N≤n → ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r n : ℂ)
        (hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n),
        ‖(hillFilledFreeGapRoot h0q h0r n (E,p))⁻¹‖ ≤ C*(n : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := exists_hillFilledFreeGapRoot_uniform_inverse_bound h0q h0r
  refine ⟨8*C,by positivity,?_⟩
  intro B
  obtain ⟨N,hN,hcommon⟩ := hbound B
  refine ⟨N,hN,?_⟩
  intro p hp n hn E hE
  have hn1 : 1 ≤ n := hN.trans hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hrad : hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n ≤ 8*(n : ℝ) := by
    rw [hillFreeGapHalfLength h0q h0r n hn1,hillFreeGapCollar h0q h0r n hn1,zero_add]
    have hpi : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_pos,Real.pi_lt_four]
    have hh := mul_le_mul_of_nonneg_left hpi (by linarith : 0 ≤ 2*(n : ℝ)-1)
    nlinarith
  exact (hcommon p hp n hn E hE).trans
    ((mul_le_mul_of_nonneg_left hrad hC.le).trans_eq (by ring))

end NLS.KdV
