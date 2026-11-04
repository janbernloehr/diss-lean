import NLS.KdV.HillFreeContourPhysicalRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillRealLabel_mem_free_contour_ball_of_control (ε D : ℝ)
    (hc : HillComplexPeriodControl h0q h0r ε D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hsmall : ‖SpectralWeight.one.toCoeff q‖ ≤ ε) (k : ℕ) (hk : 1 ≤ k) (j : ℕ)
    (hbase : hillRealLabels 0 h0q h0r j = hillRealGapCenter 0 h0q h0r k) :
    (hillRealLabels q hq hr j : ℂ) ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) := by
  let Q : ℝ → WeightedCoeff SpectralWeight.one.toWeight 2 := fun s => (s : ℂ) • q
  have hQ : Continuous Q := by dsimp only [Q];fun_prop
  have hqp (s : ℝ) : SpectralWeight.one.toCoeff (Q s) ∈ Coeff.paritySubspace 0 := by
    dsimp only [Q]
    rw [map_smul]
    exact (Coeff.paritySubspace 0).smul_mem _ hq
  have hQr (s : ℝ) : IsRealHillPotential (SpectralWeight.one.toCoeff (Q s)) := by
    dsimp only [Q]
    rw [map_smul]
    exact hr.smul_real s
  let L : ℝ → ℝ := fun s => hillRealLabels (Q s) (hqp s) (hQr s) j
  let f : ℝ → ℝ := fun s => ‖(L s : ℂ)-(hillRealGapCenter 0 h0q h0r k : ℂ)‖
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  have hL : Continuous L := continuous_hillRealLabels_family Q hQ hqp hQr j
  have hf : Continuous f := ((Complex.continuous_ofReal.comp hL).sub continuous_const).norm
  have hf0 : f 0 = 0 := by simp only [f,L,Q,ofReal_zero,zero_smul,hbase,sub_self,norm_zero]
  have havoid (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : f s ≠ R := by
    intro he
    have hsp : ‖SpectralWeight.one.toCoeff (Q s)‖ ≤ ε := by
      dsimp only [Q]
      rw [map_smul,norm_smul,norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1]
      exact ((mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)).trans_eq (one_mul _)).trans hsmall
    have hEs : (L s : ℂ) ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ) R := by
      simpa only [mem_sphere,dist_eq_norm] using he
    have hdom := (hc _ hsp).1 k hk (L s) hEs
    have hnonzero : hillL2Radicand (SpectralWeight.one.toCoeff (Q s)) (L s) ≠ 0 := by
      rw [← hillAbelianComplexRoot_sq 0 h0q h0r _ hdom]
      exact pow_ne_zero 2 (hillAbelianComplexRoot_ne_zero 0 h0q h0r _ hdom)
    exact hnonzero ((hillRealLabels_spec (Q s) (hqp s) (hQr s)).root j)
  have hf1 : f 1 < R := by
    by_contra hle
    obtain ⟨s,hs,he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hf.continuousOn
      ⟨by rw [hf0];exact hR.le,not_lt.mp hle⟩
    exact havoid s hs he
  simpa only [f,L,Q,ofReal_one,one_smul,mem_ball,dist_eq_norm] using hf1

theorem hillRealGap_mem_free_contour_ball_of_control (ε D : ℝ)
    (hc : HillComplexPeriodControl h0q h0r ε D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hsmall : ‖SpectralWeight.one.toCoeff q‖ ≤ ε) (k : ℕ) (hk : 1 ≤ k) :
    segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) ⊆
      ball (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) := by
  have hleft := hillRealLabel_mem_free_contour_ball_of_control h0q h0r ε D hc q hq hr hsmall k hk (2*k-1)
    ((hillFreeGapEndpoints h0q h0r k hk).1.trans (hillFreeGapCenter h0q h0r k hk).symm)
  have hright := hillRealLabel_mem_free_contour_ball_of_control h0q h0r ε D hc q hq hr hsmall k hk (2*k)
    ((hillFreeGapEndpoints h0q h0r k hk).2.trans (hillFreeGapCenter h0q h0r k hk).symm)
  exact (convex_ball _ _).segment_subset hleft hright

end NLS.KdV
