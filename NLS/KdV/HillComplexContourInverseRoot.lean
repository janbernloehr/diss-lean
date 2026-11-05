import NLS.KdV.HillCommonComplexContourDomain

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV



theorem norm_hillAbelianComplexRoot_base_div_sub_one_le
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (E : ℂ) (p : Coeff 2)
    (hE : E ∈ hillL2RealCutDomain q hq hr)
    (hsmall : ‖hillAbelianComplexRootRatio q (E,p)-1‖ ≤ 1/2) :
    ‖hillEnergyCanonicalRootProduct q hq hr E/hillAbelianComplexRoot q hq hr (E,p)-1‖ ≤
      2*‖hillAbelianComplexRootRatio q (E,p)-1‖ := by
  have hbase := hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr E hE
  have he : hillEnergyCanonicalRootProduct q hq hr E/hillAbelianComplexRoot q hq hr (E,p) =
      (Complex.sqrt (hillAbelianComplexRootRatio q (E,p)))⁻¹ := by
    rw [hillAbelianComplexRoot,div_mul_eq_div_div,div_self hbase,one_div]
  rw [he]
  exact norm_inv_sqrt_sub_one_le _ hsmall

theorem exists_hillFreeGapContour_inverse_root_bound
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2))) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ p : Coeff 2, ‖p‖ ≤ ε →
      ∀ n : ℕ, 1 ≤ n → ∀ E : ℂ,
        E ∈ sphere (hillRealGapCenter 0 hq hr n : ℂ)
          (hillRealGapHalfLength 0 hq hr n+hillRealGapCollar 0 hq hr n) →
        (E,p) ∈ hillAbelianComplexRootDomain 0 hq hr ∧
          ‖hillEnergyCanonicalRootProduct 0 hq hr E/hillAbelianComplexRoot 0 hq hr (E,p)-1‖ ≤
            C*‖p‖/(n : ℝ) := by
  obtain ⟨ε,C,hε,hC,hbound⟩ := exists_hillFreeGapContour_common_complex_neighborhood hq hr
  refine ⟨ε,2*C,hε,by positivity,?_⟩
  intro p hp n hn E hE
  obtain ⟨hdom,hquant,hsmall⟩ := hbound p hp n hn E hE
  have he : hillAbelianComplexRootRatio 0 (E,p) = hillL2Radicand p E/hillL2Radicand 0 E := by
    simp only [hillAbelianComplexRootRatio,map_zero]
  refine ⟨hdom,?_⟩
  have h := norm_hillAbelianComplexRoot_base_div_sub_one_le 0 hq hr E p hdom.1.1 (by rw [he];exact hsmall)
  rw [he] at h
  apply h.trans
  apply (mul_le_mul_of_nonneg_left hquant (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  ring

end NLS.KdV
