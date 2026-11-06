import NLS.KdV.HillBoundedComplexTailDomain
import NLS.KdV.HillComplexPeriodErrorBounds
import NLS.KdV.HillComplexPeriodDomainAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGapContour_bounded_complex_tail_inverse_bound (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 0 < C ∧ ∀ p : Coeff 2, ‖p‖ ≤ B →
      ∀ n : ℕ, N ≤ n → ∀ E ∈ sphere (hillRealGapCenter 0 hq hr n : ℂ)
        (hillRealGapHalfLength 0 hq hr n+hillRealGapCollar 0 hq hr n),
        (E,p) ∈ hillAbelianComplexRootDomain 0 hq hr ∧
          ‖hillEnergyCanonicalRootProduct 0 hq hr E/hillAbelianComplexRoot 0 hq hr (E,p)-1‖ ≤
            C*‖p‖/(n : ℝ) := by
  obtain ⟨N,hN,C,hC,hbound⟩ := exists_hillFreeGapContour_bounded_complex_tail_domain hq hr B
  refine ⟨N,hN,2*C,by positivity,?_⟩
  intro p hp n hn E hE
  obtain ⟨hdom,hquant,hsmall⟩ := hbound p hp n hn E hE
  have he : hillAbelianComplexRootRatio 0 (E,p) = hillL2Radicand p E/hillL2Radicand 0 E := by
    simp only [hillAbelianComplexRootRatio,map_zero]
  refine ⟨hdom,?_⟩
  have ht := norm_hillAbelianComplexRoot_base_div_sub_one_le 0 hq hr E p hdom.1.1 (by rw [he];exact hsmall)
  rw [he] at ht
  apply ht.trans
  apply (mul_le_mul_of_nonneg_left hquant (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  ring

theorem exists_hillAbelianComplexPeriod_bounded_tail_control (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ D : ℝ, 0 < D ∧ ∀ p : Coeff 2, ‖p‖ ≤ B →
      (∀ k : ℕ, N ≤ k → ∀ E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
        (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k),
        (E,p) ∈ hillAbelianComplexRootDomain 0 hq hr) ∧
      ∀ n k : ℕ, 1 ≤ n → N ≤ k → n ≠ k → ∀ a : Coeff 2,
        ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
          (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤
          D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ) := by
  obtain ⟨N,hN,C,hC,hbound⟩ := exists_hillFreeGapContour_bounded_complex_tail_inverse_bound hq hr B
  refine ⟨N,hN,2*Real.pi^2*C,by positivity,?_⟩
  intro p hp
  refine ⟨fun k hk E hE => (hbound p hp k hk E hE).1,?_⟩
  intro n k hn hk hnk a
  exact norm_scaled_hillAbelianComplexPeriod_error_le hq hr n k hn (hN.trans hk) hnk a p C hC.le
    (fun E hE => (hbound p hp k hk E hE).1) (fun E hE => (hbound p hp k hk E hE).2)

theorem exists_hillAbelianComplexPeriods_uniform_analytic_tail (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n k : ℕ, N ≤ k →
      AnalyticOnNhd ℂ (hillAbelianComplexPeriod 0 hq hr n k) (univ ×ˢ ball (0 : Coeff 2) B) := by
  obtain ⟨N,hN,C,hC,hbound⟩ := exists_hillFreeGapContour_bounded_complex_tail_domain hq hr B
  refine ⟨N,hN,?_⟩
  intro n k hk
  apply analyticOnNhd_hillAbelianComplexPeriod_of_domain 0 hq hr n k (hN.trans hk) (ball 0 B) isOpen_ball
  intro p hp E hE
  have hpB : ‖p‖ ≤ B := (show ‖p‖ < B by simpa only [mem_ball,dist_zero_right] using hp).le
  exact (hbound p hpB k hk E hE).1

end NLS.KdV
