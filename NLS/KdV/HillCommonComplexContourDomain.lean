import NLS.KdV.HillFreeContourRadicandBound
import NLS.KdV.HillSmallPotentialRadicand
import NLS.KdV.HillAbelianComplexRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeGapContour_radicand_relative_estimate
    (d : ℝ) (hd : 0 < d)
    (hfree : ∀ n : ℕ, 1 ≤ n → ∀ E : ℂ,
      E ∈ sphere (hillRealGapCenter 0 hq hr n : ℂ)
        (hillRealGapHalfLength 0 hq hr n+hillRealGapCollar 0 hq hr n) →
      d ≤ ‖hillL2Radicand 0 E‖)
    (p : Coeff 2) (hp : 4*Real.exp (Real.pi/2)*‖p‖ ≤ Real.pi/2)
    (n : ℕ) (hn : 1 ≤ n) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr n : ℂ)
      (hillRealGapHalfLength 0 hq hr n+hillRealGapCollar 0 hq hr n)) :
    ‖hillL2Radicand p E/hillL2Radicand 0 E-1‖ ≤
      (96*(Real.exp (Real.pi/2))^3/(Real.pi*d))*‖p‖/(n : ℝ) := by
  have hg := hillFreeGapContour_frequency_bounds hq hr n hn E hE
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hz0 : Complex.sqrt E ≠ 0 := norm_pos_iff.mp
    (lt_of_lt_of_le (by positivity : (0 : ℝ) < (n : ℝ)*Real.pi/2) hg.2.2.2)
  have hsq : (Complex.sqrt E)^2 = E := by
    have h := Complex.cpow_nat_inv_pow E (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hs : 4*Real.exp (Real.pi/2)*‖p‖ ≤ ‖Complex.sqrt E‖ :=
    hp.trans ((show Real.pi/2 ≤ (n : ℝ)*Real.pi/2 by
      nlinarith only [Real.pi_pos,hnR]).trans hg.2.2.2)
  have hf : d ≤ ‖hillL2Radicand 0 ((Complex.sqrt E)^2)‖ := by rw [hsq];exact hfree n hn E hE
  have hb := hillL2Radicand_ratio_free_bound p (Complex.sqrt E) hz0 (Real.pi/2) d hg.2.2.1 hd hf hs
  rw [hsq] at hb
  calc
    _ ≤ 48*(Real.exp (Real.pi/2))^3*‖p‖/(‖Complex.sqrt E‖*d) := hb
    _ ≤ 48*(Real.exp (Real.pi/2))^3*‖p‖/(((n : ℝ)*Real.pi/2)*d) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hg.2.2.2 hd.le)
    _ = _ := by field_simp;ring

theorem exists_hillFreeGapContour_common_complex_neighborhood :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ p : Coeff 2, ‖p‖ ≤ ε →
      ∀ n : ℕ, 1 ≤ n → ∀ E : ℂ,
        E ∈ sphere (hillRealGapCenter 0 hq hr n : ℂ)
          (hillRealGapHalfLength 0 hq hr n+hillRealGapCollar 0 hq hr n) →
        (E,p) ∈ hillAbelianComplexRootDomain 0 hq hr ∧
          ‖hillL2Radicand p E/hillL2Radicand 0 E-1‖ ≤ C*‖p‖/(n : ℝ) ∧
          ‖hillL2Radicand p E/hillL2Radicand 0 E-1‖ ≤ 1/2 := by
  obtain ⟨d,hd,hfree⟩ := exists_hillFreeGapContour_free_radicand_bound hq hr
  let C := 96*(Real.exp (Real.pi/2))^3/(Real.pi*d)
  have hC : 0 < C := by dsimp only [C];positivity
  obtain ⟨ε₁,hε₁,hsmall⟩ := exists_pos_mul_lt (by positivity : (0 : ℝ) < Real.pi/2) (4*Real.exp (Real.pi/2))
  obtain ⟨ε₂,hε₂,hratio⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1/2) C
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  refine ⟨ε,C,hε,hC,?_⟩
  intro p hp n hn E hE
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 4*Real.exp (Real.pi/2)*‖p‖ ≤ Real.pi/2 :=
    (mul_le_mul_of_nonneg_left (hp.trans (min_le_left ε₁ ε₂)) (by positivity)).trans hsmall.le
  have hb := hillFreeGapContour_radicand_relative_estimate hq hr d hd hfree p hs n hn E hE
  have hh : C*‖p‖/(n : ℝ) ≤ 1/2 := by
    have hp' : C*‖p‖ ≤ C*ε₂ := mul_le_mul_of_nonneg_left
      (hp.trans (min_le_right ε₁ ε₂)) hC.le
    exact (div_le_self (mul_nonneg hC.le (norm_nonneg p)) hnR).trans (hp'.trans hratio.le)
  refine ⟨?_,hb,hb.trans hh⟩
  refine ⟨⟨hillRealGapContour_sphere_subset 0 hq hr n hn hE,mem_univ _⟩,?_⟩
  have hslit := mem_slitPlane_of_norm_sub_one_le_half _ (hb.trans hh)
  change hillAbelianComplexRootRatio 0 (E,p) ∈ slitPlane
  dsimp only [hillAbelianComplexRootRatio]
  rw [map_zero]
  exact hslit

end NLS.KdV
