import NLS.KdV.HillCommonComplexContourDomain

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeGapContour_high_radicand_relative_estimate
    (d : ℝ) (hd : 0 < d)
    (hfree : ∀ n : ℕ, 1 ≤ n → ∀ E : ℂ,
      E ∈ sphere (hillRealGapCenter 0 hq hr n : ℂ)
        (hillRealGapHalfLength 0 hq hr n+hillRealGapCollar 0 hq hr n) →
      d ≤ ‖hillL2Radicand 0 E‖)
    (p : Coeff 2) (n : ℕ) (hn : 1 ≤ n)
    (hp : 4*Real.exp (Real.pi/2)*‖p‖ ≤ (n : ℝ)*Real.pi/2) (E : ℂ)
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
    hp.trans hg.2.2.2
  have hf : d ≤ ‖hillL2Radicand 0 ((Complex.sqrt E)^2)‖ := by rw [hsq];exact hfree n hn E hE
  have hb := hillL2Radicand_ratio_free_bound p (Complex.sqrt E) hz0 (Real.pi/2) d hg.2.2.1 hd hf hs
  rw [hsq] at hb
  calc
    _ ≤ 48*(Real.exp (Real.pi/2))^3*‖p‖/(‖Complex.sqrt E‖*d) := hb
    _ ≤ 48*(Real.exp (Real.pi/2))^3*‖p‖/(((n : ℝ)*Real.pi/2)*d) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hg.2.2.2 hd.le)
    _ = _ := by field_simp;ring

theorem exists_hillFreeGapContour_bounded_complex_tail_domain (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 0 < C ∧ ∀ p : Coeff 2, ‖p‖ ≤ B →
      ∀ n : ℕ, N ≤ n → ∀ E ∈ sphere (hillRealGapCenter 0 hq hr n : ℂ)
        (hillRealGapHalfLength 0 hq hr n+hillRealGapCollar 0 hq hr n),
        (E,p) ∈ hillAbelianComplexRootDomain 0 hq hr ∧
          ‖hillL2Radicand p E/hillL2Radicand 0 E-1‖ ≤ C*‖p‖/(n : ℝ) ∧
          ‖hillL2Radicand p E/hillL2Radicand 0 E-1‖ ≤ 1/2 := by
  obtain ⟨d,hd,hfree⟩ := exists_hillFreeGapContour_free_radicand_bound hq hr
  let C : ℝ := 96*(Real.exp (Real.pi/2))^3/(Real.pi*d)
  have hC : 0 < C := by dsimp only [C];positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (max (8*Real.exp (Real.pi/2)*B/Real.pi) (2*C*B)))
  have hNone : 1 ≤ N := by
    have h1 : (1 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
    exact_mod_cast h1.le
  refine ⟨N,hNone,C,hC,?_⟩
  intro p hp n hn E hE
  have hn1 : 1 ≤ n := hNone.trans hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hB1 : 8*Real.exp (Real.pi/2)*B/Real.pi ≤ (n : ℝ) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hN.le.trans hnR)
  have hB2 : 2*C*B ≤ (n : ℝ) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (hN.le.trans hnR)
  have hs : 4*Real.exp (Real.pi/2)*‖p‖ ≤ (n : ℝ)*Real.pi/2 := by
    have hh := (div_le_iff₀ Real.pi_pos).mp hB1
    have ht := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4*Real.exp (Real.pi/2))
    nlinarith
  have hb := hillFreeGapContour_high_radicand_relative_estimate hq hr d hd hfree p n hn1 hs E hE
  have hsmall : C*‖p‖/(n : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hnpos).mpr
    have ht := mul_le_mul_of_nonneg_left hp hC.le
    linarith
  refine ⟨?_,hb,hb.trans hsmall⟩
  refine ⟨⟨hillRealGapContour_sphere_subset 0 hq hr n hn1 hE,mem_univ _⟩,?_⟩
  have hslit := mem_slitPlane_of_norm_sub_one_le_half _ (hb.trans hsmall)
  change hillAbelianComplexRootRatio 0 (E,p) ∈ slitPlane
  dsimp only [hillAbelianComplexRootRatio]
  rw [map_zero]
  exact hslit

end NLS.KdV
