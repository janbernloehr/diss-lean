import NLS.KdV.HillScaledFreeContourBounds
import NLS.KdV.HillL2DirichletError
import NLS.KdV.HillSmallPotentialRadicand

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillScaledFreeGapContour_high_relative_estimates
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (d b : ℝ) (hd : 0 < d) (hb : 0 < b)
    (p : Coeff 2) (n : ℕ) (hn : 1 ≤ n)
    (hp : 4*Real.exp (Real.pi/2)*‖p‖ ≤ (n : ℝ)*Real.pi/2) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 h0q h0r n : ℂ)
      (ρ*(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n)))
    (hfree : d ≤ ‖hillL2Radicand 0 E‖)
    (hdir : b/(n : ℝ) ≤ ‖hillL2DirichletCharacteristic 0 E‖) :
    ‖hillL2Radicand p E/hillL2Radicand 0 E-1‖ ≤
      (96*(Real.exp (Real.pi/2))^3/(Real.pi*d))*‖p‖/(n : ℝ) ∧
    ‖hillL2DirichletCharacteristic p E/hillL2DirichletCharacteristic 0 E-1‖ ≤
      (16*(Real.exp (Real.pi/2))^2/(Real.pi^2*b))*‖p‖/(n : ℝ) := by
  have hg := hillScaledFreeGapContour_frequency_bounds h0q h0r ρ hρ hρ1 n hn E hE
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hzpos : 0 < ‖Complex.sqrt E‖ := lt_of_lt_of_le (by positivity) hg.2.2.2.1
  have hz0 : Complex.sqrt E ≠ 0 := norm_pos_iff.mp hzpos
  have hs : 4*Real.exp (Real.pi/2)*‖p‖ ≤ ‖Complex.sqrt E‖ := hp.trans hg.2.2.2.1
  have hf : d ≤ ‖hillL2Radicand 0 ((Complex.sqrt E)^2)‖ := by rw [complex_sqrt_sq];exact hfree
  constructor
  · have h := hillL2Radicand_ratio_free_bound p (Complex.sqrt E) hz0 (Real.pi/2) d hg.2.2.1 hd hf hs
    rw [complex_sqrt_sq] at h
    calc
      _ ≤ 48*(Real.exp (Real.pi/2))^3*‖p‖/(‖Complex.sqrt E‖*d) := h
      _ ≤ 48*(Real.exp (Real.pi/2))^3*‖p‖/(((n : ℝ)*Real.pi/2)*d) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right hg.2.2.2.1 hd.le)
      _ = _ := by field_simp;ring
  · have h := hillL2DirichletCharacteristic_free_error_small p (Complex.sqrt E) hz0 (Real.pi/2) hg.2.2.1 hs
    rw [complex_sqrt_sq,← hillL2DirichletCharacteristic_free_sq (Complex.sqrt E) hz0,
      complex_sqrt_sq] at h
    have hDn : hillL2DirichletCharacteristic 0 E ≠ 0 := norm_pos_iff.mp ((by positivity : 0 < b/(n : ℝ)).trans_le hdir)
    rw [show hillL2DirichletCharacteristic p E/hillL2DirichletCharacteristic 0 E-1 =
      (hillL2DirichletCharacteristic p E-hillL2DirichletCharacteristic 0 E)/hillL2DirichletCharacteristic 0 E by field_simp,norm_div]
    calc
      _ ≤ (4*(Real.exp (Real.pi/2))^2*‖p‖/‖Complex.sqrt E‖^2)/‖hillL2DirichletCharacteristic 0 E‖ :=
        div_le_div_of_nonneg_right h (norm_nonneg _)
      _ ≤ (4*(Real.exp (Real.pi/2))^2*‖p‖/(((n : ℝ)*Real.pi/2)^2))/(b/(n : ℝ)) :=
        div_le_div₀ (by positivity)
          (div_le_div_of_nonneg_left (by positivity) (by positivity)
            (sq_le_sq₀ (by positivity) hzpos.le |>.mpr hg.2.2.2.1)) (by positivity) hdir
      _ = _ := by field_simp;ring

theorem exists_hillScaledFreeGapContour_bounded_complex_relative_bounds
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 0 < C ∧ ∀ p : Coeff 2, ‖p‖ ≤ B →
      ∀ n : ℕ, N ≤ n → ∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r n : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n)),
        ‖hillL2Radicand p E/hillL2Radicand 0 E-1‖ ≤ C*‖p‖/(n : ℝ) ∧
        ‖hillL2DirichletCharacteristic p E/hillL2DirichletCharacteristic 0 E-1‖ ≤ C*‖p‖/(n : ℝ) ∧
        C*‖p‖/(n : ℝ) ≤ ε := by
  obtain ⟨d,hd,b,hb,hfree⟩ := exists_hillScaledFreeGapContour_characteristic_bounds h0q h0r ρ hρ hρ1
  let C1 : ℝ := 96*(Real.exp (Real.pi/2))^3/(Real.pi*d)
  let C2 : ℝ := 16*(Real.exp (Real.pi/2))^2/(Real.pi^2*b)
  let C : ℝ := C1+C2
  have hC1 : 0 < C1 := by dsimp only [C1];positivity
  have hC2 : 0 < C2 := by dsimp only [C2];positivity
  have hC : 0 < C := add_pos hC1 hC2
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (max (8*Real.exp (Real.pi/2)*B/Real.pi) (C*B/ε)))
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
  have hB2 : C*B/ε ≤ (n : ℝ) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (hN.le.trans hnR)
  have hs : 4*Real.exp (Real.pi/2)*‖p‖ ≤ (n : ℝ)*Real.pi/2 := by
    have hh := (div_le_iff₀ Real.pi_pos).mp hB1
    have ht := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4*Real.exp (Real.pi/2))
    nlinarith
  obtain ⟨hf,hd'⟩ := hfree n hn1 E hE
  obtain ⟨hr,hD⟩ := hillScaledFreeGapContour_high_relative_estimates h0q h0r ρ hρ hρ1 d b hd hb p n hn1 hs E hE hf hd'
  have hm1 : C1*‖p‖/(n : ℝ) ≤ C*‖p‖/(n : ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC2.le) (norm_nonneg p)) hnpos.le
  have hm2 : C2*‖p‖/(n : ℝ) ≤ C*‖p‖/(n : ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC1.le) (norm_nonneg p)) hnpos.le
  refine ⟨hr.trans hm1,hD.trans hm2,?_⟩
  apply (div_le_iff₀ hnpos).mpr
  exact (mul_le_mul_of_nonneg_left hp hC.le).trans (by simpa only [mul_comm] using (div_le_iff₀ hε).mp hB2)

end NLS.KdV
