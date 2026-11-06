import NLS.KdV.HillUniformComplexDirichlet
import NLS.KdV.HillL2DirichletError
import NLS.ComplexAnalysis.LocalSineInverse
import NLS.ComplexAnalysis.ComplexSquareRootShift

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



/-- The actual Dirichlet free-error estimate gives a mode-independent linear
energy displacement once the root lies in a small free energy neighborhood. -/
theorem hillDirichlet_zero_energy_displacement_le (q : Coeff 2) (n : ℕ) (hn : 1 ≤ n)
    (E : ℂ) (hzero : hillL2DirichletCharacteristic q E=0)
    (hnear : ‖E-(freeHillValue n : ℂ)‖ ≤ (n : ℝ)*Real.pi/2)
    (hsmall : 4*Real.exp (1/2)*‖q‖ ≤ (n : ℝ)*Real.pi/2) :
    ‖E-(freeHillValue n : ℂ)‖ ≤ 24*(Real.exp (1/2))^2*‖q‖ := by
  let c : ℝ := (n : ℝ)*Real.pi
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcpi : Real.pi ≤ c := by dsimp only [c];nlinarith [Real.pi_pos]
  have hc0 : 0 < c := Real.pi_pos.trans_le hcpi
  have hc1 : 1 ≤ c := by linarith [Real.pi_gt_three]
  have hcE : (freeHillValue n : ℂ) = (c : ℂ)^2 := by
    simp only [freeHillValue,Int.cast_natCast,c]
    push_cast
    ring
  have hδ : ‖Complex.sqrt E-(c : ℂ)‖ ≤ 1/2 := by
    have hh := norm_complexSqrt_sub_positive_le E c (c/2) hc0 (by simpa only [← hcE,c] using hnear)
    exact hh.trans_eq (by field_simp)
  have hlo : c/2 ≤ ‖Complex.sqrt E‖ := by
    have hh := norm_sub_norm_le (c : ℂ) (Complex.sqrt E)
    rw [norm_real,Real.norm_of_nonneg hc0.le,norm_sub_rev] at hh
    linarith
  have hspos : 0 < ‖Complex.sqrt E‖ := lt_of_lt_of_le (half_pos hc0) hlo
  have hIm : |(Complex.sqrt E).im| ≤ 1/2 := by
    have hh := abs_im_le_norm (Complex.sqrt E-(c : ℂ))
    simpa only [sub_im,ofReal_im,sub_zero] using hh.trans hδ
  have hs := hillL2DirichletCharacteristic_free_error_small q (Complex.sqrt E)
    (norm_pos_iff.mp hspos) (1/2) hIm (hsmall.trans hlo)
  rw [complex_sqrt_sq,hzero,zero_sub,norm_neg,norm_div] at hs
  have hsinprod : ‖Complex.sin (Complex.sqrt E)‖*‖Complex.sqrt E‖ ≤ 4*(Real.exp (1/2))^2*‖q‖ := by
    apply (mul_le_mul_iff_right₀ hspos).mp
    nlinarith [(div_le_div_iff₀ hspos (sq_pos_of_pos hspos)).mp hs]
  have hcC : (c : ℂ) = (n : ℂ)*Real.pi := by simp only [c,ofReal_mul,ofReal_natCast]
  have hcos : Complex.cos ((n : ℂ)*Real.pi) = (-1 : ℂ)^n := by
    have hh := congrArg Complex.ofReal (Real.cos_nat_mul_pi n)
    push_cast at hh
    exact hh
  have hnormsin : ‖Complex.sin (Complex.sqrt E-(c : ℂ))‖ = ‖Complex.sin (Complex.sqrt E)‖ := by
    rw [hcC,Complex.sin_sub,Complex.sin_nat_mul_pi,hcos,mul_zero,sub_zero,norm_mul,
      norm_pow,norm_neg,norm_one,one_pow,mul_one]
  have hinv := norm_le_two_mul_norm_sin_of_half (Complex.sqrt E-(c : ℂ)) hδ
  rw [hnormsin] at hinv
  have hprod : ‖Complex.sqrt E-(c : ℂ)‖*‖Complex.sqrt E‖ ≤ 8*(Real.exp (1/2))^2*‖q‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hinv (norm_nonneg (Complex.sqrt E))]
  have hsum : ‖Complex.sqrt E+(c : ℂ)‖ ≤ 3*‖Complex.sqrt E‖ := by
    have hh := norm_add_le (Complex.sqrt E) (c : ℂ)
    rw [norm_real,Real.norm_of_nonneg hc0.le] at hh
    linarith
  have hfactor : E-(c : ℂ)^2 = (Complex.sqrt E-(c : ℂ))*(Complex.sqrt E+(c : ℂ)) := by
    linear_combination -(complex_sqrt_sq E)
  rw [hcE,hfactor,norm_mul]
  have hh := mul_le_mul_of_nonneg_left hsum (norm_nonneg (Complex.sqrt E-(c : ℂ)))
  nlinarith

/-- On every bounded complex potential ball, the actual common high
Dirichlet roots stay within a fixed multiple of the potential norm of the
free energy, independently of the coordinate index. -/
theorem exists_hillScaledDirichletRoot_energy_displacement_bound
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : Coeff 2, ‖q‖ ≤ B → ∀ n : ℕ, N ≤ n →
      ‖hillScaledDirichletRoot h0q h0r (1/16) n q-(freeHillValue n : ℂ)‖ ≤
        24*(Real.exp (1/2))^2*‖q‖ := by
  obtain ⟨N,hN,hchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart
    h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨M,hM⟩ := exists_nat_gt (8*Real.exp (1/2)*B/Real.pi)
  refine ⟨max N M,hN.trans (le_max_left _ _),?_⟩
  intro q hq n hn
  have hnN : N ≤ n := (le_max_left N M).trans hn
  have hn1 : 1 ≤ n := hN.trans hnN
  have hB : 8*Real.exp (1/2)*B/Real.pi ≤ (n : ℝ) :=
    hM.le.trans (by exact_mod_cast (le_max_right N M).trans hn)
  have hsmall : 4*Real.exp (1/2)*‖q‖ ≤ (n : ℝ)*Real.pi/2 := by
    have hh := (div_le_iff₀ Real.pi_pos).mp hB
    nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 4*Real.exp (1/2))]
  obtain ⟨hball,hzero,_⟩ := (hchart n hnN).2 q hq
  have hnear : ‖hillScaledDirichletRoot h0q h0r (1/16) n q-(freeHillValue n : ℂ)‖ ≤
      (n : ℝ)*Real.pi/2 := by
    have hh : ‖hillScaledDirichletRoot h0q h0r (1/16) n q-(freeHillValue n : ℂ)‖ <
        (1/16)*((2*(n : ℝ)-1)*Real.pi^2/4) := by
      simpa only [mem_ball,dist_eq_norm,hillFreeGapCenter h0q h0r n hn1,
        hillFreeGapHalfLength h0q h0r n hn1,hillFreeGapCollar h0q h0r n hn1,zero_add] using hball
    have hpi : Real.pi^2 ≤ 16*Real.pi := by nlinarith [Real.pi_pos,Real.pi_lt_four]
    have hm := mul_le_mul_of_nonneg_left hpi (show (0 : ℝ) ≤ n by positivity)
    exact hh.le.trans (by nlinarith [sq_nonneg Real.pi])
  exact hillDirichlet_zero_energy_displacement_le q n hn1 _ hzero hnear hsmall

end NLS.KdV
