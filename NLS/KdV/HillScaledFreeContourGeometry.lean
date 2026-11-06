import NLS.KdV.HillFreeGapContourGeometry

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillScaledFreeGapContour_frequency_bounds (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 h0q h0r n : ℂ)
      (ρ*(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n))) :
    ρ*Real.pi/10 ≤ ‖Complex.sqrt E-(n : ℂ)*Real.pi‖ ∧
      ‖Complex.sqrt E-(n : ℂ)*Real.pi‖ ≤ Real.pi/2 ∧
      |(Complex.sqrt E).im| ≤ Real.pi/2 ∧
      (n : ℝ)*Real.pi/2 ≤ ‖Complex.sqrt E‖ ∧ ‖Complex.sqrt E‖ ≤ 3*(n : ℝ)*Real.pi/2 := by
  let c : ℝ := (n : ℝ)*Real.pi
  let R : ℝ := (2*(n : ℝ)-1)*Real.pi^2/4
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : Real.pi ≤ c := by dsimp only [c];nlinarith [Real.pi_pos]
  have hc0 : 0 < c := Real.pi_pos.trans_le hc
  have hcE : (freeHillValue n : ℂ) = (c : ℂ)^2 := by
    simp only [freeHillValue,Int.cast_natCast,c,ofReal_mul,ofReal_natCast]
    push_cast
    ring
  have hdist : ‖E-(c : ℂ)^2‖ = ρ*R := by
    simpa only [mem_sphere,dist_eq_norm,hillFreeGapCenter h0q h0r n hn,
      hillFreeGapHalfLength h0q h0r n hn,zero_add,hillFreeGapCollar h0q h0r n hn,hcE,R] using hE
  have hRlo : c*Real.pi/4 ≤ R := by dsimp only [c,R];nlinarith [sq_pos_of_pos Real.pi_pos]
  have hRhi : R ≤ c*Real.pi/2 := by dsimp only [c,R];nlinarith [sq_pos_of_pos Real.pi_pos]
  have hR0 : 0 ≤ R := (by positivity : 0 ≤ c*Real.pi/4).trans hRlo
  have hρRhi : ρ*R ≤ c*Real.pi/2 := (mul_le_of_le_one_left hR0 hρ1).trans hRhi
  let δ := ‖Complex.sqrt E-(c : ℂ)‖
  have hδ : δ ≤ Real.pi/2 := by
    apply (norm_complexSqrt_sub_positive_le E c (ρ*R) hc0 hdist.le).trans
    exact (div_le_iff₀ hc0).mpr (by nlinarith [hρRhi])
  have hsq : (Complex.sqrt E)^2 = E := by
    have h := Complex.cpow_nat_inv_pow E (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hfactor : E-(c : ℂ)^2 = (Complex.sqrt E-(c : ℂ))*(Complex.sqrt E+(c : ℂ)) := by
    linear_combination -hsq
  have hsum : ‖Complex.sqrt E+(c : ℂ)‖ ≤ 5*c/2 := by
    have h := norm_add_le (Complex.sqrt E-(c : ℂ)) (2*(c : ℂ))
    rw [show Complex.sqrt E-(c : ℂ)+2*(c : ℂ) = Complex.sqrt E+(c : ℂ) by ring,
      norm_mul,norm_ofNat,norm_real,Real.norm_eq_abs,abs_of_pos hc0] at h
    change ‖Complex.sqrt E+(c : ℂ)‖ ≤ δ+2*c at h
    linarith
  have hprod : ρ*R ≤ δ*(5*c/2) := by
    rw [← hdist,hfactor,norm_mul]
    exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
  have hδlo : ρ*Real.pi/10 ≤ δ := by
    have hlo := mul_le_mul_of_nonneg_left hRlo hρ.le
    have hm : (ρ*Real.pi/10)*c ≤ δ*c := by nlinarith [hlo,hprod]
    exact (mul_le_mul_iff_left₀ hc0).mp (by nlinarith [hm])
  have hIm : |(Complex.sqrt E).im| ≤ Real.pi/2 := by
    have h := abs_im_le_norm (Complex.sqrt E-(c : ℂ))
    simp only [sub_im,ofReal_im,sub_zero] at h
    exact h.trans hδ
  have hnorm : c/2 ≤ ‖Complex.sqrt E‖ := by
    have h := norm_sub_norm_le (c : ℂ) (Complex.sqrt E)
    rw [norm_real,Real.norm_eq_abs,abs_of_pos hc0,norm_sub_rev] at h
    linarith
  have hnormup : ‖Complex.sqrt E‖ ≤ 3*c/2 := by
    have h := norm_add_le (Complex.sqrt E-(c : ℂ)) (c : ℂ)
    rw [sub_add_cancel,norm_real,Real.norm_eq_abs,abs_of_pos hc0] at h
    change ‖Complex.sqrt E‖ ≤ δ+c at h
    linarith
  have hcC : (c : ℂ) = (n : ℂ)*Real.pi := by simp only [c,ofReal_mul,ofReal_natCast]
  exact ⟨by simpa only [δ,hcC] using hδlo,by simpa only [δ,hcC] using hδ,hIm,hnorm,by simpa only [c,mul_assoc] using hnormup⟩

end NLS.KdV
