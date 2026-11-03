import NLS.KdV.HillFreeAbelianNormalization
import NLS.ComplexAnalysis.ComplexSquareRootShift

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeGapHalfLength (n : ℕ) (hn : 1 ≤ n) :
    hillRealGapHalfLength 0 hq hr n = 0 := by
  obtain ⟨hl,hu⟩ := hillFreeGapEndpoints hq hr n hn
  rw [hillRealGapHalfLength,hl,hu,sub_self,zero_div]

theorem hillFreeGapCollar (n : ℕ) (hn : 1 ≤ n) :
    hillRealGapCollar 0 hq hr n = (2*(n : ℝ)-1)*Real.pi^2/4 := by
  obtain ⟨hl,hu⟩ := hillFreeGapEndpoints hq hr n hn
  have hlo : hillRealLabels 0 hq hr (2*n-2) = freeHillValue (n-1) := by
    rw [hillRealLabels_zero]
    congr 1
    omega
  have hup : hillRealLabels 0 hq hr (2*n+1) = freeHillValue (n+1) := by
    rw [hillRealLabels_zero]
    congr 1
    omega
  rw [hillRealGapCollar,hl,hu,hlo,hup]
  have hlo' : freeHillValue n-freeHillValue (n-1) = (2*(n : ℝ)-1)*Real.pi^2 := by
    simp only [freeHillValue,Int.cast_natCast]
    push_cast
    ring
  have hup' : freeHillValue (n+1)-freeHillValue n = (2*(n : ℝ)+1)*Real.pi^2 := by
    simp only [freeHillValue]
    push_cast
    ring
  rw [hlo',hup',min_eq_left (by nlinarith [sq_nonneg Real.pi])]

theorem hillFreeGapContour_frequency_bounds (n : ℕ) (hn : 1 ≤ n) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr n : ℂ)
      (hillRealGapHalfLength 0 hq hr n+hillRealGapCollar 0 hq hr n)) :
    Real.pi/10 ≤ ‖Complex.sqrt E-(n : ℂ)*Real.pi‖ ∧
      ‖Complex.sqrt E-(n : ℂ)*Real.pi‖ ≤ Real.pi/2 ∧
      |(Complex.sqrt E).im| ≤ Real.pi/2 ∧
      (n : ℝ)*Real.pi/2 ≤ ‖Complex.sqrt E‖ := by
  let c : ℝ := (n : ℝ)*Real.pi
  let R : ℝ := (2*(n : ℝ)-1)*Real.pi^2/4
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : Real.pi ≤ c := by dsimp only [c];nlinarith [Real.pi_pos]
  have hc0 : 0 < c := Real.pi_pos.trans_le hc
  have hcE : (freeHillValue n : ℂ) = (c : ℂ)^2 := by
    simp only [freeHillValue,Int.cast_natCast,c,ofReal_mul,ofReal_natCast]
    push_cast
    ring
  have hdist : ‖E-(c : ℂ)^2‖ = R := by
    simpa only [mem_sphere,dist_eq_norm,hillFreeGapCenter hq hr n hn,
      hillFreeGapHalfLength hq hr n hn,zero_add,hillFreeGapCollar hq hr n hn,hcE,R] using hE
  have hRlo : c*Real.pi/4 ≤ R := by dsimp only [c,R];nlinarith [sq_pos_of_pos Real.pi_pos]
  have hRhi : R ≤ c*Real.pi/2 := by dsimp only [c,R];nlinarith [sq_pos_of_pos Real.pi_pos]
  let δ := ‖Complex.sqrt E-(c : ℂ)‖
  have hδ : δ ≤ Real.pi/2 := by
    apply (norm_complexSqrt_sub_positive_le E c R hc0 hdist.le).trans
    exact (div_le_iff₀ hc0).mpr (by nlinarith [hRhi])
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
  have hprod : R ≤ δ*(5*c/2) := by
    rw [← hdist,hfactor,norm_mul]
    exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
  have hδlo : Real.pi/10 ≤ δ := by nlinarith [hRlo,hprod]
  have hIm : |(Complex.sqrt E).im| ≤ Real.pi/2 := by
    have h := abs_im_le_norm (Complex.sqrt E-(c : ℂ))
    simp only [sub_im,ofReal_im,sub_zero] at h
    exact h.trans hδ
  have hnorm : c/2 ≤ ‖Complex.sqrt E‖ := by
    have h := norm_sub_norm_le (c : ℂ) (Complex.sqrt E)
    rw [norm_real,Real.norm_eq_abs,abs_of_pos hc0,norm_sub_rev] at h
    linarith
  have hcC : (c : ℂ) = (n : ℂ)*Real.pi := by simp only [c,ofReal_mul,ofReal_natCast]
  exact ⟨by simpa only [δ,hcC] using hδlo,by simpa only [δ,hcC] using hδ,hIm,hnorm⟩

end NLS.KdV
