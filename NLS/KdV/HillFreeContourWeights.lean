import NLS.KdV.HillFreeContourSeparation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillFreeContourWeightSymbol (n : ℕ) (E : ℂ) (m : ℤ) : ℂ :=
  if 0 < m ∧ m ≠ (n : ℤ) then (m : ℂ)/((freeHillValue m : ℂ)-E) else 0

theorem hillFreeContourWeightSymbol_off_diagonal_bound (n k : ℕ) (hk : 1 ≤ k)
    (E : ℂ) (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k))
    (m : ℤ) (hmk : m ≠ k) :
    ‖hillFreeContourWeightSymbol n E m‖ ≤ 2*‖hillFreeSeparatedWeight n k m‖ := by
  unfold hillFreeContourWeightSymbol
  split_ifs with hm
  · have hnat : (m.toNat : ℤ) = m := by omega
    have hne : freeHillValue m ≠ freeHillValue k := by
      intro he
      have he' : freeHillValue m.toNat = freeHillValue k := by simpa only [hnat] using he
      have h := strictMono_freeHillValue.injective he'
      omega
    have hD : 0 < ‖(freeHillValue m : ℂ)-(freeHillValue k : ℂ)‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
    have hsep := hillFreeGapContour_energy_separation hq hr k hk m hmk hm.1 E hE
    have hweight : hillFreeSeparatedWeight n k m = (m : ℂ)/((freeHillValue m : ℂ)-(freeHillValue k : ℂ)) := by
      change hillFreeSeparatedWeightSymbol n k m = _
      rw [hillFreeSeparatedWeightSymbol,if_pos ⟨hm.1,hm.2,hmk⟩,hnat]
    rw [hweight,norm_div,norm_div]
    apply (div_le_div_of_nonneg_left (norm_nonneg (m : ℂ)) (by positivity) hsep).trans_eq
    ring
  · rw [norm_zero]
    positivity

theorem hillFreeContourWeightSymbol_bound (n k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) (m : ℤ) :
    ‖hillFreeContourWeightSymbol n E m‖ ≤
      ‖(((4/(Real.pi : ℂ)^2) • lp.single 2 (k : ℤ) 1 +
        (2 : ℂ) • hillFreeSeparatedWeight n k) : Coeff 2) m‖ := by
  by_cases hmk : m = k
  · subst m
    have hsep : hillFreeSeparatedWeight n k (k : ℤ) = 0 := by
      change hillFreeSeparatedWeightSymbol n k (k : ℤ) = 0
      simp only [hillFreeSeparatedWeightSymbol,ne_eq,not_true_eq_false,and_false,if_false]
    simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.single_apply]
    simp only [Pi.single_eq_same,hsep,mul_zero,add_zero,mul_one,norm_div,norm_ofNat,
      norm_pow,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    unfold hillFreeContourWeightSymbol
    split_ifs
    · simpa only [Int.cast_natCast] using hillFreeGapContour_diagonal_weight_bound hq hr k hk E hE
    · rw [norm_zero]
      positivity
  · have h := hillFreeContourWeightSymbol_off_diagonal_bound hq hr n k hk E hE m hmk
    simpa only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      lp.single_apply,Pi.single_apply,if_neg hmk,mul_zero,zero_add,norm_mul,norm_ofNat] using h

def hillFreeContourWeight (n k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) : Coeff 2 :=
  ⟨hillFreeContourWeightSymbol n E,by
    apply (lp.memℓp (((4/(Real.pi : ℂ)^2) • lp.single 2 (k : ℤ) 1 +
        (2 : ℂ) • hillFreeSeparatedWeight n k) : Coeff 2)).norm.mono
    exact hillFreeContourWeightSymbol_bound hq hr n k hk E hE⟩

theorem norm_hillFreeContourWeight_le (n k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) :
    ‖hillFreeContourWeight hq hr n k hk E hE‖ ≤ 8/Real.pi^2 := by
  have h : ‖hillFreeContourWeight hq hr n k hk E hE‖ ≤
      ‖((4/(Real.pi : ℂ)^2) • lp.single 2 (k : ℤ) 1 +
        (2 : ℂ) • hillFreeSeparatedWeight n k : Coeff 2)‖ :=
    lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hillFreeContourWeightSymbol_bound hq hr n k hk E hE)
  apply (h.trans (norm_add_le _ _)).trans
  rw [norm_smul,norm_smul,lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),norm_one,mul_one,
    norm_div,norm_ofNat,norm_pow,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,norm_ofNat]
  apply (add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_hillFreeSeparatedWeight_le n k)
    (by norm_num : (0 : ℝ) ≤ 2))).trans_eq
  ring

theorem hillFreeContourWeight_apply (n k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) (m : ℤ) :
    hillFreeContourWeight hq hr n k hk E hE m = hillFreeContourWeightSymbol n E m := rfl

theorem norm_hilbertWeightedProduct_hillFreeContour_le (n k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) (a : Coeff 2) :
    ‖hilbertWeightedProduct (hillFreeContourWeight hq hr n k hk E hE) a‖ ≤
      Real.exp ((8/Real.pi^2)*‖a‖) := by
  apply (norm_hilbertWeightedProduct_le _ _).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (norm_hillFreeContourWeight_le hq hr n k hk E hE) (norm_nonneg a)
  simpa only [mul_comm] using h

end NLS.KdV
