import NLS.KdV.HillAbelianHilbertInput
import NLS.KdV.FreeHill

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV



def hillFreeSeparatedWeightSymbol (n k : ℕ) (m : ℤ) : ℂ :=
  if 0 < m ∧ m ≠ (n : ℤ) ∧ m ≠ (k : ℤ) then
    (m : ℂ)/((freeHillValue m.toNat : ℂ)-(freeHillValue k : ℂ)) else 0

theorem hillFreeSeparatedWeightSymbol_bound (n k : ℕ) (m : ℤ) :
    ‖hillFreeSeparatedWeightSymbol n k m‖ ≤
      ‖(((Real.pi : ℂ)^2)⁻¹ • Coeff.shift (k : ℤ)
        (Coeff.puncturedLattice 2 (by norm_num))) m‖ := by
  unfold hillFreeSeparatedWeightSymbol
  split_ifs with hm
  · have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hm.1)
    have hmk : (m : ℂ)-(k : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hm.2.2)
    have hsum : (m : ℂ)+(k : ℂ) ≠ 0 := by
      have h : 0 < (m : ℝ)+(k : ℝ) := by
        have hp : 0 < (m : ℝ) := by exact_mod_cast hm.1
        positivity
      have he : (m : ℂ)+(k : ℂ) = (((m : ℝ)+(k : ℝ) : ℝ) : ℂ) := by push_cast; rfl
      rw [he]
      exact ofReal_ne_zero.mpr (ne_of_gt h)
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hnat : ((m.toNat : ℕ) : ℂ) = (m : ℂ) := by
      exact_mod_cast (show (m.toNat : ℤ) = m by omega)
    have hE : (freeHillValue m.toNat : ℂ)-(freeHillValue k : ℂ) =
        (Real.pi : ℂ)^2*((m : ℂ)-(k : ℂ))*((m : ℂ)+(k : ℂ)) := by
      simp only [freeHillValue,ofReal_mul,ofReal_pow]
      push_cast
      rw [hnat]
      ring
    have halg : (m : ℂ)/((freeHillValue m.toNat : ℂ)-(freeHillValue k : ℂ)) =
        ((Real.pi : ℂ)^2)⁻¹*((m : ℂ)-(k : ℂ))⁻¹*
          ((m : ℂ)/((m : ℂ)+(k : ℂ))) := by
      rw [hE]
      field_simp
    have hratio : ‖(m : ℂ)/((m : ℂ)+(k : ℂ))‖ ≤ 1 := by
      have hmr : 0 < (m : ℝ) := by exact_mod_cast hm.1
      have he : (m : ℂ)/((m : ℂ)+(k : ℂ)) =
          (((m : ℝ)/((m : ℝ)+(k : ℝ)) : ℝ) : ℂ) := by push_cast; rfl
      rw [he,norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_right (Nat.cast_nonneg k))
    rw [halg,norm_mul]
    apply (mul_le_mul_of_nonneg_left hratio (norm_nonneg _)).trans_eq
    rw [mul_one]
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Coeff.shift_apply,
      Coeff.puncturedLattice_apply,if_neg (sub_ne_zero.mpr hm.2.2),norm_mul,Int.cast_sub,Int.cast_natCast]
  · rw [norm_zero]
    exact norm_nonneg _

def hillFreeSeparatedWeight (n k : ℕ) : Coeff 2 :=
  ⟨hillFreeSeparatedWeightSymbol n k,by
    apply (lp.memℓp ((((Real.pi : ℂ)^2)⁻¹ • Coeff.shift (k : ℤ)
      (Coeff.puncturedLattice 2 (by norm_num))) : Coeff 2)).norm.mono
    exact hillFreeSeparatedWeightSymbol_bound n k⟩

theorem norm_hillFreeSeparatedWeight_le (n k : ℕ) :
    ‖hillFreeSeparatedWeight n k‖ ≤ 2/Real.pi^2 := by
  have h : ‖hillFreeSeparatedWeight n k‖ ≤
      ‖((Real.pi : ℂ)^2)⁻¹ • Coeff.shift (k : ℤ) (Coeff.puncturedLattice 2 (by norm_num))‖ :=
    lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hillFreeSeparatedWeightSymbol_bound n k)
  apply h.trans
  rw [norm_smul,Coeff.norm_shift,norm_inv,norm_pow,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  exact (mul_le_mul_of_nonneg_left Coeff.norm_puncturedLattice_two_le (by positivity)).trans_eq (by ring)

theorem hillFreeSeparatedWeight_nonpositive (n k : ℕ) (m : ℤ) (hm : m ≤ 0) :
    hillFreeSeparatedWeight n k m = 0 := by
  change hillFreeSeparatedWeightSymbol n k m = 0
  unfold hillFreeSeparatedWeightSymbol
  exact if_neg (by omega)

theorem hillFreeSeparatedWeight_natSucc (n k j : ℕ) :
    hillFreeSeparatedWeight n k ((j+1 : ℕ) : ℤ) =
      if j+1 = n ∨ j+1 = k then 0 else
        ((j+1 : ℕ) : ℂ)/((freeHillValue (j+1 : ℕ) : ℂ)-(freeHillValue k : ℂ)) := by
  change hillFreeSeparatedWeightSymbol n k ((j+1 : ℕ) : ℤ) = _
  unfold hillFreeSeparatedWeightSymbol
  by_cases h : j+1 = n ∨ j+1 = k
  · rw [if_pos h,if_neg (by omega)]
  · rw [if_neg h,if_pos (by omega)]
    simp only [Int.toNat_natCast,Int.cast_natCast]

theorem norm_hilbertWeightedProduct_hillSeparated_le (n k : ℕ) (a : Coeff 2) :
    ‖hilbertWeightedProduct (hillFreeSeparatedWeight n k) a‖ ≤
      Real.exp ((2/Real.pi^2)*‖a‖) := by
  exact (norm_hilbertWeightedProduct_le _ _).trans (Real.exp_le_exp.mpr (by
    have h := mul_le_mul_of_nonneg_left (norm_hillFreeSeparatedWeight_le n k) (norm_nonneg a)
    nlinarith))

end NLS.KdV
