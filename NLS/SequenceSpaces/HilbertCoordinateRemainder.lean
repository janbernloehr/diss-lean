import NLS.SequenceSpaces.ConjugateDuality
import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.Translation

/-! # Removing one Hilbert coordinate in bilinear coefficient pairings -/
noncomputable section
namespace NLS.Coeff

def coordinateRemainder (a : Coeff 2) (k : ℤ) : Coeff 2 := a-lp.single 2 k (a k)

theorem coordinateRemainder_apply (a : Coeff 2) (k j : ℤ) :
    coordinateRemainder a k j = if j = k then 0 else a j := by
  by_cases hj : j = k
  · subst j
    simp [coordinateRemainder,lp.single_apply]
  · simp [coordinateRemainder,lp.single_apply,hj]

theorem dualPairing_coordinateRemainder (a b : Coeff 2) (k : ℤ) :
    dualPairing a (coordinateRemainder b k) = dualPairing a b-a k*b k := by
  unfold coordinateRemainder
  rw [map_sub]
  congr 1
  simp [dualPairing_apply,lp.single_apply,Pi.single_apply]

theorem norm_dualPairing_split_le (a b : Coeff 2) (k : ℤ) :
    ‖dualPairing a b‖ ≤ ‖a k‖*‖b k‖+‖a‖*‖coordinateRemainder b k‖ := by
  have he : dualPairing a b = a k*b k+dualPairing a (coordinateRemainder b k) := by
    rw [dualPairing_coordinateRemainder]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (by rw [norm_mul]) (norm_dualPairing_le _ _))

theorem norm_coordinate_le_of_zero_pairing (a b : Coeff 2) (k : ℤ)
    (ha : ‖a‖ ≤ 2) (hb : 1/2 ≤ ‖b k‖) (hzero : dualPairing a b = 0) :
    ‖a k‖ ≤ 4*‖coordinateRemainder b k‖ := by
  have he := dualPairing_coordinateRemainder a b k
  rw [hzero,zero_sub] at he
  have hn : ‖a k‖*‖b k‖ ≤ 2*‖coordinateRemainder b k‖ := by
    calc
      _ = ‖dualPairing a (coordinateRemainder b k)‖ := by rw [he,norm_neg,norm_mul]
      _ ≤ ‖a‖*‖coordinateRemainder b k‖ := norm_dualPairing_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (a k))]

theorem norm_le_of_punctured_majorant (v : Coeff 2) (k : ℤ) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ j : ℤ, ‖v j‖ ≤ L*‖shift k (puncturedLattice 2 (by norm_num)) j‖) :
    ‖v‖ ≤ 2*L := by
  let w : Coeff 2 := (L : ℂ) • shift k (puncturedLattice 2 (by norm_num))
  have hw (j : ℤ) : ‖w j‖ = L*‖shift k (puncturedLattice 2 (by norm_num)) j‖ := by
    simp only [w,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg hL]
  calc
    _ ≤ ‖w‖ := lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun j => (hbound j).trans_eq (hw j).symm)
    _ = L*‖puncturedLattice 2 (by norm_num)‖ := by
      rw [show w = (L : ℂ) • shift k (puncturedLattice 2 (by norm_num)) from rfl,norm_smul,
        Complex.norm_real,Real.norm_of_nonneg hL,norm_shift]
    _ ≤ L*2 := mul_le_mul_of_nonneg_left norm_puncturedLattice_two_le hL
    _ = _ := by ring

theorem norm_diagonal_sub_one_le (T : Coeff 2 →L[ℂ] Coeff 2) (k : ℤ) :
    ‖(T (lp.single 2 k 1)) k-1‖ ≤ ‖T-ContinuousLinearMap.id ℂ (Coeff 2)‖ := by
  let e : Coeff 2 := lp.single 2 k 1
  let S := T-ContinuousLinearMap.id ℂ (Coeff 2)
  have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (S e) k
  have hnorm := S.le_opNorm e
  have he : ‖e‖ = 1 := by simp only [e,lp.norm_single (by norm_num : 0 < (2 : ENNReal)),norm_one]
  have hSe : S e k = T e k-1 := by
    simp only [S,sub_apply,ContinuousLinearMap.id_apply,lp.coeFn_sub,Pi.sub_apply,
      e,lp.single_apply,Pi.single_apply,ite_true]
  rw [hSe] at hcoord
  rw [he,mul_one] at hnorm
  exact hcoord.trans hnorm

theorem diagonal_norm_lower_of_operator_close (T : Coeff 2 →L[ℂ] Coeff 2) (k : ℤ)
    (hT : ‖T-ContinuousLinearMap.id ℂ (Coeff 2)‖ < 1/2) :
    1/2 ≤ ‖(T (lp.single 2 k 1)) k‖ := by
  have hh := norm_diagonal_sub_one_le T k
  have ht := norm_sub_norm_le (1 : ℂ) ((T (lp.single 2 k 1)) k)
  rw [norm_one,norm_sub_rev] at ht
  linarith

end NLS.Coeff
