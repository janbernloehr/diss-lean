import NLS.SequenceSpaces.WeightedReciprocalKernel
import NLS.SequenceSpaces.SobolevDerivative
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exact polynomial orders for the punctured reciprocal kernel.
The endpoint interval [-1,1] has a uniform bound; every order >-1
also has vanishing individual columns at positive infinity. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

def sharpReciprocalKernel (r : ℝ) (n k : ℤ) : ℝ :=
  Weight.sobolev (-r) n*Weight.sobolev r k*‖puncturedLattice 2 (by norm_num) (n-k)‖

theorem sharpReciprocalKernel_nonnegative (r : ℝ) (n k : ℤ) :
    0≤sharpReciprocalKernel r n k :=
  mul_nonneg (mul_nonneg ((Weight.sobolev (-r)).positive n).le ((Weight.sobolev r).positive k).le) (norm_nonneg _)

theorem sobolev_shift_ratio_bound (r : ℝ) (hr0 : -1≤r) (hr1 : r≤1) (n k : ℤ) :
    Weight.sobolev r k≤Weight.sobolev r n*Weight.sobolev 1 (n-k) := by
  by_cases hr : 0≤r
  · have h := (SpectralWeight.sobolev r hr).add_le n (k-n)
    simp only [SpectralWeight.sobolev_apply,add_sub_cancel] at h
    have hm := Weight.sobolev_mono hr1 (k-n)
    have he : Weight.sobolev 1 (k-n)=Weight.sobolev 1 (n-k) := by simp [abs_sub_comm]
    exact h.trans (by rw [←he];exact mul_le_mul_of_nonneg_left hm ((Weight.sobolev r).positive n).le)
  · have hd : 0≤ -r := by linarith
    have h := (SpectralWeight.sobolev (-r) hd).add_le k (n-k)
    simp only [SpectralWeight.sobolev_apply,add_sub_cancel] at h
    have hm := Weight.sobolev_mono (by linarith : -r≤1) (n-k)
    have h' : Weight.sobolev (-r) n≤Weight.sobolev (-r) k*Weight.sobolev 1 (n-k) :=
      h.trans (mul_le_mul_of_nonneg_left hm ((Weight.sobolev (-r)).positive k).le)
    have hi (j : ℤ) : Weight.sobolev (-r) j=(Weight.sobolev r j)⁻¹ := by
      simp only [Weight.sobolev_apply,Real.rpow_neg (by positivity : (0 : ℝ)≤1+|(j : ℝ)|)]
    rw [hi n,hi k] at h'
    have hdiv : 1/Weight.sobolev r n≤Weight.sobolev 1 (n-k)/Weight.sobolev r k := by
      simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using h'
    simpa only [one_mul,mul_comm] using
      (div_le_div_iff₀ ((Weight.sobolev r).positive n) ((Weight.sobolev r).positive k)).mp hdiv

theorem sharpReciprocalKernel_le_two (r : ℝ) (hr0 : -1≤r) (hr1 : r≤1) (n k : ℤ) :
    sharpReciprocalKernel r n k≤2 := by
  have hw := sobolev_shift_ratio_bound r hr0 hr1 n k
  have hi : Weight.sobolev (-r) n*Weight.sobolev r n=1 := by
    rw [←Weight.sobolev_add,neg_add_cancel,Weight.sobolev_zero_apply]
  have hk := weighted_puncturedLattice_bound 1 (n-k)
  norm_num only [sub_self,Weight.sobolev_zero_apply,div_one] at hk
  unfold sharpReciprocalKernel
  calc
    _≤Weight.sobolev (-r) n*(Weight.sobolev r n*Weight.sobolev 1 (n-k))*
      ‖puncturedLattice 2 (by norm_num) (n-k)‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw ((Weight.sobolev (-r)).positive n).le) (norm_nonneg _)
    _=Weight.sobolev 1 (n-k)*‖puncturedLattice 2 (by norm_num) (n-k)‖ := by rw [←mul_assoc,hi,one_mul]
    _≤2 := hk

theorem sharpReciprocalKernel_column_bound (r : ℝ) (n k : ℤ) :
    sharpReciprocalKernel r n k≤
      (2*Weight.sobolev 1 k*Weight.sobolev r k)*Weight.sobolev (-r-1) n := by
  have h := (SpectralWeight.sobolev 1 (by norm_num)).add_le (n-k) k
  simp only [SpectralWeight.sobolev_apply,sub_add_cancel] at h
  have hk := weighted_puncturedLattice_bound 0 (n-k)
  simp only [Weight.sobolev_zero_apply,one_mul,sub_zero] at hk
  have hb : ‖puncturedLattice 2 (by norm_num) (n-k)‖≤2*Weight.sobolev 1 k/Weight.sobolev 1 n := by
    apply hk.trans
    apply (div_le_div_iff₀ ((Weight.sobolev 1).positive _) ((Weight.sobolev 1).positive _)).mpr
    nlinarith
  unfold sharpReciprocalKernel
  apply (mul_le_mul_of_nonneg_left hb
    (mul_nonneg ((Weight.sobolev (-r)).positive n).le ((Weight.sobolev r).positive k).le)).trans_eq
  rw [show -r-1=-r+(-1) by ring,Weight.sobolev_add]
  have hi : Weight.sobolev (-1) n=(Weight.sobolev 1 n)⁻¹ := by simp [Real.rpow_neg_one]
  rw [hi,div_eq_mul_inv]
  ring

theorem tendsto_sharpReciprocalKernel_column (r : ℝ) (hr : -1<r) (k : ℤ) :
    Tendsto (fun n : ℕ => sharpReciprocalKernel r (n : ℤ) k) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => Weight.sobolev (-r-1) (n : ℤ)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ)+n) atTop atTop :=
      Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    have hp := (tendsto_rpow_neg_atTop (by linarith : 0<r+1)).comp hbase
    simpa only [Function.comp_def,Weight.sobolev_apply,Int.cast_natCast,Nat.abs_cast,neg_add_rev,neg_neg,
      show -(r+1)=-r-1 by ring] using hp
  have hb := ht.const_mul (2*Weight.sobolev 1 k*Weight.sobolev r k)
  rw [mul_zero] at hb
  exact squeeze_zero (fun n => sharpReciprocalKernel_nonnegative r n k)
    (fun n => sharpReciprocalKernel_column_bound r n k) hb

end NLS.Coeff
