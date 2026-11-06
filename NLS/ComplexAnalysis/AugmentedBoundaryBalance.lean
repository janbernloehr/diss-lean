import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.ComplexAnalysis



/-- Eliminate nontrivial augmented boundary data from an equal-diagonal
two-mode system, retaining the actual scalar boundary source. -/
theorem augmented_boundary_diagonal_balance
    (d bp bm ap am Bp Bm t u v J : ℂ)
    (h1 : d*u-bp*v+J*ap=0) (h2 : -bm*u+d*v+J*am=0)
    (h3 : Bp*u+Bm*v-J*t=0) (hne : u ≠ 0 ∨ v ≠ 0 ∨ J ≠ 0) :
    d*(Bp*ap+Bm*am+t*d) = t*bp*bm-(Bp*bp*am+Bm*bm*ap) := by
  let D := d*(Bp*ap+Bm*am+t*d)-t*bp*bm+(Bp*bp*am+Bm*bm*ap)
  have hu : D*u=0 := by
    dsimp only [D]
    linear_combination (d*t+am*Bm)*h1+(bp*t-ap*Bm)*h2+(bp*am+ap*d)*h3
  have hv : D*v=0 := by
    dsimp only [D]
    linear_combination (bm*t-am*Bp)*h1+(d*t+ap*Bp)*h2+(d*am+ap*bm)*h3
  have hJ : D*J=0 := by
    dsimp only [D]
    linear_combination (bm*Bm+d*Bp)*h1+(d*Bm+bp*Bp)*h2+(bp*bm-d^2)*h3
  have hD : D=0 := by
    rcases hne with hn | hn | hn
    · exact (mul_eq_zero.mp hu).resolve_right hn
    · exact (mul_eq_zero.mp hv).resolve_right hn
    · exact (mul_eq_zero.mp hJ).resolve_right hn
  dsimp only [D] at hD
  linear_combination hD

/-- Once the scalar boundary denominator is separated from zero, each
weighted diagonal is controlled by the two weighted off-diagonal entries. -/
theorem weighted_diagonal_le_of_augmented_boundary_balance
    (d bp bm ap am Bp Bm t : ℂ) (w D : ℝ) (hw : 0 ≤ w) (hD : 0 ≤ D)
    (hbalance : d*(Bp*ap+Bm*am+t*d) = t*bp*bm-(Bp*bp*am+Bm*bm*ap))
    (hden : 1 ≤ ‖Bp*ap+Bm*am+t*d‖)
    (hap : ‖ap‖ ≤ 2) (ham : ‖am‖ ≤ 2) (hBp : ‖Bp‖ ≤ 2) (hBm : ‖Bm‖ ≤ 2)
    (ht : ‖t‖ ≤ 1) (hbm : ‖bm‖ ≤ D) :
    w*‖d‖ ≤ (D+4)*(w*‖bp‖+w*‖bm‖) := by
  have hd : ‖d‖ ≤ ‖d*(Bp*ap+Bm*am+t*d)‖ := by
    rw [norm_mul]
    exact (mul_one ‖d‖).symm.le.trans (mul_le_mul_of_nonneg_left hden (norm_nonneg _))
  rw [hbalance] at hd
  have hb : ‖t*bp*bm‖ ≤ D*‖bp‖ := by
    rw [norm_mul,norm_mul]
    calc
      _ ≤ 1*‖bp‖*D := mul_le_mul (mul_le_mul_of_nonneg_right ht (norm_nonneg _)) hbm
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hp : ‖Bp*bp*am‖ ≤ 4*‖bp‖ := by
    rw [norm_mul,norm_mul]
    calc
      _ ≤ 2*‖bp‖*2 := mul_le_mul (mul_le_mul_of_nonneg_right hBp (norm_nonneg _)) ham
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hm : ‖Bm*bm*ap‖ ≤ 4*‖bm‖ := by
    rw [norm_mul,norm_mul]
    calc
      _ ≤ 2*‖bm‖*2 := mul_le_mul (mul_le_mul_of_nonneg_right hBm (norm_nonneg _)) hap
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hsum := (norm_sub_le (t*bp*bm) (Bp*bp*am+Bm*bm*ap)).trans
    (add_le_add le_rfl (norm_add_le _ _))
  have hfinal : ‖d‖ ≤ (D+4)*(‖bp‖+‖bm‖) := by
    nlinarith [mul_nonneg hD (norm_nonneg bm)]
  calc
    w*‖d‖ ≤ w*((D+4)*(‖bp‖+‖bm‖)) := mul_le_mul_of_nonneg_left hfinal hw
    _ = _ := by ring

/-- Small boundary row, source and trace errors separate the actual scalar
boundary denominator from zero with one fixed numerical margin. -/
theorem norm_augmented_boundary_denominator_ge_one
    (d ap am Bp Bm t : ℂ)
    (hap : ‖ap-1‖ ≤ 1/8) (ham : ‖am-1‖ ≤ 1/8)
    (hBp : ‖Bp-1‖ ≤ 1/8) (hBm : ‖Bm-1‖ ≤ 1/8)
    (htd : ‖t*d‖ ≤ 1/8) :
    1 ≤ ‖Bp*ap+Bm*am+t*d‖ ∧ ‖ap‖ ≤ 2 ∧ ‖am‖ ≤ 2 ∧ ‖Bp‖ ≤ 2 ∧ ‖Bm‖ ≤ 2 := by
  have ha : ‖ap‖ ≤ 2 := by
    have h := norm_le_norm_sub_add ap (1 : ℂ)
    rw [norm_one] at h
    linarith
  have hb : ‖am‖ ≤ 2 := by
    have h := norm_le_norm_sub_add am (1 : ℂ)
    rw [norm_one] at h
    linarith
  have hA : ‖Bp‖ ≤ 2 := by
    have h := norm_le_norm_sub_add Bp (1 : ℂ)
    rw [norm_one] at h
    linarith
  have hB : ‖Bm‖ ≤ 2 := by
    have h := norm_le_norm_sub_add Bm (1 : ℂ)
    rw [norm_one] at h
    linarith
  have hp : ‖Bp*ap-1‖ ≤ 3/8 := by
    rw [show Bp*ap-1=(Bp-1)*ap+(ap-1) by ring]
    have h := (norm_add_le ((Bp-1)*ap) (ap-1))
    rw [norm_mul] at h
    have hm := mul_le_mul hBp ha (norm_nonneg ap) (by norm_num : (0 : ℝ) ≤ 1/8)
    linarith
  have hm : ‖Bm*am-1‖ ≤ 3/8 := by
    rw [show Bm*am-1=(Bm-1)*am+(am-1) by ring]
    have h := (norm_add_le ((Bm-1)*am) (am-1))
    rw [norm_mul] at h
    have hm := mul_le_mul hBm hb (norm_nonneg am) (by norm_num : (0 : ℝ) ≤ 1/8)
    linarith
  have he : ‖Bp*ap+Bm*am+t*d-2‖ ≤ 7/8 := by
    rw [show Bp*ap+Bm*am+t*d-2=(Bp*ap-1)+(Bm*am-1)+t*d by ring]
    have h := (norm_add_le ((Bp*ap-1)+(Bm*am-1)) (t*d)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    linarith
  have hlo := norm_sub_norm_le (2 : ℂ) (Bp*ap+Bm*am+t*d)
  rw [norm_ofNat,norm_sub_rev] at hlo
  exact ⟨by linarith,ha,hb,hA,hB⟩

end NLS.ComplexAnalysis
