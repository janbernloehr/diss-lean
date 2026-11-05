import NLS.KdV.HillFreeScaledPeriodIdentity
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillFreeScaledPeriodCoordinate (n : ℕ) (a : Coeff 2) (m : ℤ) : ℂ :=
  if 0 < m ∧ m ≠ (n : ℤ) then
    (((freeHillValue m.toNat : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      hillAbelianHilbertPeriod 0 hq hr n m.toNat a else 0

theorem norm_hillFreeScaledPeriodCoordinate_le (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2) (m : ℤ) :
    ‖hillFreeScaledPeriodCoordinate hq hr n a m‖ ≤
      Real.exp ((2/Real.pi^2)*‖a‖)*‖a m‖ := by
  unfold hillFreeScaledPeriodCoordinate
  split_ifs with hm
  · have hmt : 1 ≤ m.toNat := by omega
    have hnm : n ≠ m.toNat := by omega
    have hcast : (m.toNat : ℤ) = m := by omega
    rw [hillFreeScaledHilbertPeriod_eq_product hq hr n m.toNat hn hmt hnm a,
      norm_mul,norm_neg,hcast]
    have h := mul_le_mul_of_nonneg_left (norm_hilbertWeightedProduct_hillSeparated_le n m.toNat a)
      (norm_nonneg (a m))
    exact h.trans_eq (by ring)
  · rw [norm_zero]
    positivity

def hillFreeScaledPeriodSequence (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2) : Coeff 2 :=
  ⟨hillFreeScaledPeriodCoordinate hq hr n a,by
    apply ((lp.memℓp a).norm.const_mul (Real.exp ((2/Real.pi^2)*‖a‖))).mono
    exact norm_hillFreeScaledPeriodCoordinate_le hq hr n hn a⟩

theorem hillFreeScaledPeriodSequence_apply (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2) (m : ℤ) :
    hillFreeScaledPeriodSequence hq hr n hn a m = hillFreeScaledPeriodCoordinate hq hr n a m := rfl

theorem norm_hillFreeScaledPeriodSequence_le (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2) :
    ‖hillFreeScaledPeriodSequence hq hr n hn a‖ ≤ Real.exp ((2/Real.pi^2)*‖a‖)*‖a‖ := by
  have h : ‖hillFreeScaledPeriodSequence hq hr n hn a‖ ≤
      ‖(Real.exp ((2/Real.pi^2)*‖a‖) : ℂ) • a‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro m
    simpa only [hillFreeScaledPeriodSequence_apply,lp.coeFn_smul,Pi.smul_apply,norm_smul,
      norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
        norm_hillFreeScaledPeriodCoordinate_le hq hr n hn a m
  simpa only [norm_smul,norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using h

theorem analyticOnNhd_hillFreeScaledPeriod_coordinate (n : ℕ) (hn : 1 ≤ n) (m : ℤ) :
    AnalyticOnNhd ℂ (fun a : Coeff 2 => hillFreeScaledPeriodSequence hq hr n hn a m) univ := by
  by_cases hm : 0 < m ∧ m ≠ (n : ℤ)
  · have he : (fun a : Coeff 2 => hillFreeScaledPeriodSequence hq hr n hn a m) =
        (fun a => (((freeHillValue m.toNat : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
          hillAbelianHilbertPeriod 0 hq hr n m.toNat a) := by
      funext a
      rw [hillFreeScaledPeriodSequence_apply,hillFreeScaledPeriodCoordinate,if_pos hm]
    rw [he]
    exact analyticOnNhd_const.mul (analyticOnNhd_hillAbelianHilbertPeriod 0 hq hr n m.toNat (by omega))
  · have he : (fun a : Coeff 2 => hillFreeScaledPeriodSequence hq hr n hn a m) = fun _ => 0 := by
      funext a
      rw [hillFreeScaledPeriodSequence_apply,hillFreeScaledPeriodCoordinate,if_neg hm]
    rw [he]
    exact analyticOnNhd_const

theorem analyticOnNhd_hillFreeScaledPeriodSequence (n : ℕ) (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (hillFreeScaledPeriodSequence hq hr n hn) univ := by
  intro a _
  let R := ‖a‖+1
  let M := Real.exp ((2/Real.pi^2)*R)*R
  have hcoord (m : ℤ) : AnalyticOnNhd ℂ
      (fun b : Coeff 2 => hillFreeScaledPeriodSequence hq hr n hn b m) (ball a 1) :=
    (analyticOnNhd_hillFreeScaledPeriod_coordinate hq hr n hn m).mono (subset_univ _)
  have hbound (b : Coeff 2) (hb : b ∈ ball a 1) :
      ‖hillFreeScaledPeriodSequence hq hr n hn b‖ ≤ M := by
    have hd : ‖b-a‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hb
    have hbR : ‖b‖ ≤ R := by
      have h := norm_add_le (b-a) a
      rw [sub_add_cancel] at h
      dsimp only [R]
      linarith
    apply (norm_hillFreeScaledPeriodSequence_le hq hr n hn b).trans
    exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbR (by positivity)))
      hbR (norm_nonneg _) (Real.exp_nonneg _)
  exact Coeff.analyticOnNhd_of_bounded_coordinatewise
    (hillFreeScaledPeriodSequence hq hr n hn) isOpen_ball hcoord M hbound a (mem_ball_self (by norm_num))

end NLS.KdV
