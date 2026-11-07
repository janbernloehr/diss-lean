import NLS.KdV.HillFreeMultiplierBounds
import NLS.SequenceSpaces.PositiveCoordinateAnalytic
import NLS.KdV.HillFreeScaledPeriodIdentity
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! The ACTUAL nonlinear weighted free Hill period equation with
values in the original positive inverse-index l2 space. Uniform
multiplier bounds justify membership and a norm estimate before ALL n. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem memlp_hillFreePeriodEquation (n : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    Memℓp (fun m : ℕ+ => hillFreePeriodEquationRow n m (hillFreePeriodCircle m) d) 2 := by
  apply ((lp.memℓp d).norm.const_mul (Real.exp (hillFreeInteractionConstant*‖d‖))).mono
  intro m
  simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))] using
    norm_hillFreePeriodEquationRow_le n m (hillFreePeriodCircle m) d

def hillFreePeriodEquation (n : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) : lp (fun _ : ℕ+ => ℂ) 2 :=
  ⟨fun m => hillFreePeriodEquationRow n m (hillFreePeriodCircle m) d,memlp_hillFreePeriodEquation n d⟩

theorem hillFreePeriodEquation_apply (n m : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillFreePeriodEquation n d m = hillFreePeriodEquationRow n m (hillFreePeriodCircle m) d := rfl

theorem hillFreePeriodEquation_apply_any_circle (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ))
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillFreePeriodEquation n d m = hillFreePeriodEquationRow n m D d := by
  rw [hillFreePeriodEquation_apply,hillFreePeriodEquationRow_factor,hillFreePeriodEquationRow_factor]

theorem norm_hillFreePeriodEquation_le (n : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    ‖hillFreePeriodEquation n d‖ ≤ Real.exp (hillFreeInteractionConstant*‖d‖)*‖d‖ := by
  have h : ‖hillFreePeriodEquation n d‖ ≤ ‖(Real.exp (hillFreeInteractionConstant*‖d‖):ℂ) • d‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro m
    change ‖hillFreePeriodEquationRow n m (hillFreePeriodCircle m) d‖ ≤
      ‖(Real.exp (hillFreeInteractionConstant*‖d‖):ℂ)*d m‖
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact norm_hillFreePeriodEquationRow_le n m _ d
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using h

theorem norm_hillFreePeriodEquation_sub_id_le (n : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    ‖hillFreePeriodEquation n d-d‖ ≤ (Real.exp (hillFreeInteractionConstant*‖d‖)-1)*‖d‖ := by
  let a := Real.exp (hillFreeInteractionConstant*‖d‖)-1
  have ha : 0 ≤ a := sub_nonneg.mpr
    (Real.one_le_exp (mul_nonneg hillFreeInteractionConstant_nonneg (norm_nonneg _)))
  have h : ‖hillFreePeriodEquation n d-d‖ ≤ ‖(a:ℂ) • d‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro m
    change ‖hillFreePeriodEquationRow n m (hillFreePeriodCircle m) d-d m‖ ≤ ‖(a:ℂ)*d m‖
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha]
    exact norm_hillFreePeriodEquationRow_sub_coordinate_le n m _ d
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha] using h

theorem hillFreePeriodEquation_zero (n : ℕ+) : hillFreePeriodEquation n 0 = 0 := by
  ext m
  exact hillFreePeriodEquationRow_zero n m _

theorem analyticAt_hillFreePeriodEquation (n : ℕ+) (c : lp (fun _ : ℕ+ => ℂ) 2) :
    AnalyticAt ℂ (hillFreePeriodEquation n) c := by
  let R := ‖c‖+1
  have hcoord (m : ℕ+) : AnalyticOnNhd ℂ (fun d => hillFreePeriodEquation n d m) (ball c 1) := by
    intro d _
    exact analyticAt_hillFreePeriodEquationRow n m _ d
  have hbound (d : lp (fun _ : ℕ+ => ℂ) 2) (hd : d ∈ ball c 1) :
      ‖hillFreePeriodEquation n d‖ ≤ Real.exp (hillFreeInteractionConstant*R)*R := by
    have hdR : ‖d‖ ≤ R := by
      have he : ‖d-c‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hd
      have hn := norm_le_norm_sub_add d c
      dsimp only [R]
      linarith
    exact (norm_hillFreePeriodEquation_le n d).trans
      (mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdR hillFreeInteractionConstant_nonneg))
        hdR (norm_nonneg _) (Real.exp_pos _).le)
  exact (LpSequence.analyticOnNhd_positiveL2_of_bounded_coordinatewise (hillFreePeriodEquation n)
    isOpen_ball hcoord (Real.exp (hillFreeInteractionConstant*R)*R) hbound) c (mem_ball_self (by norm_num))

end NLS.KdV

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
