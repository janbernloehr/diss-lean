import NLS.KdV.HillFreePeriodDerivative
import NLS.ComplexAnalysis.BanachTaylorBounds
import NLS.KdV.HillFreePeriodDiagonalLimit
import NLS.SequenceSpaces.CompactRowMajorant

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem norm_fderiv_hilbertWeightedProduct_hillSeparated_le (n k : ℕ) (a : Coeff 2) :
    ‖fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight n k)) a‖ ≤
      2*Real.exp ((2/Real.pi^2)*(‖a‖+2)) := by
  let f := hilbertWeightedProduct (hillFreeSeparatedWeight n k)
  have hd : DifferentiableOn ℂ f (ball a (1+1)) :=
    (analyticOnNhd_hilbertWeightedProduct _).differentiableOn.mono (subset_univ _)
  have hb : ∀ b ∈ ball a (1+1), ‖f b‖ ≤ Real.exp ((2/Real.pi^2)*(‖a‖+2)) := by
    intro b hb
    have hba : ‖b-a‖ < 2 := by simpa only [mem_ball,dist_eq_norm,show (1 : ℝ)+1=2 by norm_num] using hb
    have hnorm : ‖b‖ ≤ ‖a‖+2 := by
      have ht := norm_add_le (b-a) a
      rw [sub_add_cancel] at ht
      linarith
    exact (norm_hilbertWeightedProduct_hillSeparated_le n k b).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnorm (by positivity)))
  simpa only [div_one] using norm_fderiv_le_of_ball_bound f a a 1 1 _
    (by norm_num) hd hb (mem_ball_self (by norm_num))

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem fderiv_hillFreeScaledPeriodSequence_coordinate (n : ℕ) (hn : 1 ≤ n)
    (a h : Coeff 2) (m : ℤ) :
    fderiv ℂ (hillFreeScaledPeriodSequence hq hr n hn) a h m =
      if 0 < m ∧ m ≠ (n : ℤ) then
        -h m*hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a
        -a m*fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat)) a h else 0 := by
  have hdiff := (analyticOnNhd_hillFreeScaledPeriodSequence hq hr n hn a (mem_univ _)).differentiableAt
  rw [Coeff.fderiv_apply_of_differentiableAt _ a h m hdiff]
  by_cases hm : 0 < m ∧ m ≠ (n : ℤ)
  · rw [if_pos hm]
    have hmt : 1 ≤ m.toNat := by omega
    have hnm : n ≠ m.toNat := by omega
    have hcast : (m.toNat : ℤ) = m := by omega
    have he : (fun b : Coeff 2 => hillFreeScaledPeriodSequence hq hr n hn b m) =
        (fun b : Coeff 2 => -b m*hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) b) := by
      funext b
      rw [hillFreeScaledPeriodSequence_apply,hillFreeScaledPeriodCoordinate,if_pos hm,
        hillFreeScaledHilbertPeriod_eq_product hq hr n m.toNat hn hmt hnm b,hcast]
    rw [he]
    have hA : HasFDerivAt (fun b : Coeff 2 => -b m)
        (-(lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m)) a := by
      convert! ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).hasFDerivAt (x := a)).neg using 1
    have hB := (analyticOnNhd_hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a
      (mem_univ _)).differentiableAt.hasFDerivAt
    have hd := (hA.mul hB).fderiv
    have heval (b : Coeff 2) : lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m b = b m := rfl
    have hh := congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hd
    simpa only [add_apply,smul_apply,neg_apply,heval,smul_eq_mul,neg_mul,
      sub_eq_add_neg,add_comm,Pi.mul_def,mul_comm] using hh
  · rw [if_neg hm]
    have he : (fun b : Coeff 2 => hillFreeScaledPeriodSequence hq hr n hn b m) = fun _ => 0 := by
      funext b
      rw [hillFreeScaledPeriodSequence_apply,hillFreeScaledPeriodCoordinate,if_neg hm]
    rw [he]
    have hc : HasFDerivAt (fun _ : Coeff 2 => (0 : ℂ))
        (0 : Coeff 2 →L[ℂ] ℂ) a := hasFDerivAt_const (0 : ℂ) a
    exact congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hc.fderiv

end NLS.KdV
