import NLS.KdV.HillFreePeriodSequence
import NLS.SequenceSpaces.PositiveDeletedProjection
import NLS.SequenceSpaces.BoundedCoordinateDifferentiable
import NLS.ComplexAnalysis.HilbertPositiveProducts

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem fderiv_hillFreeScaledPeriodSequence_zero_coordinate (n : ℕ) (hn : 1 ≤ n)
    (h : Coeff 2) (m : ℤ) :
    fderiv ℂ (hillFreeScaledPeriodSequence hq hr n hn) 0 h m =
      if 0 < m ∧ m ≠ (n : ℤ) then -h m else 0 := by
  have hdiff := (analyticOnNhd_hillFreeScaledPeriodSequence hq hr n hn 0 (mem_univ _)).differentiableAt
  rw [Coeff.fderiv_apply_of_differentiableAt _ 0 h m hdiff]
  by_cases hm : 0 < m ∧ m ≠ (n : ℤ)
  · rw [if_pos hm]
    have hmt : 1 ≤ m.toNat := by omega
    have hnm : n ≠ m.toNat := by omega
    have hcast : (m.toNat : ℤ) = m := by omega
    have he : (fun a : Coeff 2 => hillFreeScaledPeriodSequence hq hr n hn a m) =
        (fun a : Coeff 2 => -a m*hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a) := by
      funext a
      rw [hillFreeScaledPeriodSequence_apply,hillFreeScaledPeriodCoordinate,if_pos hm,
        hillFreeScaledHilbertPeriod_eq_product hq hr n m.toNat hn hmt hnm a,hcast]
    rw [he]
    have hA := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).hasFDerivAt (x := (0 : Coeff 2))
    have hB := (analyticOnNhd_hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) 0
      (mem_univ _)).differentiableAt.hasFDerivAt
    have hAz : HasFDerivAt (fun a : Coeff 2 => -a m)
        (-(lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m)) (0 : Coeff 2) := by
      convert! hA.neg using 1
    have hd : HasFDerivAt
        (fun a : Coeff 2 => -a m*hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a)
        (-(lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m)) (0 : Coeff 2) := by
      convert! hAz.mul hB using 1
      simp [hilbertWeightedProduct_zero]
    exact congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hd.fderiv
  · rw [if_neg hm]
    have he : (fun a : Coeff 2 => hillFreeScaledPeriodSequence hq hr n hn a m) = fun _ => 0 := by
      funext a
      rw [hillFreeScaledPeriodSequence_apply,hillFreeScaledPeriodCoordinate,if_neg hm]
    rw [he]
    have hc : HasFDerivAt (fun _ : Coeff 2 => (0 : ℂ))
        (0 : Coeff 2 →L[ℂ] ℂ) (0 : Coeff 2) := hasFDerivAt_const (0 : ℂ) (0 : Coeff 2)
    exact congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hc.fderiv

theorem fderiv_hillFreeScaledPeriodSequence_zero (n : ℕ) (hn : 1 ≤ n) :
    fderiv ℂ (hillFreeScaledPeriodSequence hq hr n hn) 0 =
      -Coeff.positiveDeletedProjection 2 (n : ℤ) := by
  ext h m
  rw [fderiv_hillFreeScaledPeriodSequence_zero_coordinate,neg_apply,
    lp.coeFn_neg,Pi.neg_apply,Coeff.positiveDeletedProjection_apply]
  split_ifs
  · rfl
  · simp only [neg_zero]

theorem fderiv_hillFreeScaledPeriodSequence_zero_on_supported (n : ℕ) (hn : 1 ≤ n)
    (h : Coeff 2) (hh : ∀ m : ℤ, m ≤ 0 ∨ m = (n : ℤ) → h m = 0) :
    fderiv ℂ (hillFreeScaledPeriodSequence hq hr n hn) 0 h = -h := by
  rw [fderiv_hillFreeScaledPeriodSequence_zero,neg_apply,
    (Coeff.positiveDeletedProjection_eq_self_iff 2 (n : ℤ) h).mpr hh]

theorem hillFreeScaledPeriodSequence_zero (n : ℕ) (hn : 1 ≤ n) :
    hillFreeScaledPeriodSequence hq hr n hn 0 = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm
  · simpa only [norm_zero,mul_zero] using norm_hillFreeScaledPeriodSequence_le hq hr n hn 0
  · exact norm_nonneg _

end NLS.KdV
