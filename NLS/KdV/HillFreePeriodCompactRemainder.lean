import NLS.KdV.HillFreePeriodCompactDiagonal
import NLS.KdV.HillFreePeriodDerivativeRows

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem isCompactOperator_fderiv_hillFreeScaledPeriodSequence_add_projection
    (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2) :
    IsCompactOperator (fderiv ℂ (hillFreeScaledPeriodSequence hq hr n hn) a+
      Coeff.positiveDeletedProjection 2 (n : ℤ)) := by
  let D := Coeff.multiplierCLM (p := 2) (hillFreePeriodDiagonalCorrection n a)
  let K := fderiv ℂ (hillFreeScaledPeriodSequence hq hr n hn) a+
      Coeff.positiveDeletedProjection 2 (n : ℤ)+D
  let C := 2*Real.exp ((2/Real.pi^2)*(‖a‖+2))
  let b : Coeff 2 := (C : ℂ) • a
  have hK : IsCompactOperator K := by
    apply Coeff.isCompactOperator_of_rowMajorant (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) K b
    intro m h
    change ‖(fderiv ℂ (hillFreeScaledPeriodSequence hq hr n hn) a h+
        Coeff.positiveDeletedProjection 2 (n : ℤ) h+D h) m‖ ≤ ‖b m‖*‖h‖
    simp only [lp.coeFn_add,Pi.add_apply]
    rw [fderiv_hillFreeScaledPeriodSequence_coordinate hq hr n hn,
      Coeff.positiveDeletedProjection_apply]
    have hD : D h m = (if 0 < m ∧ m ≠ (n : ℤ) then
        hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a-1 else 0)*h m := rfl
    rw [hD]
    by_cases hm : 0 < m ∧ m ≠ (n : ℤ)
    · rw [if_pos hm,if_pos hm,if_pos hm]
      have he : -h m*hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a-
          a m*fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat)) a h+
          h m+(hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a-1)*h m =
          -(a m*fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat)) a h) := by ring
      rw [he,norm_neg,norm_mul]
      have hnorm : ‖fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat)) a h‖ ≤ C*‖h‖ :=
        ((fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat)) a).le_opNorm h).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_hilbertWeightedProduct_hillSeparated_le n m.toNat a) (norm_nonneg h))
      have hb : ‖b m‖ = C*‖a m‖ := by
        simp only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,norm_real,
          Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ C by dsimp [C];positivity)]
      rw [hb]
      nlinarith [mul_le_mul_of_nonneg_left hnorm (norm_nonneg (a m))]
    · rw [if_neg hm,if_neg hm,if_neg hm,zero_mul,zero_add,add_zero,norm_zero]
      positivity
  have hD : IsCompactOperator D := isCompactOperator_hillFreePeriodDiagonalCorrection n a
  have he : fderiv ℂ (hillFreeScaledPeriodSequence hq hr n hn) a+
      Coeff.positiveDeletedProjection 2 (n : ℤ) = K-D := by dsimp [K];abel
  rw [he]
  exact hK.sub hD

end NLS.KdV
