import NLS.KdV.HillGlobalComplexPeriodSummability

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillComplexScaledTailPeriodSequence (N n : ℕ) (t : Coeff 2 × Coeff 2) : Coeff 2 :=
  Coeff.fourierTail N (hillComplexScaledPeriodSequence hq hr n t)

theorem hillComplexScaledTailPeriodSequence_apply
    (N n : ℕ) (hn : 1 ≤ n) (t : Coeff 2 × Coeff 2) (m : ℤ) :
    hillComplexScaledTailPeriodSequence hq hr N n t m =
      if N ≤ m.natAbs then hillComplexScaledPeriodCoordinate hq hr n t m else 0 := by
  rw [hillComplexScaledTailPeriodSequence,Coeff.fourierTail_apply,
    hillComplexScaledPeriodSequence_apply_global hq hr n hn t m]

theorem norm_hillComplexScaledTailPeriodSequence_sub_free_le
    (N n : ℕ) (hn : 1 ≤ n) (a p : Coeff 2) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ k : ℕ, N ≤ k → n ≠ k →
      ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤
        D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ)) :
    ‖hillComplexScaledTailPeriodSequence hq hr N n (a,p)-
      Coeff.fourierTail N (hillFreeScaledPeriodSequence hq hr n hn a)‖ ≤
        2*D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖ := by
  let B : ℝ := D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hnorm : ‖hillComplexScaledTailPeriodSequence hq hr N n (a,p)-
      Coeff.fourierTail N (hillFreeScaledPeriodSequence hq hr n hn a)‖ ≤
        ‖(B : ℂ) • Coeff.positivePuncturedLattice 2 (by norm_num)‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro m
    rw [lp.coeFn_sub,Pi.sub_apply,hillComplexScaledTailPeriodSequence_apply hq hr N n hn,
      Coeff.fourierTail_apply,hillFreeScaledPeriodSequence_apply]
    by_cases hm : N ≤ m.natAbs
    · simp only [if_pos hm]
      simpa only [lp.coeFn_smul,Pi.smul_apply,norm_smul,norm_real,Real.norm_eq_abs,abs_of_nonneg hB] using
        norm_hillComplexScaledPeriodCoordinate_sub_free_le_on_tail hq hr N n a p D hD hbound m hm
    · simp only [if_neg hm,sub_self,norm_zero]
      exact norm_nonneg _
  apply hnorm.trans
  rw [norm_smul,norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
  apply (mul_le_mul_of_nonneg_left Coeff.norm_positivePuncturedLattice_two_le hB).trans_eq
  dsimp only [B]
  ring

theorem norm_hillComplexScaledTailPeriodSequence_le
    (N n : ℕ) (hn : 1 ≤ n) (a p : Coeff 2) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ k : ℕ, N ≤ k → n ≠ k →
      ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤
        D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ)) :
    ‖hillComplexScaledTailPeriodSequence hq hr N n (a,p)‖ ≤
      Real.exp ((2/Real.pi^2)*‖a‖)*‖a‖+2*D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖ := by
  apply (norm_le_norm_sub_add (hillComplexScaledTailPeriodSequence hq hr N n (a,p))
    (Coeff.fourierTail N (hillFreeScaledPeriodSequence hq hr n hn a))).trans
  have htail := (Coeff.norm_fourierTail_le (by norm_num : (2 : ℝ≥0∞) ≠ 0) N
    (hillFreeScaledPeriodSequence hq hr n hn a)).trans (norm_hillFreeScaledPeriodSequence_le hq hr n hn a)
  exact (add_le_add (norm_hillComplexScaledTailPeriodSequence_sub_free_le hq hr N n hn a p D hD hbound) htail).trans_eq (by ring)

end NLS.KdV
