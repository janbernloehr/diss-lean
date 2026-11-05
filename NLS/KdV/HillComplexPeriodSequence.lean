import NLS.KdV.HillComplexPeriodCoordinates

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillComplexScaledPeriodSequence (n : ℕ) (t : Coeff 2 × Coeff 2) : Coeff 2 := by
  classical
  exact if h : Memℓp (hillComplexScaledPeriodCoordinate hq hr n t) 2 then
    ⟨hillComplexScaledPeriodCoordinate hq hr n t,h⟩ else 0

theorem hillComplexScaledPeriodSequence_apply_of_mem (n : ℕ) (t : Coeff 2 × Coeff 2)
    (ht : Memℓp (hillComplexScaledPeriodCoordinate hq hr n t) 2) (m : ℤ) :
    hillComplexScaledPeriodSequence hq hr n t m = hillComplexScaledPeriodCoordinate hq hr n t m := by
  rw [hillComplexScaledPeriodSequence,dif_pos ht]

theorem norm_hillComplexScaledPeriodSequence_sub_free_le (n : ℕ) (hn : 1 ≤ n) (a p : Coeff 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ k : ℕ, 1 ≤ k → n ≠ k →
      ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤
        D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ)) :
    ‖hillComplexScaledPeriodSequence hq hr n (a,p)-hillFreeScaledPeriodSequence hq hr n hn a‖ ≤
      2*D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖ := by
  have hmem := memℓp_hillComplexScaledPeriodCoordinate hq hr n hn a p D hD hbound
  let B := D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hnorm : ‖hillComplexScaledPeriodSequence hq hr n (a,p)-hillFreeScaledPeriodSequence hq hr n hn a‖ ≤
      ‖(B : ℂ) • Coeff.positivePuncturedLattice 2 (by norm_num)‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro m
    simpa only [lp.coeFn_sub,Pi.sub_apply,hillComplexScaledPeriodSequence_apply_of_mem hq hr n (a,p) hmem,
      hillFreeScaledPeriodSequence_apply,lp.coeFn_smul,Pi.smul_apply,norm_smul,norm_real,Real.norm_eq_abs,
      abs_of_nonneg hB] using norm_hillComplexScaledPeriodCoordinate_sub_free_le hq hr n a p D hD hbound m
  apply hnorm.trans
  rw [norm_smul,norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
  apply (mul_le_mul_of_nonneg_left Coeff.norm_positivePuncturedLattice_two_le hB).trans_eq
  dsimp only [B]
  ring

theorem norm_hillComplexScaledPeriodSequence_le (n : ℕ) (hn : 1 ≤ n) (a p : Coeff 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ k : ℕ, 1 ≤ k → n ≠ k →
      ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤
        D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ)) :
    ‖hillComplexScaledPeriodSequence hq hr n (a,p)‖ ≤
      Real.exp ((2/Real.pi^2)*‖a‖)*‖a‖+2*D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖ := by
  apply (norm_le_norm_sub_add (hillComplexScaledPeriodSequence hq hr n (a,p))
    (hillFreeScaledPeriodSequence hq hr n hn a)).trans
  exact (add_le_add (norm_hillComplexScaledPeriodSequence_sub_free_le hq hr n hn a p D hD hbound)
    (norm_hillFreeScaledPeriodSequence_le hq hr n hn a)).trans_eq (by ring)

end NLS.KdV
