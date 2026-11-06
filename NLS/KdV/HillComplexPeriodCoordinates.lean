import NLS.KdV.HillComplexPeriodControl
import NLS.KdV.HillFreePeriodSequence

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillComplexScaledPeriodCoordinate (n : ℕ) (t : Coeff 2 × Coeff 2) (m : ℤ) : ℂ :=
  if 0 < m ∧ m ≠ (n : ℤ) then
    (((freeHillValue m.toNat : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      hillAbelianComplexPeriod 0 hq hr n m.toNat t else 0

theorem norm_hillComplexScaledPeriodCoordinate_le (n : ℕ) (hn : 1 ≤ n) (a p : Coeff 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ k : ℕ, 1 ≤ k → n ≠ k →
      ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤
        D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ)) (m : ℤ) :
    ‖hillComplexScaledPeriodCoordinate hq hr n (a,p) m‖ ≤
      Real.exp ((2/Real.pi^2)*‖a‖)*‖a m‖ +
        (D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖)*‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖ := by
  by_cases hm : 0 < m ∧ m ≠ (n : ℤ)
  · have hmt : 1 ≤ m.toNat := by omega
    have hnm : n ≠ m.toNat := by omega
    have hcast : (m.toNat : ℤ) = m := by omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm.1
    have hlat : ‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖ = 1/(m.toNat : ℝ) := by
      rw [Coeff.positivePuncturedLattice_apply,if_pos hm.1,norm_inv,norm_intCast,abs_of_pos hmR]
      have he : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast hcast
      rw [he,one_div]
    have hfree := norm_hillFreeScaledPeriodCoordinate_le hq hr n hn a m
    have herr := hbound m.toNat hmt hnm
    have hdiff : hillComplexScaledPeriodCoordinate hq hr n (a,p) m-
        hillFreeScaledPeriodCoordinate hq hr n a m =
        (((freeHillValue m.toNat : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
          (hillAbelianComplexPeriod 0 hq hr n m.toNat (a,p)-hillAbelianHilbertPeriod 0 hq hr n m.toNat a) := by
      rw [hillComplexScaledPeriodCoordinate,if_pos hm,hillFreeScaledPeriodCoordinate,if_pos hm]
      ring
    have htri := norm_le_norm_sub_add (hillComplexScaledPeriodCoordinate hq hr n (a,p) m)
      (hillFreeScaledPeriodCoordinate hq hr n a m)
    rw [hdiff] at htri
    apply (htri.trans (add_le_add herr hfree)).trans_eq
    rw [hlat]
    ring
  · rw [hillComplexScaledPeriodCoordinate,if_neg hm,norm_zero]
    positivity

theorem memℓp_hillComplexScaledPeriodCoordinate (n : ℕ) (hn : 1 ≤ n) (a p : Coeff 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ k : ℕ, 1 ≤ k → n ≠ k →
      ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤
        D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ)) :
    Memℓp (hillComplexScaledPeriodCoordinate hq hr n (a,p)) 2 := by
  apply (((lp.memℓp a).norm.const_mul (Real.exp ((2/Real.pi^2)*‖a‖))).add
    ((lp.memℓp (Coeff.positivePuncturedLattice 2 (by norm_num))).norm.const_mul
      (D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖))).mono
  intro m
  exact norm_hillComplexScaledPeriodCoordinate_le hq hr n hn a p D hD hbound m

theorem norm_hillComplexScaledPeriodCoordinate_sub_free_le (n : ℕ) (a p : Coeff 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ k : ℕ, 1 ≤ k → n ≠ k →
      ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤
        D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ)) (m : ℤ) :
    ‖hillComplexScaledPeriodCoordinate hq hr n (a,p) m-hillFreeScaledPeriodCoordinate hq hr n a m‖ ≤
      (D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖)*‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖ := by
  by_cases hm : 0 < m ∧ m ≠ (n : ℤ)
  · have hmt : 1 ≤ m.toNat := by omega
    have hnm : n ≠ m.toNat := by omega
    have hcast : (m.toNat : ℤ) = m := by omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm.1
    have hlat : ‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖ = 1/(m.toNat : ℝ) := by
      rw [Coeff.positivePuncturedLattice_apply,if_pos hm.1,norm_inv,norm_intCast,abs_of_pos hmR]
      have he : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast hcast
      rw [he,one_div]
    rw [hillComplexScaledPeriodCoordinate,if_pos hm,hillFreeScaledPeriodCoordinate,if_pos hm,← mul_sub,hlat]
    exact (hbound m.toNat hmt hnm).trans_eq (by ring)
  · rw [hillComplexScaledPeriodCoordinate,if_neg hm,hillFreeScaledPeriodCoordinate,if_neg hm,
      sub_self,norm_zero]
    positivity

end NLS.KdV
