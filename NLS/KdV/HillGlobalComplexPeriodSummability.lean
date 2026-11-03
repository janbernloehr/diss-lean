import NLS.KdV.HillBoundedComplexTailPeriodControl
import NLS.KdV.HillComplexPeriodSequence
import NLS.SequenceSpaces.PowerDecaySummability
import NLS.SequenceSpaces.FourierTail

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem norm_hillComplexScaledPeriodCoordinate_sub_free_le_on_tail (N n : ℕ) (a p : Coeff 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ k : ℕ, N ≤ k → n ≠ k →
      ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤
        D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ)) (m : ℤ) (hmcut : N ≤ m.natAbs) :
    ‖hillComplexScaledPeriodCoordinate hq hr n (a,p) m-hillFreeScaledPeriodCoordinate hq hr n a m‖ ≤
      (D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖)*‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖ := by
  by_cases hm : 0 < m ∧ m ≠ (n : ℤ)
  · have hmt : N ≤ m.toNat := by omega
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

theorem memℓp_hillComplexScaledPeriodCoordinate_global (n : ℕ) (hn : 1 ≤ n) (a p : Coeff 2) :
    Memℓp (hillComplexScaledPeriodCoordinate hq hr n (a,p)) 2 := by
  obtain ⟨N,hN,D,hD,hcontrol⟩ := exists_hillAbelianComplexPeriod_bounded_tail_control hq hr ‖p‖
  let g : ℤ → ℝ := fun m => (D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖)*‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖
  have hg : Memℓp g 2 := (lp.memℓp (Coeff.positivePuncturedLattice 2 (by norm_num))).norm.const_mul _
  have hdiff : Memℓp (fun m => hillComplexScaledPeriodCoordinate hq hr n (a,p) m-
      hillFreeScaledPeriodCoordinate hq hr n a m) 2 := by
    have ht := memlp_of_natAbs_eventual_bound 2 (by norm_num)
      (fun m => hillComplexScaledPeriodCoordinate hq hr n (a,p) m-hillFreeScaledPeriodCoordinate hq hr n a m)
      g (by simpa only [ENNReal.ofReal_ofNat] using hg) N (fun m hm =>
        norm_hillComplexScaledPeriodCoordinate_sub_free_le_on_tail hq hr N n a p D hD.le
          (fun k hk hnk => (hcontrol p le_rfl).2 n k hn hk hnk a) m hm)
    simpa only [ENNReal.ofReal_ofNat] using ht
  have hh := hdiff.add (lp.memℓp (hillFreeScaledPeriodSequence hq hr n hn a))
  simpa only [Pi.add_def,hillFreeScaledPeriodSequence_apply,sub_add_cancel] using hh

theorem hillComplexScaledPeriodSequence_apply_global (n : ℕ) (hn : 1 ≤ n) (t : Coeff 2 × Coeff 2) (m : ℤ) :
    hillComplexScaledPeriodSequence hq hr n t m = hillComplexScaledPeriodCoordinate hq hr n t m := by
  exact hillComplexScaledPeriodSequence_apply_of_mem hq hr n t
    (memℓp_hillComplexScaledPeriodCoordinate_global hq hr n hn t.1 t.2) m

end NLS.KdV
