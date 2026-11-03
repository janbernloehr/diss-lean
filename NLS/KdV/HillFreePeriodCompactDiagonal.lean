import NLS.KdV.HillFreePeriodDiagonalLimit
import NLS.SequenceSpaces.Compact

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



def hillFreePeriodDiagonalCorrection (n : ℕ) (a : Coeff 2) : Coeff ⊤ :=
  ⟨fun m => if 0 < m ∧ m ≠ (n : ℤ) then
      hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a-1 else 0, by
    apply memℓp_infty
    refine ⟨Real.exp ((2/Real.pi^2)*‖a‖)+1,?_⟩
    rintro _ ⟨m,rfl⟩
    dsimp only
    split_ifs
    · exact (norm_sub_le _ _).trans (by
        simpa only [norm_one,add_comm] using add_le_add_right
          (norm_hilbertWeightedProduct_hillSeparated_le n m.toNat a) 1)
    · rw [norm_zero]
      positivity⟩

theorem isCompactOperator_hillFreePeriodDiagonalCorrection (n : ℕ) (a : Coeff 2) :
    IsCompactOperator (Coeff.multiplierCLM (p := 2) (hillFreePeriodDiagonalCorrection n a)) := by
  apply Coeff.isCompactOperator_multiplierCLM
  intro ε hε
  have ht : Tendsto (fun k : ℕ =>
      hilbertWeightedProduct (hillFreeSeparatedWeight n k) a-1) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_hilbertWeightedProduct_hillFreeSeparatedWeight n a).sub_const 1
  obtain ⟨K,hK⟩ := Metric.tendsto_atTop.mp ht ε hε
  refine ⟨Finset.Icc (-(K : ℤ)) K,?_⟩
  intro m hm
  change ‖if 0 < m ∧ m ≠ (n : ℤ) then
    hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a-1 else 0‖ ≤ ε
  split_ifs with hpos
  · have hmk : K ≤ m.toNat := by
      simp only [Finset.mem_Icc] at hm
      omega
    simpa only [dist_eq_norm,sub_zero] using (hK m.toNat hmk).le
  · simpa only [norm_zero] using hε.le

end NLS.KdV
