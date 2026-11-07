import NLS.KdV.HillOffIndexBoundedSequence
import NLS.KdV.HillAbelianCartesian

/-! Uniform ALL-n bounds for the actual infinite phase multipliers.
They transfer estimates on the intrinsic diagonal factors to the complete
Abelian factors. The action amplitude and diagonal estimate are separate. -/
noncomputable section
open Set Metric Complex
open scoped Classical
namespace NLS.KdV

theorem exists_local_uniform_offIndex_phase_exponential_bound (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexBoundedDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusOffIndexBoundedDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖Complex.exp (I*hillHminusOffIndexAbelianCorrection n a)‖ ≤ C ∧
          ‖Complex.exp (-I*hillHminusOffIndexAbelianCorrection n a)‖ ≤ C := by
  obtain ⟨U,hU,hqU,hUW,R,_,hbound⟩ := exists_locally_uniform_hillHminusOffIndexAbelianCorrection_bound q hq
  refine ⟨U,hU,hqU,hUW,Real.exp R,Real.exp_pos _,?_⟩
  intro a ha n
  have hb := (hbound a ha n).2
  constructor
  · rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    apply (Complex.re_le_norm _).trans
    simpa only [norm_mul,norm_I,one_mul] using hb
  · rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    apply (Complex.re_le_norm _).trans
    simpa only [norm_mul,norm_neg,norm_I,one_mul] using hb

theorem exists_local_uniform_complete_Abelian_diagonal_multiplier_bound (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexBoundedDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusOffIndexBoundedDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖hillHminusAbelianCartesianPlus n a‖ ≤ C*‖hillHminusDiagonalCartesianPlus n a‖ ∧
          ‖hillHminusAbelianCartesianMinus n a‖ ≤ C*‖hillHminusDiagonalCartesianMinus n a‖ := by
  obtain ⟨U,hU,hqU,hUW,C,hC,hb⟩ := exists_local_uniform_offIndex_phase_exponential_bound q hq
  refine ⟨U,hU,hqU,hUW,C,hC,?_⟩
  intro a ha n
  have h := hb a ha n
  constructor
  · simpa only [hillHminusAbelianCartesianPlus,norm_mul,mul_comm C] using
      mul_le_mul_of_nonneg_left h.1 (norm_nonneg (hillHminusDiagonalCartesianPlus n a))
  · simpa only [hillHminusAbelianCartesianMinus,norm_mul,mul_comm C] using
      mul_le_mul_of_nonneg_left h.2 (norm_nonneg (hillHminusDiagonalCartesianMinus n a))

end NLS.KdV
