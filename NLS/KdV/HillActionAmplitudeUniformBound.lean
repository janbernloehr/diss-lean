import NLS.KdV.HillCanonicalActionAmplitude

/-! The positively normalized action amplitude is locally O(n^-1/2)
on ONE complex source neighborhood BEFORE ALL n. -/
noncomputable section
open Set Metric Complex
open scoped Classical
namespace NLS.KdV

theorem exists_local_uniform_hillHminusCanonicalActionAmplitude_bound (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusActionAmplitudeDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖hillHminusCanonicalActionAmplitude n a‖ ≤ C/Real.sqrt (n:ℕ) := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  let C := Real.sqrt B.bound/(2*Real.sqrt Real.pi)
  have hC : 0 < C := div_pos (Real.sqrt_pos.mpr B.bound_pos)
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos))
  refine ⟨B.source,B.source_open,hB,(fun a ha => mem_iUnion.mpr ⟨B,ha⟩),C,hC,?_⟩
  intro a ha n
  have hs := congrArg norm (hillHminusActionRatioSqrt_sq n a)
  rw [norm_pow] at hs
  have hnorm : ‖hillHminusActionRatioSqrt n a‖ ≤ Real.sqrt B.bound := by
    have hb := B.norm_bound a ha n
    have hsq := Real.sq_sqrt B.bound_pos.le
    have hn := Real.sqrt_nonneg B.bound
    nlinarith [norm_nonneg (hillHminusActionRatioSqrt n a)]
  have hd : 0 < 2*Real.sqrt Real.pi*Real.sqrt (n:ℕ) := hillActionAmplitude_denominator_pos n
  rw [hillHminusCanonicalActionAmplitude,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
  apply (div_le_div_of_nonneg_right hnorm hd.le).trans_eq
  dsimp only [C]
  rw [div_div]

end NLS.KdV
