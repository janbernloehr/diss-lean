import NLS.KdV.HillMiuraActionReflection
import NLS.ZakharovShabat.SourceInverseActionCauchySchwarz

/-! On EVERY actual signed noncentral Miura gap, frequency divided by
its original index is strictly positive. Thus the actual inverse/direct
gap moments satisfy Cauchy--Schwarz even at collapsed positive gaps. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

theorem hillMiura_gap_coordinate_div_index_pos (u : PeriodOneRealL2) (n : ℤ) (hn : n ≠ 0) (θ : ℝ) :
    0 < realGapAffinePoint (by simp) (by norm_num) (hillMiuraDiagonal u.val) n (Real.cos θ)/(n:ℝ) := by
  have hb := realGapAffinePoint_cos_mem_Icc (by simp) (by norm_num) (hillMiuraRealSource u) n θ
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · apply div_pos_of_neg_of_neg
    · exact hb.2.trans_lt (hillMiura_negative_gap_right_neg u n hneg)
    · exact_mod_cast hneg
  · apply div_pos
    · exact (hillMiura_positive_gap_left_pos u n hpos).trans_le hb.1
    · exact_mod_cast hpos

/-- The normalized signed per-gap inverse action inequality is unconditional
for EVERY genuine real L2 lift and EVERY nonzero original Dirac index. -/
theorem hillMiura_inverseAction_CauchySchwarz (u : PeriodOneRealL2) (n : ℤ) (hn : n ≠ 0) :
    (sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 0)^2 ≤
      ((n:ℝ)*sourceRealInverseAction (by simp) (by norm_num) (hillMiuraRealSource u) n)*
        (sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1/(n:ℝ)) :=
  source_inverseAction_CauchySchwarz (by simp) (by norm_num) (hillMiuraRealSource u) n
    (hillMiura_gap_coordinate_div_index_pos u n hn)


theorem hillMiura_inverseAction_nonneg (u : PeriodOneRealL2) (n : ℤ) (hn : n ≠ 0) :
    0 ≤ (n:ℝ)*sourceRealInverseAction (by simp) (by norm_num) (hillMiuraRealSource u) n ∧
      0 ≤ sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1/(n:ℝ) :=
  source_inverseAction_nonneg (by simp) (by norm_num) (hillMiuraRealSource u) n
    (hillMiura_gap_coordinate_div_index_pos u n hn)

end NLS.KdV
