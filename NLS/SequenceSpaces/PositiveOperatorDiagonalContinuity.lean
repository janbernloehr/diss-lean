import NLS.SequenceSpaces.PositiveOperatorDiagonal
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Diagonal extraction on the original positive l2 operator space is
a bounded linear contraction. Its off-diagonal complement is continuous
in the FULL operator norm, so compact remainders pass to norm limits. -/
noncomputable section
open Complex
open scoped ENNReal Classical
namespace NLS.LpSequence

theorem norm_positiveOperatorDiagonal_le
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) :
    ‖positiveOperatorDiagonal T‖ ≤ ‖T‖ := by
  have he (m : ℕ+) : ‖T (lp.single 2 m 1) m‖ ≤ ‖T‖ := by
    calc
      _ ≤ ‖T (lp.single 2 m 1)‖ := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) _ m
      _ ≤ ‖T‖*‖(lp.single 2 m 1 : lp (fun _ : ℕ+ => ℂ) 2)‖ := T.le_opNorm _
      _ = ‖T‖ := by rw [lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2),norm_one,mul_one]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  have hn : ‖positiveOperatorDiagonal T a‖ ≤ ‖(‖T‖:ℂ) • a‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro m
    rw [positiveOperatorDiagonal_apply]
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right (he m) (norm_nonneg _)
  simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)] using hn

def positiveOperatorDiagonalCLM :
    (lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) →L[ℂ]
      (lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) :=
  LinearMap.mkContinuous
    { toFun := positiveOperatorDiagonal
      map_add' := by
        intro T S
        ext a m
        simp only [positiveOperatorDiagonal_apply,add_apply,lp.coeFn_add,Pi.add_apply]
        ring
      map_smul' := by
        intro z T
        ext a m
        simp only [positiveOperatorDiagonal_apply,smul_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
        ring }
    1 (by intro T; rw [one_mul]; exact norm_positiveOperatorDiagonal_le T)

theorem positiveOperatorDiagonalCLM_apply
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) :
    positiveOperatorDiagonalCLM T = positiveOperatorDiagonal T := rfl

theorem continuous_positiveOperatorDiagonal : Continuous
    (positiveOperatorDiagonal :
      (lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) →
        (lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)) :=
  positiveOperatorDiagonalCLM.continuous

theorem continuous_positiveOperatorOffDiagonal : Continuous
    (positiveOperatorOffDiagonal :
      (lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) →
        (lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)) :=
  continuous_id.sub continuous_positiveOperatorDiagonal

end NLS.LpSequence
