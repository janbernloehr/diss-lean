import NLS.ZakharovShabat.ClassicalMonodromyAnalytic
import NLS.ZakharovShabat.ClassicalL2Stability

/-! # An L2 bound for the full continuous Volterra inverse

The forcing is an arbitrary continuous curve. The bound depends on the
physical L2 potential norm, so it remains uniform under L2 approximation.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

theorem norm_classicalSolutionOperator_apply_le_L2
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (f : Curve (ℂ × ℂ)) :
    ‖solutionOperator (classicalCoefficientCurveCLM (z,φ)) f‖ ≤
      Real.exp (‖z‖+classicalPotentialL2Norm φ)*‖f‖ := by
  let A := classicalCoefficientCurveCLM (z,φ)
  let w := solutionOperator A f
  let a (s : ℝ) := ‖z‖+‖extend φ s‖
  have ha : Continuous a := continuous_const.add (continuous_extend φ).norm
  have hw : (1-volterra A) w = f := by
    change ((1-volterra A)*solutionOperator A) f = f
    rw [mul_solutionOperator,one_apply_eq_self]
  have he (t : Icc (0 : ℝ) 1) :
      w t = f t+∫ s in (0 : ℝ)..t.val, classicalODECoefficient (extend φ s) z (extend w s) := by
    have h := congrArg (fun g : Curve (ℂ × ℂ) => g t) hw
    simp only [sub_apply,one_apply_eq_self,ContinuousMap.sub_apply,volterra_apply] at h
    have heq : ∀ s : ℝ, extend A s = classicalODECoefficient (extend φ s) z := fun _ => rfl
    simp_rw [heq] at h
    exact eq_add_of_sub_eq h
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖extend w t‖ ≤ ‖f‖+∫ s in (0 : ℝ)..t, a s*‖extend w s‖ := by
    rw [show extend w t = w ⟨t,ht⟩ from extend_coe w ⟨t,ht⟩,he]
    apply (norm_add_le _ _).trans
    apply add_le_add (f.norm_coe_le_norm _)
    apply intervalIntegral.norm_integral_le_of_norm_le ht.1
    · filter_upwards [] with s _
      exact norm_classicalODECoefficient_apply_le _ _ _
    · exact (ha.mul (continuous_extend w).norm).intervalIntegrable _ _
  have h := le_exp_integral_of_le_const_add_integral (fun s => ‖extend w s‖) a
    (continuous_extend w).norm ha 1 ‖f‖ (norm_nonneg _)
    (fun _ _ => norm_nonneg _) (fun _ _ => by dsimp [a]; positivity) hb
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have ht := h t t.property
  rw [extend_coe] at ht
  exact ht.trans ((mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (integral_classicalCoefficient_norm_budget φ z t)) (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem norm_classicalSolutionOperator_le_L2 (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    ‖solutionOperator (classicalCoefficientCurveCLM (z,φ))‖ ≤
      Real.exp (‖z‖+classicalPotentialL2Norm φ) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
    (norm_classicalSolutionOperator_apply_le_L2 φ z)

end NLS.ZakharovShabat
