import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot
import Mathlib.Analysis.Normed.Operator.Prod

/-! # A quantitative inverse for a triangular Banach derivative -/

noncomputable section
namespace NLS.ComplexAnalysis
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- The derivative of the equation-and-parameter map has an explicit
two-sided inverse. Its norm is controlled by the root inverse norm
and the joint equation derivative norm. -/
theorem exists_triangularLinearEquiv_norm_bound
    (A : (E × P) →L[ℂ] E) (S : E →L[ℂ] E)
    (hQS : (A.comp (ContinuousLinearMap.inl ℂ E P)).comp S = ContinuousLinearMap.id ℂ E)
    (hSQ : S.comp (A.comp (ContinuousLinearMap.inl ℂ E P)) = ContinuousLinearMap.id ℂ E) :
    ∃ T : (E × P) ≃L[ℂ] (E × P),
      (T : (E × P) →L[ℂ] (E × P)) = A.prod (ContinuousLinearMap.snd ℂ E P) ∧
      ‖(T.symm : (E × P) →L[ℂ] (E × P))‖ ≤ ‖S‖*(1+‖A‖)+1 := by
  let Q := A.comp (ContinuousLinearMap.inl ℂ E P)
  let B := A.comp (ContinuousLinearMap.inr ℂ E P)
  let T₀ := A.prod (ContinuousLinearMap.snd ℂ E P)
  let R := (S.comp (ContinuousLinearMap.fst ℂ E P-
    B.comp (ContinuousLinearMap.snd ℂ E P))).prod (ContinuousLinearMap.snd ℂ E P)
  have hA (e : E) (y : P) : A (e,y) = Q e+B y := by
    have hsplit : (e,y) = (e,(0:P))+(0,y) := by ext <;> simp
    rw [hsplit,map_add]
    rfl
  have hrightS (e : E) : Q (S e) = e := by
    have h := congrArg (fun L : E →L[ℂ] E => L e) hQS
    simpa only [Q,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using h
  have hleftS (e : E) : S (Q e) = e := by
    have h := congrArg (fun L : E →L[ℂ] E => L e) hSQ
    simpa only [Q,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using h
  have hRT : Function.LeftInverse R T₀ := by
    intro x
    apply Prod.ext
    · change S (A (x.1,x.2)-B x.2) = x.1
      rw [hA,add_sub_cancel_right,hleftS]
    · rfl
  have hTR : Function.RightInverse R T₀ := by
    intro y
    apply Prod.ext
    · change A (S (y.1-B y.2),y.2) = y.1
      rw [hA,hrightS,sub_add_cancel]
    · rfl
  let T := ContinuousLinearEquiv.equivOfInverse T₀ R hRT hTR
  refine ⟨T,rfl,?_⟩
  change ‖R‖ ≤ ‖S‖*(1+‖A‖)+1
  apply R.opNorm_le_bound (by positivity)
  intro y
  change max ‖S (y.1-A (0,y.2))‖ ‖y.2‖ ≤ (‖S‖*(1+‖A‖)+1)*‖y‖
  have hy₁ : ‖y.1‖ ≤ ‖y‖ := le_max_left _ _
  have hy₂ : ‖y.2‖ ≤ ‖y‖ := le_max_right _ _
  have hAy : ‖A (0,y.2)‖ ≤ ‖A‖*‖y.2‖ := by
    simpa only [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] using A.le_opNorm (0,y.2)
  apply max_le
  · calc
      _ ≤ ‖S‖*‖y.1-A (0,y.2)‖ := S.le_opNorm _
      _ ≤ ‖S‖*(‖y.1‖+‖A‖*‖y.2‖) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add le_rfl hAy)) (norm_nonneg _)
      _ ≤ ‖S‖*(‖y‖+‖A‖*‖y‖) := by gcongr
      _ = (‖S‖*(1+‖A‖))*‖y‖ := by ring
      _ ≤ (‖S‖*(1+‖A‖)+1)*‖y‖ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one) (norm_nonneg y)
  · calc
      _ ≤ ‖y‖ := hy₂
      _ ≤ (‖S‖*(1+‖A‖)+1)*‖y‖ := by
        have hK : 1 ≤ ‖S‖*(1+‖A‖)+1 := le_add_of_nonneg_left (by positivity)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (norm_nonneg y)

end NLS.ComplexAnalysis
