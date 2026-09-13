import NLS.FunctionalAnalysis.ComplexVolterraOperator

/-!
# Analytic dependence of continuous linear ODE solutions

The coefficient-to-Volterra map is bounded and complex linear. Inversion on
units therefore gives analytic dependence of the whole solution curve on its
continuous coefficient, with no smallness restriction.
-/

noncomputable section
open Set MeasureTheory intervalIntegral
namespace NLS.LinearVolterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The coefficient-to-integral-operator map is bounded complex linear. -/
def volterraCoefficientMap : Curve (E →L[ℂ] E) →L[ℂ] (Curve E →L[ℂ] Curve E) :=
  LinearMap.mkContinuous
    { toFun := volterra (E := E)
      map_add' := by
        intro A B
        ext u t
        simp only [add_apply,ContinuousMap.add_apply,volterra_apply,
          extend,add_apply]
        exact intervalIntegral.integral_add
          ((continuous_integrand (realCoefficient A) u).intervalIntegrable _ _)
          ((continuous_integrand (realCoefficient B) u).intervalIntegrable _ _)
      map_smul' := by
        intro c A
        ext u t
        simp only [smul_apply,ContinuousMap.smul_apply,RingHom.id_apply,
          volterra_apply,extend]
        exact intervalIntegral.integral_smul _ _ }
    1 (fun A => by simpa only [one_mul] using! norm_volterra_le A)

/-- The inverse Volterra operator solves arbitrary continuous forcing equations. -/
def solutionOperator (A : Curve (E →L[ℂ] E)) : Curve E →L[ℂ] Curve E :=
  Ring.inverse (1-volterra A)

theorem solutionOperator_mul (A : Curve (E →L[ℂ] E)) : solutionOperator A * (1-volterra A) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_one_sub_volterra A)

theorem mul_solutionOperator (A : Curve (E →L[ℂ] E)) : (1-volterra A) * solutionOperator A = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_one_sub_volterra A)

/-- The previously constructed initial-value solution is exactly the inverse applied to its constant initial curve. -/
theorem solutionCurve_eq_solutionOperator (A : Curve (E →L[ℂ] E)) (x : E) :
    solutionCurve (realCoefficient A) x = solutionOperator A (ContinuousMap.const _ x) := by
  have hs : (1-volterra A) (solutionCurve (realCoefficient A) x) = ContinuousMap.const _ x := by
    ext t
    simp only [sub_apply,one_apply_eq_self,ContinuousMap.sub_apply,
      volterra_apply,ContinuousMap.const_apply]
    rw [solutionCurve_eq]
    change (x + ∫ s in (0 : ℝ)..t.val, extend A s (extend (solutionCurve (realCoefficient A) x) s)) -
      (∫ s in (0 : ℝ)..t.val, extend A s (extend (solutionCurve (realCoefficient A) x) s)) = x
    exact add_sub_cancel_right _ _
  calc
    _ = (solutionOperator A * (1-volterra A)) (solutionCurve (realCoefficient A) x) := by
      rw [solutionOperator_mul,one_apply_eq_self]
    _ = _ := by rw [mul_apply_eq_comp,hs]

/-- The inverse operator is analytic on the full continuous-coefficient Banach space. -/
theorem analyticOnNhd_solutionOperator :
    AnalyticOnNhd ℂ (solutionOperator (E := E)) Set.univ := by
  intro A _
  have hV : AnalyticAt ℂ (volterra (E := E)) A := by
    convert! ContinuousLinearMap.analyticAt (𝕜 := ℂ) (F := Curve E →L[ℂ] Curve E) (volterraCoefficientMap (E := E)) A
  exact (analyticOnNhd_inverse (𝕜 := ℂ) (A := Curve E →L[ℂ] Curve E) _ (isUnit_one_sub_volterra A)).comp
    (f := fun B : Curve (E →L[ℂ] E) => 1-volterra B)
    (analyticAt_const.sub hV)

/-- The whole continuous solution curve depends analytically on the coefficient. -/
theorem analyticOnNhd_solutionCurve_coefficient (x : E) :
    AnalyticOnNhd ℂ (fun A : Curve (E →L[ℂ] E) => solutionCurve (realCoefficient A) x) Set.univ := by
  simp_rw [solutionCurve_eq_solutionOperator]
  intro A _
  exact ((ContinuousLinearMap.apply ℂ (Curve E) (ContinuousMap.const _ x)).analyticAt _).comp
    (analyticOnNhd_solutionOperator A (Set.mem_univ _))

/-- Evaluation anywhere on the closed interval retains analytic coefficient dependence. -/
theorem analyticOnNhd_solution_coefficient (x : E) (t : Icc (0 : ℝ) 1) :
    AnalyticOnNhd ℂ (fun A : Curve (E →L[ℂ] E) => solution (realCoefficient A) x t) Set.univ := by
  simp_rw [solution_coe]
  intro A _
  exact ((ContinuousMap.evalCLM ℂ t).analyticAt _).comp
    (analyticOnNhd_solutionCurve_coefficient x A (Set.mem_univ _))

end NLS.LinearVolterra
