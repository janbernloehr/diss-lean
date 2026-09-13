import NLS.FunctionalAnalysis.ComplexVolterraAnalytic
import NLS.ZakharovShabat.ClassicalBoundaryDeterminants
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Matrix.Normed

/-!
# Joint analyticity of classical monodromy

The spectral parameter and continuous potential enter the ODE coefficient
through a bounded complex-linear map. The global inverse Volterra formula
therefore gives joint analyticity of its solutions, monodromy, discriminant,
and both endpoint characteristic determinants, including at multiple roots.
-/

noncomputable section
open Set Complex Matrix
open NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

private def classicalCoefficientPointCLM : (ℂ × (ℂ × ℂ)) →L[ℂ] ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) :=
  ( { toFun := fun t => classicalODECoefficient t.2 t.1
      map_add' := by
        intro t s
        ext <;> simp [classicalODECoefficient_apply] <;> ring
      map_smul' := by
        intro c t
        ext <;> simp [classicalODECoefficient_apply,smul_eq_mul] <;> ring } :
      (ℂ × (ℂ × ℂ)) →ₗ[ℂ] ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ))).toContinuousLinearMap

private def classicalParameterCurveCLM : (ℂ × Curve (ℂ × ℂ)) →L[ℂ] Curve (ℂ × (ℂ × ℂ)) :=
  LinearMap.mkContinuous
    { toFun := fun t => ⟨fun s => (t.1,t.2 s),continuous_const.prodMk t.2.continuous⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun t => by
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg t)).mpr
      intro s
      change ‖(t.1,t.2 s)‖ ≤ ‖t‖
      simp only [Prod.norm_def]
      exact max_le (le_max_left _ _) ((t.2.norm_coe_le_norm s).trans (le_max_right _ _)))

/-- The joint coefficient map from spectral parameter and continuous potential is bounded complex linear. -/
def classicalCoefficientCurveCLM : (ℂ × Curve (ℂ × ℂ)) →L[ℂ] Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) :=
  (ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1) classicalCoefficientPointCLM).comp classicalParameterCurveCLM

@[simp] theorem classicalCoefficientCurveCLM_apply (q : ℂ × Curve (ℂ × ℂ)) (t : Icc (0 : ℝ) 1) :
    classicalCoefficientCurveCLM q t = classicalODECoefficient (q.2 t) q.1 := rfl

/-- Restricting the coefficient scalars recovers the previously constructed classical ODE exactly. -/
theorem realCoefficient_classicalCoefficientCurve (q : ℂ × Curve (ℂ × ℂ)) :
    realCoefficient (classicalCoefficientCurveCLM q) = classicalODECurve q.2 q.1 := by
  ext t v <;> rfl

/-- At each point of the closed physical interval, the initial-value solution is jointly analytic. -/
theorem analyticOnNhd_classicalSolution_joint (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    AnalyticOnNhd ℂ (fun q : ℂ × Curve (ℂ × ℂ) => classicalSolution q.2 q.1 v t) Set.univ := by
  intro q _
  have h := (analyticOnNhd_solution_coefficient v t (classicalCoefficientCurveCLM q) (Set.mem_univ _)).comp
    (f := fun q => classicalCoefficientCurveCLM q) (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (F := Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ))) classicalCoefficientCurveCLM q)
  simpa only [Function.comp_def,realCoefficient_classicalCoefficientCurve,classicalSolution] using h

/-- Every entry of the fundamental matrix is jointly analytic, including at spectral collisions. -/
theorem analyticOnNhd_classicalFundamentalMatrix_joint (t : Icc (0 : ℝ) 1) :
    AnalyticOnNhd ℂ (fun q : ℂ × Curve (ℂ × ℂ) => classicalFundamentalMatrix q.2 q.1 t) Set.univ := by
  intro q _
  have h₁ := analyticOnNhd_classicalSolution_joint (1,0) t q (Set.mem_univ _)
  have h₂ := analyticOnNhd_classicalSolution_joint (0,1) t q (Set.mem_univ _)
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  fin_cases i <;> fin_cases j
  · exact analyticAt_fst.comp h₁
  · exact analyticAt_fst.comp h₂
  · exact analyticAt_snd.comp h₁
  · exact analyticAt_snd.comp h₂

/-- The endpoint monodromy is jointly analytic in spectral parameter and continuous potential. -/
theorem analyticOnNhd_classicalMonodromy_joint :
    AnalyticOnNhd ℂ (fun q : ℂ × Curve (ℂ × ℂ) => classicalMonodromy q.2 q.1) Set.univ :=
  analyticOnNhd_classicalFundamentalMatrix_joint ⟨1,by constructor <;> norm_num⟩

/-- The monodromy trace is jointly analytic on the full continuous-potential domain. -/
theorem analyticOnNhd_classicalDiscriminant_joint :
    AnalyticOnNhd ℂ (fun q : ℂ × Curve (ℂ × ℂ) => classicalDiscriminant q.2 q.1) Set.univ := by
  intro q _
  have h₁ := analyticOnNhd_classicalSolution_joint (1,0) ⟨1,by constructor <;> norm_num⟩ q (Set.mem_univ _)
  have h₂ := analyticOnNhd_classicalSolution_joint (0,1) ⟨1,by constructor <;> norm_num⟩ q (Set.mem_univ _)
  simp only [classicalDiscriminant,Matrix.trace_fin_two,classicalMonodromy,classicalFundamentalMatrix]
  exact (analyticAt_fst.comp h₁).add (analyticAt_snd.comp h₂)

/-- The characteristic determinant is jointly analytic for every fixed endpoint multiplier. -/
theorem analyticOnNhd_classicalBoundaryDeterminant_joint (σ : ℂ) :
    AnalyticOnNhd ℂ (fun q : ℂ × Curve (ℂ × ℂ) => (classicalMonodromy q.2 q.1 - σ • 1).det) Set.univ := by
  simp_rw [det_classicalMonodromy_sub_scalar]
  intro q _
  exact (analyticAt_const.sub (analyticAt_const.mul
    (analyticOnNhd_classicalDiscriminant_joint q (Set.mem_univ _)))).add analyticAt_const

/-- All mixed Fréchet derivatives of the classical discriminant remain analytic. -/
theorem analyticOnNhd_iteratedFDeriv_classicalDiscriminant (n : ℕ) :
    AnalyticOnNhd ℂ (iteratedFDeriv ℂ n
      (fun q : ℂ × Curve (ℂ × ℂ) => classicalDiscriminant q.2 q.1)) Set.univ :=
  analyticOnNhd_classicalDiscriminant_joint.iteratedFDeriv n

end NLS.ZakharovShabat
