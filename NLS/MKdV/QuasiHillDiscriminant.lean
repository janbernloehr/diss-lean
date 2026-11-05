import NLS.FunctionalAnalysis.LinearVolterraFlow
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Analytic.Constructions

/-! # An independent Miura–Hill initial-value problem

For a continuous complex u, the state (g,w) with w=g'-u*g satisfies
g'=u*g+w and w'=-mu*g-u*w. This initial-value problem is constructed directly
by the existing generic Volterra solver, independently of Zakharov–Shabat data.
For differentiable u it gives -g''+(u'+u²)*g=mu*g. Identification with the
physical H¹ Hill operator is recorded separately from this construction.
-/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.MKdV

/-- Coefficient of the physical Miura quasi-derivative system. -/
def quasiHillCoefficient (u μ : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (u • ContinuousLinearMap.fst ℂ ℂ ℂ+ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((-μ) • ContinuousLinearMap.fst ℂ ℂ ℂ-u • ContinuousLinearMap.snd ℂ ℂ ℂ)

@[simp] theorem quasiHillCoefficient_apply (u μ : ℂ) (v : ℂ × ℂ) :
    quasiHillCoefficient u μ v = (u*v.1+v.2,-μ*v.1-u*v.2) := rfl

private def quasiHillZeroCoefficient (u : Curve ℂ) : Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) where
  toFun t := quasiHillCoefficient (u t) 0
  continuous_toFun := by
    exact (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp
      (show Continuous (fun t : Icc (0 : ℝ) 1 =>
        ((u t) • ContinuousLinearMap.fst ℂ ℂ ℂ+ContinuousLinearMap.snd ℂ ℂ ℂ,
         (-0 : ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ-(u t) • ContinuousLinearMap.snd ℂ ℂ ℂ)) by
        fun_prop)

private theorem quasiHillZeroCoefficient_apply (u : Curve ℂ) (t : Icc (0 : ℝ) 1) :
    quasiHillZeroCoefficient u t = quasiHillCoefficient (u t) 0 := rfl

private def quasiHillSpectralCurveCLM : ℂ →L[ℂ] Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) :=
  let K : Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) := ContinuousMap.const _
    ((0 : (ℂ × ℂ) →L[ℂ] ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ))
  LinearMap.mkContinuous
    { toFun := fun μ => μ • K
      map_add' := fun a b => add_smul a b K
      map_smul' := fun a b => by simp only [RingHom.id_apply, smul_eq_mul, smul_smul] }
    ‖K‖ (by intro μ; change ‖μ • K‖ ≤ ‖K‖*‖μ‖; exact (norm_smul_le μ K).trans_eq (mul_comm _ _))

private theorem quasiHillSpectralCurveCLM_apply (μ : ℂ) (t : Icc (0 : ℝ) 1) (v : ℂ × ℂ) :
    quasiHillSpectralCurveCLM μ t v = (0, μ*v.1) := by
  change μ • ((0 : (ℂ × ℂ) →L[ℂ] ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ) v) = _
  simp

/-- The independent coefficient curve, affine in the squared spectral parameter. -/
def quasiHillCoefficientCurve (u : Curve ℂ) (μ : ℂ) : Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) :=
  quasiHillZeroCoefficient u-quasiHillSpectralCurveCLM μ

@[simp] theorem quasiHillCoefficientCurve_apply (u : Curve ℂ) (μ : ℂ)
    (t : Icc (0 : ℝ) 1) : quasiHillCoefficientCurve u μ t = quasiHillCoefficient (u t) μ := by
  apply ContinuousLinearMap.ext
  intro v
  change (quasiHillZeroCoefficient u t) v-(quasiHillSpectralCurveCLM μ t) v = _
  rw [quasiHillZeroCoefficient_apply, quasiHillSpectralCurveCLM_apply]
  apply Prod.ext <;> simp [quasiHillCoefficient_apply]
  ring

theorem analyticAt_quasiHillCoefficientCurve (u : Curve ℂ) (μ : ℂ) :
    AnalyticAt ℂ (quasiHillCoefficientCurve u) μ := by
  change AnalyticAt ℂ (fun w => quasiHillZeroCoefficient u-quasiHillSpectralCurveCLM w) μ
  have h : AnalyticAt ℂ (fun w => quasiHillSpectralCurveCLM w) μ := by
    convert! ContinuousLinearMap.analyticAt (𝕜 := ℂ)
      (F := Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ))) quasiHillSpectralCurveCLM μ
  exact analyticAt_const.sub h

/-- The independent quasi-Hill solution with prescribed position and quasi-derivative. -/
def quasiHillSolution (u : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ) : ℝ → ℂ × ℂ :=
  solution (realCoefficient (quasiHillCoefficientCurve u μ)) v

@[simp] theorem quasiHillSolution_zero (u : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ) :
    quasiHillSolution u μ v 0 = v := solution_zero _ _

theorem hasDerivAt_quasiHillSolution (u : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (quasiHillSolution u μ v)
      (quasiHillCoefficient (u t) μ (quasiHillSolution u μ v t)) t := by
  simpa only [quasiHillSolution, realCoefficient, ContinuousMap.coe_mk,
    quasiHillCoefficientCurve_apply, ContinuousLinearMap.coe_restrictScalars] using!
      hasDerivAt_solution_coe (realCoefficient (quasiHillCoefficientCurve u μ)) v t

theorem hasDerivAt_fst_quasiHillSolution (u : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => (quasiHillSolution u μ v y).1)
      (u t*(quasiHillSolution u μ v t).1+(quasiHillSolution u μ v t).2) t := by
  have h := hasDerivAt_quasiHillSolution u μ v t
  simpa only [quasiHillCoefficient_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using! (HasFDerivAt.hasDerivAt h.fst)

theorem hasDerivAt_snd_quasiHillSolution (u : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => (quasiHillSolution u μ v y).2)
      (-μ*(quasiHillSolution u μ v t).1-u t*(quasiHillSolution u μ v t).2) t := by
  have h := hasDerivAt_quasiHillSolution u μ v t
  simpa only [quasiHillCoefficient_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using! (HasFDerivAt.hasDerivAt h.snd)

/-- Trace of the independently constructed physical quasi-Hill monodromy. -/
def quasiHillDiscriminant (u : Curve ℂ) (μ : ℂ) : ℂ :=
  LinearMap.trace ℂ (ℂ × ℂ)
    (solutionMap (quasiHillCoefficientCurve u μ) ⟨1,by constructor <;> norm_num⟩).toLinearMap

/-- The independent discriminant is analytic even at the zero spectral parameter. -/
theorem analyticAt_quasiHillDiscriminant (u : Curve ℂ) (μ : ℂ) :
    AnalyticAt ℂ (quasiHillDiscriminant u) μ := by
  change AnalyticAt ℂ (fun w => LinearMap.trace ℂ (ℂ × ℂ)
    (solutionMap (quasiHillCoefficientCurve u w) ⟨1,by constructor <;> norm_num⟩).toLinearMap) μ
  simp only [trace_pairCLM, solutionMap_apply]
  have h1 := (analyticOnNhd_solution_coefficient (E := ℂ × ℂ) (1,0)
    ⟨1,by constructor <;> norm_num⟩ (quasiHillCoefficientCurve u μ) (mem_univ _)).comp
      (analyticAt_quasiHillCoefficientCurve u μ)
  have h2 := (analyticOnNhd_solution_coefficient (E := ℂ × ℂ) (0,1)
    ⟨1,by constructor <;> norm_num⟩ (quasiHillCoefficientCurve u μ) (mem_univ _)).comp
      (analyticAt_quasiHillCoefficientCurve u μ)
  exact (analyticAt_fst.comp h1).add (analyticAt_snd.comp h2)

end NLS.MKdV
