import NLS.FunctionalAnalysis.ComplexVolterraAnalytic
import NLS.FunctionalAnalysis.LinearVolterraRegularity
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Linear initial-value maps and invariant traces

The existing Volterra construction gives a bounded complex-linear map from
initial data to the solution at a fixed time. A constant intertwiner of the
coefficient equations intertwines these actual solution maps. In finite
dimension an injective intertwiner therefore preserves their trace.
-/
noncomputable section
open Set Module
namespace NLS.LinearVolterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The constructed solution is absolutely continuous on its closed interval. -/
theorem absolutelyContinuous_solution (A : Curve (E →L[ℝ] E)) (v : E) :
    AbsolutelyContinuousOnInterval (solution A v) 0 1 := by
  have h := NLS.FunctionalAnalysis.absolutelyContinuousOnInterval_integral
    ((continuous_integrand A (solutionCurve A v)).intervalIntegrable 0 1)
    (by simp : (0 : ℝ) ∈ uIcc 0 1)
  exact NLS.FunctionalAnalysis.absolutelyContinuousOnInterval_const_add h v

/-- The actual linear initial-value map at a point of the closed interval. -/
def solutionMap (A : Curve (E →L[ℂ] E)) (t : Icc (0 : ℝ) 1) : E →L[ℂ] E :=
  (ContinuousMap.evalCLM ℂ t).comp
    ((solutionOperator A).comp (ContinuousLinearMap.const ℂ (Icc (0 : ℝ) 1)))

@[simp] theorem solutionMap_apply (A : Curve (E →L[ℂ] E)) (t : Icc (0 : ℝ) 1) (v : E) :
    solutionMap A t v = solution (realCoefficient A) v t := by
  rw [solution, solutionMap]
  change solutionOperator A (ContinuousMap.const _ v) t = _
  rw [← solutionCurve_eq_solutionOperator, solutionCurve_eq]

/-- Uniqueness transfers a constant coefficient intertwiner to the solutions. -/
theorem solutionMap_intertwine (A B : Curve (E →L[ℂ] E)) (T : E →L[ℂ] E)
    (hT : ∀ t : Icc (0 : ℝ) 1, ∀ v : E, B t (T v) = T (A t v))
    (v : E) (t : Icc (0 : ℝ) 1) :
    solutionMap B t (T v) = T (solutionMap A t v) := by
  simp only [solutionMap_apply]
  symm
  apply solution_unique (realCoefficient B) (T v)
    (fun x => T (solution (realCoefficient A) v x))
    (T.continuous.comp (continuous_solution _ _)).continuousOn
    (by simp) _ t.property
  intro s _
  have hd := (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (s : ℝ)
    (hasDerivAt_solution_coe (realCoefficient A) v s)
  convert! hd using 1
  exact hT s _

/-- An injective constant intertwiner preserves the actual finite-dimensional
solution trace; no spectral identification is assumed. -/
theorem trace_solutionMap_intertwine [FiniteDimensional ℂ E]
    (A B : Curve (E →L[ℂ] E)) (T : E →L[ℂ] E) (hinj : Function.Injective T)
    (hT : ∀ t : Icc (0 : ℝ) 1, ∀ v : E, B t (T v) = T (A t v))
    (t : Icc (0 : ℝ) 1) :
    LinearMap.trace ℂ E (solutionMap B t).toLinearMap =
      LinearMap.trace ℂ E (solutionMap A t).toLinearMap := by
  let e := LinearEquiv.ofInjectiveEndo T.toLinearMap hinj
  have he : (solutionMap B t).toLinearMap = e.conj (solutionMap A t).toLinearMap := by
    ext v
    change solutionMap B t v = T (solutionMap A t (e.symm v))
    have h := solutionMap_intertwine A B T hT (e.symm v) t
    have hi : T (e.symm v) = v := e.apply_symm_apply v
    simpa only [hi] using h
  rw [he]
  exact LinearMap.trace_conj' _ e

/-- The basis-free trace of a complex pair map is its two physical diagonal
entries, in the standard order (1,0), (0,1). -/
theorem trace_pairCLM (T : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) :
    LinearMap.trace ℂ (ℂ × ℂ) T.toLinearMap = (T (1,0)).1+(T (0,1)).2 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Basis.finTwoProd ℂ), Matrix.trace_fin_two]
  simp [LinearMap.toMatrix_apply, Basis.coe_finTwoProd_repr]

end NLS.LinearVolterra
