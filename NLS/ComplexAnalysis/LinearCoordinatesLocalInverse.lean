import NLS.ComplexAnalysis.AnalyticLocalInverseCriterion
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Analytic maps and inverse germs in linear coordinates -/
noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Conjugating a map by continuous linear coordinates preserves analyticity. -/
theorem analyticAt_linear_conjugate (e : E ≃L[𝕜] F) {f : E → E} {x : E}
    (hf : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (fun y => e (f (e.symm y))) (e x) := by
  have hh : AnalyticAt 𝕜 (fun y => f (e.symm y)) (e x) :=
    hf.comp_of_eq (f := e.symm) (e.symm.analyticAt (e x)) (e.symm_apply_apply x)
  exact (e.analyticAt _).comp hh

/-- The derivative in linear coordinates is conjugate to the original derivative. -/
theorem fderiv_linear_conjugate (e : E ≃L[𝕜] F) {f : E → E} {x : E}
    (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun y => e (f (e.symm y))) (e x) =
      e.conjContinuousAlgEquiv (fderiv 𝕜 f x) := by
  have hfx : HasFDerivAt f (fderiv 𝕜 f x) (e.symm (e x)) := by
    simpa only [e.symm_apply_apply] using hf.hasFDerivAt
  exact (e.hasFDerivAt.comp (e x) (hfx.comp (e x) e.symm.hasFDerivAt)).fderiv

/-- Compactness of derivative minus identity survives the same coordinate change. -/
theorem compact_sub_one_linear_conjugate (e : E ≃L[𝕜] F) {A : E →L[𝕜] E}
    (hA : IsCompactOperator (A-1 : E →L[𝕜] E)) :
    IsCompactOperator (e.conjContinuousAlgEquiv A-1 : F →L[𝕜] F) := by
  have hh := (hA.comp_clm e.symm.toContinuousLinearMap).clm_comp e.toContinuousLinearMap
  have he : e.toContinuousLinearMap.comp ((A-1).comp e.symm.toContinuousLinearMap) =
      e.conjContinuousAlgEquiv A-1 := by ext y; simp
  change IsCompactOperator (e.toContinuousLinearMap.comp ((A-1).comp e.symm.toContinuousLinearMap)) at hh
  rwa [he] at hh

/-- An actual analytic two-sided inverse germ. -/
def HasAnalyticInverse (f : E → E) (x : E) : Prop :=
  ∃ g : E → E, AnalyticAt 𝕜 g (f x) ∧ g (f x) = x ∧
    (∀ᶠ y in 𝓝 x, g (f y) = y) ∧ (∀ᶠ z in 𝓝 (f x), f (g z) = z)

/-- Transport both identities of an actual inverse, in either real or complex coordinates. -/
theorem HasAnalyticInverse.linear_conjugate (e : E ≃L[𝕜] F) {f : E → E} {x : E}
    (h : HasAnalyticInverse (𝕜 := 𝕜) f x) :
    HasAnalyticInverse (𝕜 := 𝕜) (fun y => e (f (e.symm y))) (e x) := by
  obtain ⟨g,hg,hgx,hl,hr⟩ := h
  refine ⟨fun z => e (g (e.symm z)),?_,?_,?_,?_⟩
  · simpa only [e.symm_apply_apply] using analyticAt_linear_conjugate e hg
  · simp only [e.symm_apply_apply,hgx]
  · have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      simpa only [e.symm_apply_apply] using e.symm.continuous.tendsto (e x)
    filter_upwards [ht hl] with y hy
    change g (f (e.symm y)) = e.symm y at hy
    simp only [e.symm_apply_apply,hy,e.apply_symm_apply]
  · have ht : Tendsto e.symm (𝓝 (e (f (e.symm (e x))))) (𝓝 (f x)) := by
      simpa only [e.symm_apply_apply] using e.symm.continuous.tendsto (e (f x))
    filter_upwards [ht hr] with y hy
    change f (g (e.symm y)) = e.symm y at hy
    simp only [e.symm_apply_apply,hy,e.apply_symm_apply]

/-- Existence of local inverse germs is invariant under linear coordinates. -/
theorem hasAnalyticInverse_linear_conjugate_iff (e : E ≃L[𝕜] F) {f : E → E} {x : E} :
    HasAnalyticInverse (𝕜 := 𝕜) (fun y => e (f (e.symm y))) (e x) ↔
      HasAnalyticInverse (𝕜 := 𝕜) f x := by
  constructor
  · intro h
    simpa only [ContinuousLinearEquiv.symm_symm,e.symm_apply_apply] using h.linear_conjugate e.symm
  · exact HasAnalyticInverse.linear_conjugate e

/-- A differentiable left inverse germ, without a right-inverse assumption. -/
def HasDifferentiableLeftInverse (f : E → E) (x : E) : Prop :=
  ∃ g : E → E, DifferentiableAt 𝕜 g (f x) ∧ ∀ᶠ y in 𝓝 x, g (f y) = y

/-- A differentiable real or complex left inverse also transports in linear coordinates. -/
theorem HasDifferentiableLeftInverse.linear_conjugate (e : E ≃L[𝕜] F) {f : E → E} {x : E}
    (h : HasDifferentiableLeftInverse (𝕜 := 𝕜) f x) :
    HasDifferentiableLeftInverse (𝕜 := 𝕜) (fun y => e (f (e.symm y))) (e x) := by
  obtain ⟨g,hg,hl⟩ := h
  refine ⟨fun z => e (g (e.symm z)),?_,?_⟩
  · have hg' : DifferentiableAt 𝕜 g (e.symm (e (f x))) := by
      simpa only [e.symm_apply_apply] using hg
    simpa only [e.symm_apply_apply,Function.comp_def] using
      e.differentiableAt.comp (e (f x)) (hg'.comp (e (f x)) e.symm.differentiableAt)
  · have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      simpa only [e.symm_apply_apply] using e.symm.continuous.tendsto (e x)
    filter_upwards [ht hl] with y hy
    change g (f (e.symm y)) = e.symm y at hy
    simp only [e.symm_apply_apply,hy,e.apply_symm_apply]

end NLS.ComplexAnalysis
