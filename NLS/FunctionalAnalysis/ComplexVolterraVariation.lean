import NLS.FunctionalAnalysis.ForcedVolterraSolution
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Actual coefficient variation of continuous linear ODE solutions

Differentiating the globally invertible Volterra equation identifies the
Fréchet derivative of the entire solution curve. It is the zero-initial
forced solution whose source is the coefficient perturbation applied
to the original solution, with no smallness assumption.
-/

noncomputable section
open Set
namespace NLS.LinearVolterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem fderiv_solutionCurve_coefficient_apply
    (A B : Curve (E →L[ℂ] E)) (x : E) :
    (fderiv ℂ (fun C : Curve (E →L[ℂ] E) => solutionCurve (realCoefficient C) x) A) B =
      solutionOperator A (volterra B (solutionCurve (realCoefficient A) x)) := by
  let u : Curve (E →L[ℂ] E) → Curve E := fun C => solutionCurve (realCoefficient C) x
  have hd : HasFDerivAt u (fderiv ℂ u A) A :=
    ((analyticOnNhd_solutionCurve_coefficient x) A (mem_univ _)).differentiableAt.hasFDerivAt
  have hV : HasFDerivAt (volterraCoefficientMap (E := E)) (volterraCoefficientMap (E := E)) A :=
    (volterraCoefficientMap (E := E)).hasFDerivAt
  have hprod : HasFDerivAt (fun C => volterraCoefficientMap (E := E) C (u C))
      ((volterra A).comp (fderiv ℂ u A)+(volterraCoefficientMap (E := E)).flip (u A)) A :=
    HasFDerivAt.clm_apply (𝕜 := ℂ) (E := Curve (E →L[ℂ] E))
      (G := Curve E) (H := Curve E) hV hd
  have hdiff := hd.sub hprod
  have heq : (fun C : Curve (E →L[ℂ] E) => u C-volterraCoefficientMap C (u C)) =
      (fun _ => ContinuousMap.const _ x) := by
    funext C
    change (1-volterra C) (solutionCurve (realCoefficient C) x) = _
    rw [solutionCurve_eq_solutionOperator,← mul_apply_eq_comp,mul_solutionOperator,one_apply_eq_self]
  have hzero := congrArg (fun L => L B) hdiff.fderiv
  change (fderiv ℂ (fun C => u C-volterraCoefficientMap (E := E) C (u C)) A) B = _ at hzero
  rw [heq] at hzero
  simp only [fderiv_fun_const] at hzero
  change (0 : Curve E) = (fderiv ℂ u A) B-
    (volterra A ((fderiv ℂ u A) B)+volterra B (u A)) at hzero
  have hlin : (1-volterra A) ((fderiv ℂ u A) B) = volterra B (u A) := by
    have h := sub_eq_zero.mp hzero.symm
    change (fderiv ℂ u A) B-volterra A ((fderiv ℂ u A) B) = _
    exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))
  have h := congrArg (fun v => solutionOperator A v) hlin
  rw [← mul_apply_eq_comp,solutionOperator_mul,one_apply_eq_self] at h
  exact h

/-- Pointwise multiplication of a continuous operator coefficient and
a continuous curve is the continuous source in the variation equation. -/
def coefficientVariationSource (B : Curve (E →L[ℂ] E)) (u : Curve E) : Curve E :=
  ⟨fun t => B t (u t),B.continuous.clm_apply u.continuous⟩

theorem primitive_coefficientVariationSource (B : Curve (E →L[ℂ] E)) (u : Curve E) :
    primitive (coefficientVariationSource B u) = volterra B u := by
  ext t
  rw [primitive_apply,volterra_apply]
  rfl

theorem fderiv_solutionCurve_coefficient_eq_forced
    (A B : Curve (E →L[ℂ] E)) (x : E) :
    (fderiv ℂ (fun C : Curve (E →L[ℂ] E) => solutionCurve (realCoefficient C) x) A) B =
      forcedSolutionCurve A (coefficientVariationSource B (solutionCurve (realCoefficient A) x)) 0 := by
  rw [fderiv_solutionCurve_coefficient_apply]
  simp only [forcedSolutionCurve,
    show ContinuousMap.const (Icc (0 : ℝ) 1) (0 : E) = 0 from rfl,
    zero_add,primitive_coefficientVariationSource]

end NLS.LinearVolterra
