import NLS.SequenceSpaces.WeightedSymbolGauge
import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.FunctionalAnalysis.LinearTargetDerivative
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Removing an analytic bounded exponential symbol from a weighted
sequence map changes its derivative, after the invertible diagonal
factor, by an actual compact operator at every finite exponent. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def removeExponentialSymbol (w : Weight) (θ : E → Coeff ⊤)
    (f : E → WeightedCoeff w p) (q : E) : WeightedCoeff w p :=
  (exponentialSymbolEquiv w (θ q)).symm (f q)

theorem analyticAt_removeExponentialSymbol (w : Weight) (θ : E → Coeff ⊤)
    (f : E → WeightedCoeff w p) (q : E) (hθ : AnalyticAt ℂ θ q)
    (hf : AnalyticAt ℂ f q) : AnalyticAt ℂ (removeExponentialSymbol w θ f) q := by
  exact ((boundedSymbolBilinear w).analyticAt_bilinear _).comp
    (((NormedSpace.exp_analytic _).comp hθ.neg).prod hf)

theorem fderiv_removeExponentialSymbol_remainder (w : Weight) (θ : E → Coeff ⊤)
    (f : E → WeightedCoeff w p) (q : E) (hθ : AnalyticAt ℂ θ q)
    (hf : AnalyticAt ℂ f q) :
    fderiv ℂ f q - (exponentialSymbolEquiv w (θ q)).toContinuousLinearMap.comp
      (fderiv ℂ (removeExponentialSymbol w θ f) q) =
    ((boundedSymbolBilinear w).flip (f q)).comp (fderiv ℂ θ q) := by
  let g := removeExponentialSymbol w θ f
  have hg := analyticAt_removeExponentialSymbol w θ f q hθ hf
  ext h
  apply Subtype.ext
  funext k
  let ev := evalCLM w p k
  let es := lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ k
  have ht := (es.hasFDerivAt.comp q hθ.differentiableAt.hasFDerivAt).cexp
  have hgd := ev.hasFDerivAt.comp q hg.differentiableAt.hasFDerivAt
  have hfd := ev.hasFDerivAt.comp q hf.differentiableAt.hasFDerivAt
  have he : (fun x => Complex.exp (θ x k)*(g x).val k) = fun x => (f x).val k := by
    funext x
    exact (exponentialSymbolEquiv_apply w (θ x) (g x) k).symm.trans
      (congrArg (fun a : WeightedCoeff w p => a.val k)
        ((exponentialSymbolEquiv w (θ x)).apply_symm_apply (f x)))
  have hd := ht.fun_mul hgd
  change HasFDerivAt (fun x => Complex.exp (θ x k)*(g x).val k) _ q at hd
  rw [he] at hd
  have hh := congrArg (fun L : E →L[ℂ] ℂ => L h) (hd.unique hfd)
  change Complex.exp (θ q k)*((fderiv ℂ g q) h).val k +
    (g q).val k*(Complex.exp (θ q k)*((fderiv ℂ θ q) h k)) =
      ((fderiv ℂ f q) h).val k at hh
  have hv : Complex.exp (θ q k)*(g q).val k = (f q).val k := congrFun he q
  change ((fderiv ℂ f q) h).val k -
    (exponentialSymbolEquiv w (θ q) ((fderiv ℂ g q) h)).val k =
      ((fderiv ℂ θ q) h k)*(f q).val k
  rw [exponentialSymbolEquiv_apply,← hv]
  linear_combination -hh

theorem isCompactOperator_removeExponentialSymbol_remainder (w : Weight) (hp : p ≠ ⊤)
    (θ : E → Coeff ⊤) (f : E → WeightedCoeff w p) (q : E)
    (hθ : AnalyticAt ℂ θ q) (hf : AnalyticAt ℂ f q) :
    IsCompactOperator (fderiv ℂ f q - (exponentialSymbolEquiv w (θ q)).toContinuousLinearMap.comp
      (fderiv ℂ (removeExponentialSymbol w θ f) q)) := by
  rw [fderiv_removeExponentialSymbol_remainder w θ f q hθ hf]
  exact (isCompactOperator_boundedSymbol_fixed w hp (f q)).comp_clm (fderiv ℂ θ q)

end NLS.WeightedCoeff
