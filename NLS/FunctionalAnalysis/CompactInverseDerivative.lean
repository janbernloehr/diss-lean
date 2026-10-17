import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! # Compact derivative remainders under analytic inverse charts

A right inverse of identity plus a compact operator differs compactly
from the identity. The chain rule transfers this fact to an actual
analytic inverse germ and a map with a compact linear remainder.
-/

noncomputable section
namespace NLS
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A right inverse of an identity-plus-compact operator is itself identity-plus-compact. -/
theorem isCompactOperator_rightInverse_sub_id
    (A B : E →L[ℂ] E) (hA : IsCompactOperator (A-ContinuousLinearMap.id ℂ E))
    (hAB : A.comp B = ContinuousLinearMap.id ℂ E) :
    IsCompactOperator (B-ContinuousLinearMap.id ℂ E) := by
  have he : B-ContinuousLinearMap.id ℂ E = -((A-ContinuousLinearMap.id ℂ E).comp B) := by
    ext x
    have hx := congrArg (fun L => L x) hAB
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hx
    change B x-x = -(A (B x)-B x)
    rw [hx,neg_sub]
  rw [he]
  exact (hA.comp_clm B).neg

/-- Composing on the right with an identity-plus-compact map preserves a compact remainder. -/
theorem isCompactOperator_comp_sub_of_compact_remainders
    (L Q : E →L[ℂ] F) (B : E →L[ℂ] E)
    (hL : IsCompactOperator (L-Q))
    (hB : IsCompactOperator (B-ContinuousLinearMap.id ℂ E)) :
    IsCompactOperator (L.comp B-Q) := by
  have he : L.comp B-Q = (L-Q).comp B+Q.comp (B-ContinuousLinearMap.id ℂ E) := by
    ext x
    change L (B x)-Q x = (L (B x)-Q (B x))+Q (B x-x)
    rw [map_sub]
    abel
  rw [he]
  exact (hL.comp_clm B).add (hB.clm_comp Q)
end NLS

namespace NLS
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Transfer actual compact derivative remainders through an analytic inverse germ. -/
theorem isCompactOperator_fderiv_comp_inverse_sub
    (A g : E → E) (f : E → F) (Q : E →L[ℂ] F) (a b : E)
    (hA : AnalyticAt ℂ A a) (hg : AnalyticAt ℂ g b) (hf : AnalyticAt ℂ f a)
    (hgb : g b = a) (hinv : (fun y => A (g y)) =ᶠ[𝓝 b] id)
    (hAc : IsCompactOperator (fderiv ℂ A a-ContinuousLinearMap.id ℂ E))
    (hfc : IsCompactOperator (fderiv ℂ f a-Q)) :
    IsCompactOperator (fderiv ℂ (fun y => f (g y)) b-Q) := by
  have hAg : HasFDerivAt A (fderiv ℂ A a) (g b) := by
    rw [hgb]
    exact hA.differentiableAt.hasFDerivAt
  have hfg : HasFDerivAt f (fderiv ℂ f a) (g b) := by
    rw [hgb]
    exact hf.differentiableAt.hasFDerivAt
  have hright : (fderiv ℂ A a).comp (fderiv ℂ g b) = ContinuousLinearMap.id ℂ E :=
    ((hAg.comp b hg.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hinv.symm).unique (hasFDerivAt_id b)
  have hd : fderiv ℂ (fun y => f (g y)) b = (fderiv ℂ f a).comp (fderiv ℂ g b) :=
    (hfg.comp b hg.differentiableAt.hasFDerivAt).fderiv
  rw [hd]
  exact isCompactOperator_comp_sub_of_compact_remainders _ _ _ hfc
    (isCompactOperator_rightInverse_sub_id _ _ hAc hright)
end NLS
