import NLS.FunctionalAnalysis.CompactDerivativeComposition
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Compact derivative principals under real linear germ transport -/
noncomputable section
set_option autoImplicit false
namespace NLS.ComplexAnalysis

theorem isCompactOperator_fderiv_real_linear_transport_sub
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : E →L[ℝ] F) (A : G →L[ℝ] H) (f : F → G) (a : E)
    (Q : F →L[ℂ] G) (hf : DifferentiableAt ℂ f (J a))
    (hc : IsCompactOperator (fderiv ℂ f (J a)-Q)) :
    IsCompactOperator (fderiv ℝ (fun x => A (f (J x))) a-
      A.comp ((Q.restrictScalars ℝ).comp J)) := by
  have hd := (A.hasFDerivAt.comp a
    ((hf.hasFDerivAt.restrictScalars ℝ).comp a J.hasFDerivAt)).fderiv
  change fderiv ℝ (fun x => A (f (J x))) a =
    A.comp (((fderiv ℂ f (J a)).restrictScalars ℝ).comp J) at hd
  have hr : IsCompactOperator ((fderiv ℂ f (J a)-Q).restrictScalars ℝ) := hc
  have he : fderiv ℝ (fun x => A (f (J x))) a-A.comp ((Q.restrictScalars ℝ).comp J)=
      A.comp (((fderiv ℂ f (J a)-Q).restrictScalars ℝ).comp J) := by
    rw [hd]
    apply ContinuousLinearMap.ext
    intro x
    exact (map_sub A _ _).symm
  rw [he]
  exact (hr.comp_clm J).clm_comp A

end NLS.ComplexAnalysis
