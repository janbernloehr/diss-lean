import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Operator.Compact.Basic

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.FunctionalAnalysis

/-- The second derivative of an analytic scalar germ factoring through a
compact linear inclusion is compact as an operator into the source dual.
The equality is local; no global factorization is required. -/
theorem isCompactOperator_fderiv_fderiv_of_compact_germ
    {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : E →L[ℝ] H) (hL : IsCompactOperator L) (F : H → G) (q : E)
    (hF : AnalyticAt ℝ F (L q)) (g : E → G)
    (hg : g =ᶠ[𝓝 q] (fun p => F (L p))) :
    IsCompactOperator (fderiv ℝ (fderiv ℝ g) q) := by
  let K : (H →L[ℝ] G) →L[ℝ] (E →L[ℝ] G) :=
    (ContinuousLinearMap.compL ℝ E H G).flip L
  let A : E → E →L[ℝ] G := fun p => K (fderiv ℝ F (L p))
  have hd : HasFDerivAt A ((K.comp (fderiv ℝ (fderiv ℝ F) (L q))).comp L) q :=
    (K.hasFDerivAt.comp (L q) hF.fderiv.differentiableAt.hasFDerivAt).comp q L.hasFDerivAt
  have hc : IsCompactOperator (fderiv ℝ A q) := by
    rw [hd.fderiv]
    exact hL.clm_comp (K.comp (fderiv ℝ (fderiv ℝ F) (L q)))
  have he : fderiv ℝ g =ᶠ[𝓝 q] A := by
    filter_upwards [hg.fderiv (𝕜 := ℝ),L.continuous.continuousAt.tendsto.eventually hF.eventually_analyticAt] with p hp hpa
    rw [hp]
    exact (hpa.differentiableAt.hasFDerivAt.comp p L.hasFDerivAt).fderiv
  rw [he.fderiv_eq]
  exact hc

end NLS.FunctionalAnalysis
