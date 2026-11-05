import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Operator.Compact.Basic

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.FunctionalAnalysis

/-- Linear postcomposition acts on the full second derivative by the
corresponding bounded postcomposition operator. -/
theorem fderiv_fderiv_clm_comp
    {E Y G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E → Y) (q : E) (hF : AnalyticAt ℝ F q) (ℓ : Y →L[ℝ] G) :
    fderiv ℝ (fderiv ℝ (ℓ ∘ F)) q =
      ((ContinuousLinearMap.compL ℝ E Y G) ℓ).comp (fderiv ℝ (fderiv ℝ F) q) := by
  let P := (ContinuousLinearMap.compL ℝ E Y G) ℓ
  have he : fderiv ℝ (ℓ ∘ F) =ᶠ[𝓝 q] (fun p => P (fderiv ℝ F p)) := by
    filter_upwards [hF.eventually_analyticAt] with p hp
    exact (ℓ.hasFDerivAt.comp p hp.differentiableAt.hasFDerivAt).fderiv
  have hd : HasFDerivAt (fun p => P (fderiv ℝ F p))
      (P.comp (fderiv ℝ (fderiv ℝ F) q)) q :=
    P.hasFDerivAt.comp q hF.fderiv.differentiableAt.hasFDerivAt
  exact he.fderiv_eq.trans hd.fderiv

/-- Compactness of scalar Hessians persists under norm limits of the
postcomposing linear functional, in operator norm on the source dual. -/
theorem isCompactOperator_secondDerivative_of_dual_limit
    {E Y G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (F : E → Y) (q : E) (hF : AnalyticAt ℝ F q)
    (ℓ : Y →L[ℝ] G) (a : ι → Y →L[ℝ] G) {l : Filter ι} [NeBot l]
    (ha : Tendsto a l (𝓝 ℓ))
    (hc : ∀ᶠ j in l, IsCompactOperator (fderiv ℝ (fderiv ℝ (a j ∘ F)) q)) :
    IsCompactOperator (fderiv ℝ (fderiv ℝ (ℓ ∘ F)) q) := by
  have hcont : Continuous (fun A : Y →L[ℝ] G =>
      ((ContinuousLinearMap.compL ℝ E Y G) A).comp (fderiv ℝ (fderiv ℝ F) q)) := by
    fun_prop
  have ht := hcont.continuousAt.tendsto.comp ha
  have he : Tendsto (fun j => fderiv ℝ (fderiv ℝ (a j ∘ F)) q) l
      (𝓝 (fderiv ℝ (fderiv ℝ (ℓ ∘ F)) q)) := by
    simp_rw [fderiv_fderiv_clm_comp F q hF]
    exact ht
  exact isCompactOperator_of_tendsto he hc

/-- Bounded linear postcomposition preserves compact scalar Hessians. -/
theorem isCompactOperator_secondDerivative_clm_comp
    {E Y G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E → Y) (q : E) (hF : AnalyticAt ℝ F q) (ℓ : Y →L[ℝ] G)
    (hc : IsCompactOperator (fderiv ℝ (fderiv ℝ F) q)) :
    IsCompactOperator (fderiv ℝ (fderiv ℝ (ℓ ∘ F)) q) := by
  rw [fderiv_fderiv_clm_comp F q hF]
  exact hc.clm_comp ((ContinuousLinearMap.compL ℝ E Y G) ℓ)

/-- A finite sum of postcomposing functionals with compact Hessians has
compact Hessian, in the full source-to-dual operator norm. -/
theorem isCompactOperator_secondDerivative_clm_sum
    {E Y G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E → Y) (q : E) (hF : AnalyticAt ℝ F q)
    (a : ι → Y →L[ℝ] G) (s : Finset ι)
    (hc : ∀ i ∈ s, IsCompactOperator (fderiv ℝ (fderiv ℝ (a i ∘ F)) q)) :
    IsCompactOperator (fderiv ℝ (fderiv ℝ (((∑ i ∈ s, a i) : Y →L[ℝ] G) ∘ F)) q) := by
  let B : (Y →L[ℝ] G) →L[ℝ] E →L[ℝ] E →L[ℝ] G :=
    ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] Y) (E →L[ℝ] G)).flip
      (fderiv ℝ (fderiv ℝ F) q)).comp (ContinuousLinearMap.compL ℝ E Y G)
  have he (u : Y →L[ℝ] G) : fderiv ℝ (fderiv ℝ (u ∘ F)) q = B u :=
    fderiv_fderiv_clm_comp F q hF u
  rw [he,map_sum]
  have hc' : ∀ i ∈ s, IsCompactOperator (B (a i)) := by simpa only [he] using hc
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    change IsCompactOperator (0 : E → (E →L[ℝ] G))
    exact isCompactOperator_zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hc' i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
        (fun j hj => hc' j (Finset.mem_insert_of_mem hj)))

end NLS.FunctionalAnalysis
