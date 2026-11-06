import NLS.FunctionalAnalysis.SecondDerivativePostcomposition
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.SequenceSpaces

/-- Compact coordinate Hessians imply compactness of the Hessian paired
with ANY full sequence. Finite-output pairings converge in source-to-dual
operator norm by Banach analyticity, rather than just coordinatewise. -/
theorem isCompactOperator_secondDerivative_natL2_inner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → lp (fun _ : ℕ => ℂ) 2) (q : E) (hF : AnalyticAt ℝ F q)
    (hc : ∀ k : ℕ, IsCompactOperator
      (fderiv ℝ (fderiv ℝ (fun p => F p k)) q))
    (c : lp (fun _ : ℕ => ℂ) 2) :
    IsCompactOperator (fderiv ℝ (fderiv ℝ (fun p => inner ℝ c (F p))) q) := by
  let Y := lp (fun _ : ℕ => ℂ) 2
  let a : Finset ℕ → Y →L[ℝ] ℝ := fun s => innerSL ℝ (∑ k ∈ s,lp.single 2 k (c k))
  have ht : Tendsto a atTop (𝓝 (innerSL ℝ c)) :=
    (innerSL ℝ).continuous.continuousAt.tendsto.comp
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) c)
  have hsingle (k : ℕ) : IsCompactOperator
      (fderiv ℝ (fderiv ℝ ((innerSL ℝ (lp.single 2 k (c k))) ∘ F)) q) := by
    let e : Y →L[ℝ] ℂ := (lp.evalCLM (𝕜 := ℂ) (fun _ : ℕ => ℂ) 2 k).restrictScalars ℝ
    let v : ℂ →L[ℝ] ℝ := innerSL ℝ (c k)
    have he : innerSL ℝ (lp.single 2 k (c k)) = v.comp e := by
      ext y
      exact lp.inner_single_left (𝕜 := ℝ) k (c k) y
    rw [he]
    change IsCompactOperator (fderiv ℝ (fderiv ℝ (v ∘ (fun p => F p k))) q)
    exact NLS.FunctionalAnalysis.isCompactOperator_secondDerivative_clm_comp _ q
      ((e.analyticAt (F q)).comp hF) v (hc k)
  have hca (s : Finset ℕ) : IsCompactOperator (fderiv ℝ (fderiv ℝ (a s ∘ F)) q) := by
    dsimp only [a]
    rw [map_sum]
    exact NLS.FunctionalAnalysis.isCompactOperator_secondDerivative_clm_sum F q hF
      (fun k => innerSL ℝ (lp.single 2 k (c k))) s (fun k _ => hsingle k)
  exact NLS.FunctionalAnalysis.isCompactOperator_secondDerivative_of_dual_limit F q hF
    (innerSL ℝ c) a ht (Eventually.of_forall hca)

end NLS.SequenceSpaces
