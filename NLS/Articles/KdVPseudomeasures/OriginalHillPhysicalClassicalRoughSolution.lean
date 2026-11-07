import NLS.Articles.KdVPseudomeasures.OriginalHillClassicalRoughSolution
import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalRoughFlow

/-! The rough classical-approximation solution definition on the
original physical H-minus-one distributions. Every classical curve is
realized with its entire original Fourier sequence. Actual inverse
physical adapters transfer limits in both directions. -/
noncomputable section
open Set Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

def originalClassicalKdVCurve (f : ℝ × ℝ → ℂ) (hf : HillClassicalSpaceTimeKdVSolution f)
    (t : ℝ) : OriginalHminusOnePotential :=
  originalHillPotentialOfRealSource (hillClassicalSolutionRoughCurve f hf t)

def OriginalKdVSolutionByClassicalApproximation (q : OriginalHminusOnePotential)
    (γ : ℝ → OriginalHminusOnePotential) : Prop :=
  Continuous γ ∧ γ 0 = q ∧
  ∀ (F : ℕ → ℝ × ℝ → ℂ) (hF : ∀ j, HillClassicalSpaceTimeKdVSolution (F j)),
    Tendsto (fun j => originalClassicalKdVCurve (F j) (hF j) 0) atTop (𝓝 q) →
    ∀ t, Tendsto (fun j => originalClassicalKdVCurve (F j) (hF j) t) atTop (𝓝 (γ t))

theorem exists_originalClassical_approximating_solutions (q : OriginalHminusOnePotential) :
    ∃ (F : ℕ → ℝ × ℝ → ℂ) (hF : ∀ j, HillClassicalSpaceTimeKdVSolution (F j)),
      Tendsto (fun j => originalClassicalKdVCurve (F j) (hF j) 0) atTop (𝓝 q) := by
  obtain ⟨F,hF,hi⟩ := exists_hillClassical_approximating_solutions (originalHillRealMeanZeroSource q)
  refine ⟨F,hF,?_⟩
  have h := continuous_originalHillPotentialOfRealSource.continuousAt.tendsto.comp hi
  simpa only [Function.comp_def, originalHillPotentialOfRealSource_ofOriginal,
    originalClassicalKdVCurve] using! h

theorem hillOriginalCanonicalFlow_is_solutionByClassicalApproximation (q : OriginalHminusOnePotential) :
    OriginalKdVSolutionByClassicalApproximation q (hillOriginalCanonicalKdVFlow q) := by
  have ht : Continuous (hillOriginalCanonicalKdVFlow q) := by
    have hi : Continuous (fun t : ℝ => (t,q)) := continuous_id.prodMk continuous_const
    simpa only [Function.comp_def] using! continuous_hillOriginalCanonicalKdVFlow.comp hi
  refine ⟨ht,hillOriginalCanonicalKdVFlow_zero q,?_⟩
  intro F hF hi t
  have hreal := continuous_originalHillRealMeanZeroSource.continuousAt.tendsto.comp hi
  simp only [Function.comp_def, originalClassicalKdVCurve,
    originalHillRealMeanZeroSource_ofRealSource] at hreal
  have hr := (hillCanonicalFlow_is_roughSolutionByClassicalApproximation
    (originalHillRealMeanZeroSource q)).2.2 F hF hreal t
  have h := continuous_originalHillPotentialOfRealSource.continuousAt.tendsto.comp hr
  exact h

theorem originalKdVSolutionByClassicalApproximation_unique
    (q : OriginalHminusOnePotential) (γ : ℝ → OriginalHminusOnePotential)
    (hγ : OriginalKdVSolutionByClassicalApproximation q γ) : γ = hillOriginalCanonicalKdVFlow q := by
  let : T2Space OriginalHminusOnePotential := isClosedEmbedding_originalHminusOnePotential.isEmbedding.t2Space
  obtain ⟨F,hF,hi⟩ := exists_originalClassical_approximating_solutions q
  have hc := hillOriginalCanonicalFlow_is_solutionByClassicalApproximation q
  funext t
  exact tendsto_nhds_unique (hγ.2.2 F hF hi t) (hc.2.2 F hF hi t)

theorem existsUnique_originalKdVSolutionByClassicalApproximation (q : OriginalHminusOnePotential) :
    ∃! γ : ℝ → OriginalHminusOnePotential, OriginalKdVSolutionByClassicalApproximation q γ :=
  ⟨hillOriginalCanonicalKdVFlow q,hillOriginalCanonicalFlow_is_solutionByClassicalApproximation q,
    fun γ hγ => originalKdVSolutionByClassicalApproximation_unique q γ hγ⟩

end NLS.Articles.KdVPseudomeasures
