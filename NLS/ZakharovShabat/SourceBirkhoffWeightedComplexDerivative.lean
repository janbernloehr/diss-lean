import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexAnalytic

/-! # The actual weighted Jacobian and its unweighted inclusion

The full weighted Fréchet derivative is a bounded linear map. Forgetting
the target weight commutes with both the complex Birkhoff map and its
derivative, on the constructed common complex domain.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Include weighted rectangular outputs in the original unweighted target. -/
def weightedBirkhoffTargetInclusion (w : SpectralWeight) :
    WeightedCoeffPair (sourceFrequencyWeight w) p →L[ℂ] (Coeff p × Coeff p) :=
  (CoeffPair.toMax p).toContinuousLinearMap.comp (originalWeightedSourceCLM w)

@[simp] theorem weightedBirkhoffTargetInclusion_fst (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) (n : ℤ) :
    (weightedBirkhoffTargetInclusion w a).1 n = a.fst.val n := originalWeightedSourceCLM_fst w a n

@[simp] theorem weightedBirkhoffTargetInclusion_snd (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) (n : ℤ) :
    (weightedBirkhoffTargetInclusion w a).2 n = a.snd.val n := originalWeightedSourceCLM_snd w a n

private theorem derivative_intertwines
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (J : E →L[ℂ] F) (K : G →L[ℂ] H) (f : E → G) (g : F → H)
    (U : Set E) (hU : IsOpen U) (a : E) (ha : a ∈ U)
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g (J a))
    (he : ∀ b ∈ U, K (f b) = g (J b)) :
    K.comp (fderiv ℂ f a) = (fderiv ℂ g (J a)).comp J := by
  have h₁ := K.hasFDerivAt.comp a hf.differentiableAt.hasFDerivAt
  have h₂ := hg.differentiableAt.hasFDerivAt.comp a J.hasFDerivAt
  have hEq : (fun b => g (J b)) =ᶠ[𝓝 a] fun b => K (f b) := by
    filter_upwards [hU.mem_nhds ha] with b hb
    exact (he b hb).symm
  exact (h₁.congr_of_eventuallyEq hEq).unique h₂

private theorem target_inclusion_eq_of_coordinates (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) (b : Coeff p × Coeff p)
    (h : ∀ n : ℤ, a.fst.val n = b.1 n ∧ a.snd.val n = b.2 n) :
    weightedBirkhoffTargetInclusion w a = b := by
  apply Prod.ext <;> ext n
  · rw [weightedBirkhoffTargetInclusion_fst]
    exact (h n).1
  · rw [weightedBirkhoffTargetInclusion_snd]
    exact (h n).2

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Native weighted analyticity and exact compatibility of the full bounded Jacobian. -/
theorem exists_originalWeightedBirkhoffMap_compatible_derivative
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight) :
    ∃ V : Set (WeightedCoeffPair (sourceFrequencyWeight w) p), IsOpen V ∧
      (∀ a : weightedRealSourceSubmodule (p := p) w, a.val ∈ V) ∧
      AnalyticOnNhd ℂ (originalWeightedBirkhoffMap hp hp1 s w) V ∧
      ∀ a ∈ V, originalWeightedSourceCLM w a ∈ W ∧
        weightedBirkhoffTargetInclusion w (originalWeightedBirkhoffMap hp hp1 s w a) =
          sourceBirkhoffMap hp hp1 s (originalWeightedSourceCLM w a) ∧
        (weightedBirkhoffTargetInclusion w).comp (fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a) =
          (fderiv ℂ (sourceBirkhoffMap hp hp1 s) (originalWeightedSourceCLM w a)).comp (originalWeightedSourceCLM w) := by
  obtain ⟨V,hoV,hreal,hVW,hA,hcoord⟩ := D.exists_originalWeightedBirkhoffMap_analytic w
  have he a (ha : a ∈ V) : weightedBirkhoffTargetInclusion w (originalWeightedBirkhoffMap hp hp1 s w a) =
      sourceBirkhoffMap hp hp1 s (originalWeightedSourceCLM w a) := by
    exact target_inclusion_eq_of_coordinates w _ _ (hcoord a ha)
  refine ⟨V,hoV,hreal,hA,fun a ha => ⟨hVW a ha,he a ha,?_⟩⟩
  exact derivative_intertwines (originalWeightedSourceCLM w) (weightedBirkhoffTargetInclusion w)
    (originalWeightedBirkhoffMap hp hp1 s w) (sourceBirkhoffMap hp hp1 s) V hoV a ha
    (hA a ha) (D.analytic _ (hVW a ha)) he

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
