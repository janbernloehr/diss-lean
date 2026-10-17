import NLS.SequenceSpaces.WeightedRealPairProjection
import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexAnalytic

/-! # Real analyticity of the original weighted Birkhoff map

Restrict the constructed complex extension and apply the bounded real-part
projection. Exact raw coefficients identify the result with the original map.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
private theorem analytic_real_linear_transport
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : E →L[ℝ] F) (L : G →L[ℝ] H) (f : F → G) (a : E)
    (hf : AnalyticAt ℂ f (J a)) :
    AnalyticAt ℝ (fun b => L (f (J b))) a := by
  exact (L.analyticAt _).comp (f := fun b => f (J b))
    ((hf.restrictScalars (𝕜 := ℝ)).comp (J.analyticAt a))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Full real power-series analyticity in the native weighted source and target norms. -/
theorem originalWeightedRealMap_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight) :
    AnalyticOnNhd ℝ (D.originalWeightedRealMap w) univ := by
  have he : D.originalWeightedRealMap w = fun a =>
      WeightedCoeffPair.reCLM (sourceFrequencyWeight w) (originalWeightedBirkhoffMap hp hp1 s w a.val) := by
    funext a
    exact (WeightedCoeffPair.reCLM_pair_eq_of_coordinates (sourceFrequencyWeight w)
      _ _ (D.originalWeightedBirkhoffMap_real w a)).symm
  rw [he]
  obtain ⟨U,_,hr,_,hA,_⟩ := D.exists_originalWeightedBirkhoffMap_analytic w
  intro a _
  exact analytic_real_linear_transport (weightedRealSourceSubmodule (p := p) w).subtypeL
    (WeightedCoeffPair.reCLM (sourceFrequencyWeight w)) (originalWeightedBirkhoffMap hp hp1 s w) a
    (hA a.val (hr a))
end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
