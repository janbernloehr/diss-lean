import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexDerivative

/-! # A fixed domain for each actual weighted complex map

The domain depends on one family and weight, so comparisons with other
families all use the same domain.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- A fixed common analytic weighted domain for this original family. -/
def originalWeightedComplexDomain (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) : Set (WeightedCoeffPair (sourceFrequencyWeight w) p) :=
  (D.exists_originalWeightedBirkhoffMap_compatible_derivative w).choose

/-- The chosen domain retains all real sources, analyticity, and both inclusion identities. -/
theorem originalWeightedComplexDomain_spec (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) :
    IsOpen (D.originalWeightedComplexDomain w) ∧
      (∀ a : weightedRealSourceSubmodule (p := p) w, a.val ∈ D.originalWeightedComplexDomain w) ∧
      AnalyticOnNhd ℂ (originalWeightedBirkhoffMap hp hp1 s w) (D.originalWeightedComplexDomain w) ∧
      ∀ a ∈ D.originalWeightedComplexDomain w, originalWeightedSourceCLM w a ∈ W ∧
        weightedBirkhoffTargetInclusion w (originalWeightedBirkhoffMap hp hp1 s w a) =
          sourceBirkhoffMap hp hp1 s (originalWeightedSourceCLM w a) ∧
        (weightedBirkhoffTargetInclusion w).comp (fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a) =
          (fderiv ℂ (sourceBirkhoffMap hp hp1 s) (originalWeightedSourceCLM w a)).comp (originalWeightedSourceCLM w) :=
  (D.exists_originalWeightedBirkhoffMap_compatible_derivative w).choose_spec
end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
