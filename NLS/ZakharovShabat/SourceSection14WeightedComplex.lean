import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexDerivative
import NLS.ZakharovShabat.SourceSection14

/-! # Section 14 in the full weighted complex topology

One actual Section 14 construction extends analytically to a neighborhood
of every weighted real source for every spectral weight and finite p>1.
Both the map and its full weighted Jacobian commute with the original
unweighted inclusions. Invertibility of that weighted Jacobian and analytic
weighted inverse maps remain separate assertions.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Constructed weighted complex analyticity and full derivative compatibility. -/
theorem sourceSection14_weighted_complex_analytic (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ _D : SourceSection14Data hp hp1 W₀ W V s, ∀ w : SpectralWeight,
        ∃ U : Set (WeightedCoeffPair (sourceFrequencyWeight w) p), IsOpen U ∧
          (∀ a : weightedRealSourceSubmodule (p := p) w, a.val ∈ U) ∧
          AnalyticOnNhd ℂ (originalWeightedBirkhoffMap hp hp1 s w) U ∧
          ∀ a ∈ U, originalWeightedSourceCLM w a ∈ V ∧
            weightedBirkhoffTargetInclusion w (originalWeightedBirkhoffMap hp hp1 s w a) =
              sourceBirkhoffMap hp hp1 s (originalWeightedSourceCLM w a) ∧
            (weightedBirkhoffTargetInclusion w).comp (fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a) =
              (fderiv ℂ (sourceBirkhoffMap hp hp1 s) (originalWeightedSourceCLM w a)).comp
                (originalWeightedSourceCLM w) := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 hp hp1
  exact ⟨W₀,W,V,s,D,fun w => D.complex.exists_originalWeightedBirkhoffMap_compatible_derivative w⟩

end NLS.ZakharovShabat
