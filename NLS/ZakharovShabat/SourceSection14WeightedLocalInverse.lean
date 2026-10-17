import NLS.ZakharovShabat.SourceBirkhoffWeightedLocalInverse
import NLS.ZakharovShabat.SourceSection14

/-! # Constructed weighted Jacobians and actual analytic local inverses

One Section 14 construction supplies the weighted maps for every spectral
weight. Their full native complex derivatives are bijective at every real
source, and the actual maps have two-sided complex analytic inverse germs.
No derivative equivalence, inverse function, or compactness premise is
supplied by the caller.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Construct the original family before choosing the weight or real source,
then supply the bijective native Jacobian and both actual inverse germs. -/
theorem sourceSection14_weighted_complex_local_inverse (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection14Data hp hp1 W₀ B W s, ∀ w : SpectralWeight,
        ∀ a : weightedRealSourceSubmodule (p := p) w,
          Function.Bijective (fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a.val) ∧
          ∃ g : WeightedCoeffPair (sourceFrequencyWeight w) p → WeightedCoeffPair (sourceFrequencyWeight w) p,
            AnalyticAt ℂ g (originalWeightedBirkhoffMap hp hp1 s w a.val) ∧
            g (originalWeightedBirkhoffMap hp hp1 s w a.val) = a.val ∧
            (∀ᶠ b in 𝓝 a.val, g (originalWeightedBirkhoffMap hp hp1 s w b) = b) ∧
            (∀ᶠ z in 𝓝 (originalWeightedBirkhoffMap hp hp1 s w a.val), originalWeightedBirkhoffMap hp hp1 s w (g z) = z) ∧
            HasStrictFDerivAt g (D.complex.originalWeightedJacobianEquiv w a).symm.toContinuousLinearMap
              (originalWeightedBirkhoffMap hp hp1 s w a.val) := by
  obtain ⟨W₀,B,W,s,D⟩ := sourceSection14 hp hp1
  exact ⟨W₀,B,W,s,D,fun w a => ⟨D.complex.originalWeightedBirkhoffMap_fderiv_bijective w a,
    D.complex.exists_originalWeighted_complex_localInverse w a⟩⟩

end NLS.ZakharovShabat
