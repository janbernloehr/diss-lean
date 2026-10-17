import NLS.ZakharovShabat.SourceBirkhoffWeightedImageInverse
import NLS.ZakharovShabat.SourceBirkhoffSobolevGlobalInverse
import NLS.ZakharovShabat.SourceSection14

/-! # Constructed weighted real local inverses and Sobolev global inverses

One original Section 14 family supplies real analytic local inverses for
every spectral weight. In the onto exponent range it supplies the global
Sobolev homeomorphism with both analytic directions for every real order t>=0.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Construct the original family before choosing any spectral weight or real source. -/
theorem sourceSection14_weighted_real_local_inverse (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection14Data hp hp1 W₀ B W s, ∀ w : SpectralWeight,
        IsOpenEmbedding (D.complex.originalWeightedRealMap w) ∧
        ∀ a : weightedRealSourceSubmodule (p := p) w,
          Function.Bijective (fderiv ℝ (D.complex.originalWeightedRealMap w) a) ∧
          ∃ g : WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p) →
              weightedRealSourceSubmodule (p := p) w,
            AnalyticAt ℝ g (D.complex.originalWeightedRealMap w a) ∧
            g (D.complex.originalWeightedRealMap w a) = a ∧
            (∀ᶠ b in 𝓝 a, g (D.complex.originalWeightedRealMap w b) = b) ∧
            (∀ᶠ z in 𝓝 (D.complex.originalWeightedRealMap w a), D.complex.originalWeightedRealMap w (g z) = z) ∧
            HasStrictFDerivAt g (D.complex.originalWeightedRealJacobianEquiv w a).symm.toContinuousLinearMap
              (D.complex.originalWeightedRealMap w a) := by
  obtain ⟨W₀,B,W,s,D⟩ := sourceSection14 hp hp1
  exact ⟨W₀,B,W,s,D,fun w => ⟨D.complex.originalWeightedRealMap_isOpenEmbedding w,fun a =>
    ⟨D.complex.originalWeightedRealMap_fderiv_bijective w a,D.complex.exists_originalWeighted_real_localInverse w a⟩⟩⟩

/-- One constructed family gives the actual global analytic Sobolev inverse at every t>=0. -/
theorem sourceSection14_sobolev_global_analytic_inverse (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection14Data hp hp1 W₀ B W s, ∀ t : ℝ, ∀ ht : 0 ≤ t,
        ∃ e : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight t ht) ≃ₜ
            WithLp p (WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p ×
              WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) p),
          (∀ a, e a = D.complex.originalWeightedRealMap (sourceSobolevSpectralWeight t ht) a) ∧
          (∀ z, e.symm z = (D.complex.originalWeightedRealSobolevEquiv hp2 t ht).symm z) ∧
          AnalyticOnNhd ℝ e univ ∧ AnalyticOnNhd ℝ e.symm univ := by
  obtain ⟨W₀,B,W,s,D⟩ := sourceSection14 hp hp1
  refine ⟨W₀,B,W,s,D,fun t ht => ?_⟩
  exact ⟨D.complex.originalWeightedRealSobolevHomeomorph hp2 t ht,fun _ => rfl,fun _ => rfl,
    D.complex.originalWeightedRealSobolevHomeomorph_analytic hp2 t ht,
    D.complex.originalWeightedRealSobolevHomeomorph_symm_analytic hp2 t ht⟩

end NLS.ZakharovShabat
