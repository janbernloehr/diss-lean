import NLS.ZakharovShabat.SourceBirkhoffSobolevGlobalInverse
import NLS.ZakharovShabat.SourceRealTypeProjection
import NLS.ComplexAnalysis.ContinuousMapAnalyticInverse

/-! # Analytic Sobolev Birkhoff inversion on compact trajectory spaces -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {K : Type} [TopologicalSpace K] [CompactSpace K]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Apply the actual global Sobolev inverse at every time, retaining the
native weighted source and target norms. -/
def sobolevInverseTrajectory (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ)
    (z : C(K, WithLp p (WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ)) p ×
      WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ)) p))) :
    C(K, weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) where
  toFun k := (D.originalWeightedRealSobolevHomeomorph hp2 σ hσ).symm (z k)
  continuous_toFun := (D.originalWeightedRealSobolevHomeomorph hp2 σ hσ).symm.continuous.comp z.continuous

/-- Inversion is continuous for the full compact-time uniform Sobolev norm. -/
theorem continuous_sobolevInverseTrajectory
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) :
    Continuous (D.sobolevInverseTrajectory (K := K) hp2 σ hσ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (D.originalWeightedRealSobolevHomeomorph hp2 σ hσ).symm.continuous.comp continuous_eval

/-- The actual inverse acts real analytically on complete compact trajectories,
for every real nonnegative Sobolev order, in the stronger uniform norm. -/
theorem analytic_sobolevInverseTrajectory
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) :
    AnalyticOnNhd ℝ (D.sobolevInverseTrajectory (K := K) hp2 σ hσ) univ := by
  let w := sourceSobolevSpectralWeight σ hσ
  let E := weightedRealSourceSubmodule (p := p) w
  let G := D.sobolevInverseTrajectory (K := K) hp2 σ hσ
  let J := (weightedRealSourceSubmodule (p := p) w).subtypeL.compLeftContinuous ℝ K
  let L := (WeightedCoeffPair.complexCLM (p := p) (sourceFrequencyWeight w)).compLeftContinuous ℝ K
  let R : WeightedCoeffPair (sourceFrequencyWeight w) p →L[ℝ] E :=
    (weightedRealSourceEquiv w).symm.toContinuousLinearMap.comp
      ((sourceRealTypeProjection hp).comp
        ((sourcePairWeightCoordinates (p := p) w).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ))
  have hR (a : E) : R a.val = a := by
    change (weightedRealSourceEquiv w).symm (sourceRealTypeProjection hp (weightedRealSourceEquiv w a).val) = a
    rw [sourceRealTypeProjection_subtype,ContinuousLinearEquiv.symm_apply_apply]
  have hspec := D.originalWeightedComplexDomain_spec w
  have he (z : C(K, WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p ×
      WeightedRealCoeff (sourceFrequencyWeight w) p))) :
      superposition (originalWeightedBirkhoffMap hp hp1 s w) (J (G z)) = L z := by
    apply ContinuousMap.ext
    intro k
    rw [superposition_apply hspec.2.2.1.continuousOn (by
      rintro _ ⟨j,rfl⟩
      exact hspec.2.1 (G z j))]
    change originalWeightedBirkhoffMap hp hp1 s w (G z k).val =
      WeightedCoeffPair.complexCLM (sourceFrequencyWeight w) (z k)
    rw [← D.originalWeightedRealMap_complex_inclusion]
    change WeightedCoeffPair.complexCLM (sourceFrequencyWeight w)
      (D.originalWeightedRealSobolevHomeomorph hp2 σ hσ
        ((D.originalWeightedRealSobolevHomeomorph hp2 σ hσ).symm (z k))) = _
    rw [Homeomorph.apply_symm_apply]
  intro z _
  have ha : AnalyticAt ℝ (fun y => J (G y)) z := by
    apply analyticAt_real_lift_of_superposition hspec.1 hspec.2.2.1
      (fun y => J (G y)) z
    · exact (J.continuous.comp (D.continuous_sobolevInverseTrajectory hp2 σ hσ)).continuousAt
    · rintro _ ⟨k,rfl⟩
      exact hspec.2.1 (G z k)
    · intro k
      exact ⟨D.originalWeightedJacobianEquiv w (G z k),rfl⟩
    · simpa only [he] using L.analyticAt z
  have hr (y : C(K, WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p ×
      WeightedRealCoeff (sourceFrequencyWeight w) p))) :
      (R.compLeftContinuous ℝ K) (J (G y)) = G y := by
    apply ContinuousMap.ext
    intro k
    exact hR (G y k)
  simpa only [Function.comp_def,hr] using!
    ((R.compLeftContinuous ℝ K).analyticAt _).comp ha

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
