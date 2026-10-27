import NLS.SequenceSpaces.WeightedActionOpening
import NLS.ZakharovShabat.SourceBirkhoffSobolevGlobalInverse

/-! # Sobolev regularity of the actual gap-opening curve

The original Birkhoff amplitude line lifts analytically in every native
nonnegative Sobolev norm. Its raw coefficients are exactly those of the
previous Hilbert curve, so all its gap and action identities are retained.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Pull the raw one-mode opening line through the actual Sobolev inverse. -/
def sobolevGapOpening (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ))
    (n : ℤ) (t : ℝ) : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ) :=
  (D.originalWeightedRealSobolevEquiv hp2 σ hσ).symm
    (Birkhoff.weightedActionOpening (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ))
      (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a) n t)

@[simp] theorem sobolevGapOpening_zero (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) (n : ℤ) :
    D.sobolevGapOpening hp2 σ hσ a n 0 = a := by
  simp only [sobolevGapOpening, Birkhoff.weightedActionOpening_zero]
  exact (D.originalWeightedRealSobolevEquiv hp2 σ hσ).symm_apply_apply a

/-- Analyticity holds in the full original weighted source norm. -/
theorem analyticOnNhd_sobolevGapOpening (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) (n : ℤ) :
    AnalyticOnNhd ℝ (D.sobolevGapOpening hp2 σ hσ a n) univ := by
  intro t _
  exact (D.originalWeightedRealSobolevEquiv_symm_analytic hp2 σ hσ _ (mem_univ _)).comp
    (Birkhoff.analyticOnNhd_weightedActionOpening _ _ n t (mem_univ _))

theorem tendsto_sobolevGapOpening_zero (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) (n : ℤ) :
    Tendsto (D.sobolevGapOpening hp2 σ hσ a n) (𝓝 0) (𝓝 a) := by
  simpa only [ContinuousAt, sobolevGapOpening_zero] using
    (D.analyticOnNhd_sobolevGapOpening hp2 σ hσ a n 0 (mem_univ _)).continuousAt

/-- The raw coefficients are exactly the unweighted inverse of the same line. -/
theorem originalWeightedRealSource_sobolevGapOpening
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ))
    (n : ℤ) (t : ℝ) :
    originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ)
      (D.sobolevGapOpening hp2 σ hσ a n t) =
      (D.realHomeomorph hp2).symm (RealCoeff.actionOpening
        (sourceRealBirkhoffMap hp hp1 s
          (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a)) n t) := by
  unfold sobolevGapOpening
  rw [D.originalWeightedRealSource_sobolevEquiv_symm]
  change (D.realHomeomorph hp2).symm
    (WeightedRealCoeff.forgetPairWeightCLM _ _ (Birkhoff.weightedActionOpening _ _ n t)) = _
  erw [Birkhoff.forget_weightedActionOpening]
  change (D.realHomeomorph hp2).symm (RealCoeff.actionOpening
    (originalWeightedRealTarget _ (D.originalWeightedRealMap _ a)) n t) = _
  rw [D.originalWeightedRealTarget_map]

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
