import NLS.Dynamics.WeightedRealPhaseFlow
import NLS.ZakharovShabat.SourceBirkhoffSobolevGlobalInverse
import NLS.ZakharovShabat.SourceRenormalizedFlow

/-! # Almost-periodic phase lifts through the native Sobolev inverse

The actual weighted norms and original coefficients are retained throughout.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
namespace SourceBirkhoffMapComplexData

/-- Lift a Hamiltonian phase orbit through the actual native Sobolev inverse. -/
def weightedSourcePhaseFlow (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) (ω : ℤ → ℝ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ))
    (t : ℝ) : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ) :=
  (D.originalWeightedRealSobolevHomeomorph hp2 σ hσ).symm
    (Birkhoff.weightedRealPhaseFlow (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ))
      ω t (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a))

/-- The full native Sobolev norm has relatively dense uniform return times,
at every nonnegative real regularity. -/
theorem bohrAlmostPeriodic_weightedSourcePhaseFlow
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) (ω : ℤ → ℝ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) :
    Dynamics.BohrAlmostPeriodic (D.weightedSourcePhaseFlow hp2 σ hσ ω a) := by
  let w := sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ)
  exact Birkhoff.bohrAlmostPeriodic_hamiltonianPhaseFlow_comp hp ω
    (Birkhoff.encodeReal (Birkhoff.weightedRealCoordinates w
      (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a)))
    (fun z => (D.originalWeightedRealSobolevHomeomorph hp2 σ hσ).symm
      ((Birkhoff.weightedRealCoordinates w).symm (Birkhoff.decodeReal z)))
    ((D.originalWeightedRealSobolevHomeomorph hp2 σ hσ).symm.continuous.comp
      ((Birkhoff.weightedRealCoordinates w).symm.continuous.comp Birkhoff.decodeReal.continuous))

/-- Forgetting the native Sobolev weight recovers the same original phase curve,
with its exact raw coefficients and Hamiltonian time orientation. -/
theorem originalWeightedRealSource_weightedSourcePhaseFlow
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) (ω : ℤ → ℝ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ))
    (t : ℝ) :
    originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ)
      (D.weightedSourcePhaseFlow hp2 σ hσ ω a t) =
    (D.realHomeomorph hp2).symm (Birkhoff.decodeReal
      (Birkhoff.hamiltonianPhaseFlow ω t (sourceComplexBirkhoffMap hp hp1 s
        (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a).val))) := by
  unfold weightedSourcePhaseFlow
  change originalWeightedRealSource _ ((D.originalWeightedRealSobolevEquiv hp2 σ hσ).symm _) = _
  rw [D.originalWeightedRealSource_sobolevEquiv_symm]
  change (D.realHomeomorph hp2).symm
    (WeightedRealCoeff.forgetPairWeightCLM _ _
      (Birkhoff.weightedRealPhaseFlow _ ω t _)) = _
  erw [Birkhoff.forget_weightedRealPhaseFlow]
  change (D.realHomeomorph hp2).symm (Birkhoff.decodeReal
    (Birkhoff.hamiltonianPhaseFlow ω t (Birkhoff.encodeReal
      (originalWeightedRealTarget _ (D.originalWeightedRealMap _ a))))) = _
  rw [D.originalWeightedRealTarget_map,D.encode_real_map]

@[simp] theorem weightedSourcePhaseFlow_zero
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (σ : ℝ) (hσ : 0 ≤ σ) (ω : ℤ → ℝ)
    (a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight σ hσ)) :
    D.weightedSourcePhaseFlow hp2 σ hσ ω a 0 = a := by
  simp only [weightedSourcePhaseFlow,Birkhoff.weightedRealPhaseFlow,
    Birkhoff.hamiltonianPhaseFlow_zero,Birkhoff.decodeReal_encodeReal,
    ContinuousLinearEquiv.symm_apply_apply]
  exact (D.originalWeightedRealSobolevHomeomorph hp2 σ hσ).symm_apply_apply a

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
