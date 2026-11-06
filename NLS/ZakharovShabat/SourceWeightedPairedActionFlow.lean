import NLS.ZakharovShabat.SourcePairedActionFlowSobolev
import NLS.ZakharovShabat.SourceBirkhoffSobolevGlobalInverse
import NLS.Dynamics.WeightedPairedActionRotation

/-! # The complete paired flow in its full native Sobolev topology

The proved weighted global inverse gives a continuous lift at every
nonnegative real Sobolev order. Forgetting the weight recovers exactly
the actual L2 Hamiltonian flow, with every raw Fourier coefficient intact.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

def weightedPairedActionFlow
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ))
    (k l : ℤ) (t : ℝ) : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ) :=
  (D.originalWeightedRealSobolevHomeomorph le_rfl σ hσ).symm
    (Birkhoff.weightedRealPairedActionRotation (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ))
      (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a) k l t)

theorem originalWeightedRealSource_pairedActionFlow
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ))
    (k l : ℤ) (t : ℝ) :
    originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (D.weightedPairedActionFlow σ hσ a k l t) =
      D.hilbertPairedActionFlow (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a) k l t := by
  let w := sourceSobolevSpectralWeight σ hσ
  have ht : D.originalWeightedRealMap w (D.weightedPairedActionFlow σ hσ a k l t) =
      Birkhoff.weightedRealPairedActionRotation (sourceFrequencyWeight w) (D.originalWeightedRealMap w a) k l t :=
    (D.originalWeightedRealSobolevHomeomorph le_rfl σ hσ).apply_symm_apply _
  apply D.hilbertRealHomeomorph.injective
  rw [hilbertRealHomeomorph_apply,← D.originalWeightedRealTarget_map w,ht]
  change WeightedRealCoeff.forgetPairWeightCLM (sourceFrequencyWeight w) (fun n => w.one_le (2*n))
    (Birkhoff.weightedRealPairedActionRotation (sourceFrequencyWeight w) (D.originalWeightedRealMap w a) k l t) = _
  erw [Birkhoff.forget_weightedRealPairedActionRotation,D.hilbertRealHomeomorph_pairedActionFlow,
    D.hilbertRealHomeomorph_apply,← D.originalWeightedRealTarget_map w a]
  rfl

set_option maxHeartbeats 800000 in
theorem continuous_weightedPairedActionFlow
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (σ : ℝ) (hσ : 0 ≤ σ) (k l : ℤ) :
    Continuous (fun x : ℝ × weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ) =>
      D.weightedPairedActionFlow σ hσ x.2 k l x.1) := by
  let w := sourceSobolevSpectralWeight σ hσ
  have hpair : Continuous (fun x : ℝ × weightedRealSourceSubmodule (p := 2) w =>
      (x.1,D.originalWeightedRealMap w x.2)) :=
    continuous_fst.prodMk ((D.originalWeightedRealMap_continuous w).comp continuous_snd)
  have hrot := (Birkhoff.continuous_weightedRealPairedActionRotation (sourceFrequencyWeight w) k l).comp hpair
  exact (D.originalWeightedRealSobolevHomeomorph le_rfl σ hσ).symm.continuous.comp hrot

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
