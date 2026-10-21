import NLS.ZakharovShabat.SourceBirkhoffFourierRemainder
import NLS.ZakharovShabat.SourceBirkhoffSobolevGlobalInverse

/-! # Original Sobolev source conversion for one-smoothing

The native weighted source converts contractively to the higher Sobolev source with identical Fourier coefficients. The canonical remainder is real analytic on the entire native real space.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Convert the native component-sum Sobolev source to the maximum-norm
higher source, preserving the original Fourier coefficients. -/
def originalSobolevToHigher (m : ℕ) :
    WeightedCoeffPair (sourceFrequencyWeight (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) 2
      →L[ℂ] SobolevSource m :=
  let L := WeightedCoeff.inclusionCLM (p := 2)
    (sourceFrequencyWeight (sourceSobolevSpectralWeight m (Nat.cast_nonneg m)))
    (Weight.sobolev m) (by intro n; simp)
  (L.prodMap L).comp (WeightedCoeffPair.toMax _ 2).toContinuousLinearMap

@[simp] theorem originalSobolevToHigher_fst (m : ℕ)
    (a : WeightedCoeffPair (sourceFrequencyWeight (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) 2)
    (n : ℤ) : (originalSobolevToHigher m a).1.val n = a.fst.val n := by
  simp [originalSobolevToHigher]

@[simp] theorem originalSobolevToHigher_snd (m : ℕ)
    (a : WeightedCoeffPair (sourceFrequencyWeight (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) 2)
    (n : ℤ) : (originalSobolevToHigher m a).2.val n = a.snd.val n := by
  simp [originalSobolevToHigher]

/-- The change from the native pair norm to the higher source is contractive. -/
theorem norm_originalSobolevToHigher_le (m : ℕ)
    (a : WeightedCoeffPair (sourceFrequencyWeight (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) 2) :
    ‖originalSobolevToHigher m a‖ ≤ ‖a‖ := by
  apply le_trans _ (WeightedCoeffPair.norm_toMax_le _ a)
  change max ‖WeightedCoeff.inclusionCLM _ _ (by intro n; simp) a.fst‖
    ‖WeightedCoeff.inclusionCLM _ _ (by intro n; simp) a.snd‖ ≤ max ‖a.fst‖ ‖a.snd‖
  exact max_le_max (WeightedCoeff.norm_inclusionCLM_le _ _ _ _)
    (WeightedCoeff.norm_inclusionCLM_le _ _ _ _)

/-- Both source representations have exactly the same unweighted inclusion. -/
theorem higherSobolevSourceInclusion_originalSobolevToHigher (m : ℕ)
    (a : WeightedCoeffPair (sourceFrequencyWeight (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) 2) :
    higherSobolevSourceInclusion m (originalSobolevToHigher m a) =
      originalWeightedSourceCLM (sourceSobolevSpectralWeight m (Nat.cast_nonneg m)) a := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n <;> simp

/-- Restrict the coefficient-preserving conversion to the actual real
Sobolev source Banach space. -/
def originalRealSobolevToHigher (m : ℕ) :
    weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))
      →L[ℝ] SobolevSource m :=
  ((originalSobolevToHigher m).restrictScalars ℝ).comp
    (weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))).subtypeL

/-- The real weighted source converts to a real original higher source. -/
theorem originalRealSobolevToHigher_real (m : ℕ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) :
    IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion m (originalRealSobolevToHigher m a))) := by
  change IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion m (originalSobolevToHigher m a.val)))
  rw [higherSobolevSourceInclusion_originalSobolevToHigher, originalWeightedSourceCLM_real]
  exact (originalWeightedRealSource _ a).property

/-- The real source conversion is contractive in the stated native norms. -/
theorem norm_originalRealSobolevToHigher_le (m : ℕ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) :
    ‖originalRealSobolevToHigher m a‖ ≤ ‖a‖ :=
  norm_originalSobolevToHigher_le m a.val

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- The canonical stronger Fourier remainder is real analytic on the
entire native real Sobolev space used by the global inverse. -/
theorem higherSobolevBirkhoffFourierRemainder_originalReal_analytic
    (m : ℕ) (hm : 1 ≤ m) :
    AnalyticOnNhd ℝ (fun a => higherSobolevBirkhoffFourierRemainder m s
      (originalRealSobolevToHigher m a)) univ := by
  intro a _
  have h : AnalyticAt ℝ (higherSobolevBirkhoffFourierRemainder m s)
      (originalRealSobolevToHigher m a) :=
    (D.higherSobolevBirkhoffFourierRemainder_analyticAt_real m hm
      ⟨originalRealSobolevToHigher m a,originalRealSobolevToHigher_real m a⟩).restrictScalars
  exact h.comp ((originalRealSobolevToHigher m).analyticAt a)

/-- The remainder remains uniformly bounded on native real Sobolev balls. -/
theorem higherSobolevBirkhoffFourierRemainder_originalReal_uniform_ball
    (m : ℕ) (hm : 1 ≤ m) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : weightedRealSourceSubmodule (p := 2)
      (sourceSobolevSpectralWeight m (Nat.cast_nonneg m)), ‖a‖ ≤ R →
      ‖higherSobolevBirkhoffFourierRemainder m s (originalRealSobolevToHigher m a)‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := D.higherSobolevBirkhoffFourierRemainder_uniform_real_ball m hm R hR
  refine ⟨C,hC,fun a ha => h
    ⟨originalRealSobolevToHigher m a,originalRealSobolevToHigher_real m a⟩
      ((norm_originalRealSobolevToHigher_le m a).trans ha)⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
