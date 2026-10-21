import NLS.ZakharovShabat.SourceBirkhoffInverseFourierSobolevBall
import NLS.ZakharovShabat.SourceRealTypeProjection
import NLS.SequenceSpaces.WeightedRealPairProjection

/-! # Exact real Sobolev projections

Bounded linear realizations preserve the literal Fourier coefficients and restore the original real conditions and component-sum norms.
-/

noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat

/-- Restore the native component-sum norm at the order gained by the
Fourier remainder, preserving every raw coefficient. -/
def strongerSobolevToNativePair (m : ℕ) :
    (WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 × WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2) →L[ℂ]
      WeightedCoeffPair (sourceFrequencyWeight (sourceSobolevSpectralWeight ((m+1:ℕ):ℝ) (Nat.cast_nonneg (m+1)))) 2 :=
  let L := WeightedCoeff.inclusionCLM (p := 2) (Weight.sobolev ((m:ℝ)+1))
    (sourceFrequencyWeight (sourceSobolevSpectralWeight ((m+1:ℕ):ℝ) (Nat.cast_nonneg (m+1)))) (by intro n; simp)
  (WeightedCoeffPair.toMax _ 2).symm.toContinuousLinearMap.comp (L.prodMap L)

@[simp] theorem strongerSobolevToNativePair_fst (m : ℕ)
    (v : WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 × WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2)
    (n : ℤ) : (strongerSobolevToNativePair m v).fst.val n = v.1.val n := by
  exact WeightedCoeff.inclusionCLM_apply _ _ (by intro j; simp) v.1 n

@[simp] theorem strongerSobolevToNativePair_snd (m : ℕ)
    (v : WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 × WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2)
    (n : ℤ) : (strongerSobolevToNativePair m v).snd.val n = v.2.val n := by
  exact WeightedCoeff.inclusionCLM_apply _ _ (by intro j; simp) v.2 n

/-- The bounded real projection onto the native weighted source form. -/
def weightedRealSourceProjection (w : SpectralWeight) :
    WeightedCoeffPair (sourceFrequencyWeight w) 2 →L[ℝ] weightedRealSourceSubmodule (p := 2) w :=
  (weightedRealSourceEquiv w).symm.toContinuousLinearMap.comp
    ((sourceRealTypeProjection (p := 2) (by norm_num)).comp
      ((sourcePairWeightCoordinates (p := 2) w).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ))

/-- Projection fixes every actual native real source. -/
theorem weightedRealSourceProjection_subtype (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := 2) w) :
    weightedRealSourceProjection w a.val = a := by
  change (weightedRealSourceEquiv w).symm
    (sourceRealTypeProjection (by norm_num) (weightedRealSourceEquiv w a).val) = a
  rw [sourceRealTypeProjection_subtype,ContinuousLinearEquiv.symm_apply_apply]

/-- Projection has the same ambient weighted value on the real subspace. -/
theorem weightedRealSourceProjection_val_of_mem (w : SpectralWeight)
    (v : WeightedCoeffPair (sourceFrequencyWeight w) 2) (hv : v ∈ weightedRealSourceSubmodule w) :
    (weightedRealSourceProjection w v).val = v := by
  exact congrArg Subtype.val (weightedRealSourceProjection_subtype w ⟨v,hv⟩)

/-- The stronger Fourier target as the exact native real target. -/
def strongerSobolevRealTargetProjection (m : ℕ) :
    (WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 × WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2) →L[ℝ]
      originalRealSobolevTarget (m+1) :=
  (WeightedCoeffPair.reCLM _).comp ((strongerSobolevToNativePair m).restrictScalars ℝ)

/-- The stronger inverse source as the exact native real source. -/
def strongerSobolevRealSourceProjection (m : ℕ) :
    (WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 × WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2) →L[ℝ]
      weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight ((m+1:ℕ):ℝ) (Nat.cast_nonneg (m+1))) :=
  (weightedRealSourceProjection _).comp ((strongerSobolevToNativePair m).restrictScalars ℝ)

/-- Real target projection preserves the complete literal coefficient pair. -/
theorem strongerSobolevRealTargetProjection_coordinates (m : ℕ)
    (v : WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 × WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2)
    (hv : ∀ n, (v.1.val n).im = 0 ∧ (v.2.val n).im = 0) (n : ℤ) :
    (strongerSobolevRealTargetProjection m v).fst.val.val n = v.1.val n ∧
    (strongerSobolevRealTargetProjection m v).snd.val.val n = v.2.val n := by
  have hx := WeightedCoeff.complexCLM_reCLM _ 2 (strongerSobolevToNativePair m v).fst
    (fun j => by simpa only [strongerSobolevToNativePair_fst] using (hv j).1)
  have hy := WeightedCoeff.complexCLM_reCLM _ 2 (strongerSobolevToNativePair m v).snd
    (fun j => by simpa only [strongerSobolevToNativePair_snd] using (hv j).2)
  constructor
  · exact (congrArg (fun c => c.val n) hx).trans (strongerSobolevToNativePair_fst m v n)
  · exact (congrArg (fun c => c.val n) hy).trans (strongerSobolevToNativePair_snd m v n)

/-- Real source projection preserves every coefficient of a real-type
stronger remainder, including the conjugate-reflection condition. -/
theorem strongerSobolevRealSourceProjection_coordinates (m : ℕ)
    (v : WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 × WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2)
    (hv : ∀ n, v.2.val n = conj (v.1.val (-n))) (n : ℤ) :
    (strongerSobolevRealSourceProjection m v).val.fst.val n = v.1.val n ∧
    (strongerSobolevRealSourceProjection m v).val.snd.val n = v.2.val n := by
  have hmem : strongerSobolevToNativePair m v ∈ weightedRealSourceSubmodule _ :=
    (mem_weightedRealSourceSubmodule_iff _ _).mpr (by
      intro j
      simpa only [strongerSobolevToNativePair_fst,strongerSobolevToNativePair_snd] using hv j)
  have he := weightedRealSourceProjection_val_of_mem _ (strongerSobolevToNativePair m v) hmem
  constructor
  · exact (congrArg (fun c => c.fst.val n) he).trans (strongerSobolevToNativePair_fst m v n)
  · exact (congrArg (fun c => c.snd.val n) he).trans (strongerSobolevToNativePair_snd m v n)

end NLS.ZakharovShabat
