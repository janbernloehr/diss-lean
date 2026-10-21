import NLS.ZakharovShabat.SourceSobolevNativeBridge
import NLS.ZakharovShabat.SourceBirkhoffFourierEquivalence

/-! # The analytic one-smoothing inverse Fourier remainder

Composition with the actual global Sobolev inverse gives a stronger-target real analytic inverse remainder, with exact reflected Fourier coefficients and normalization.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The source Fourier inverse preserves every Sobolev order, including
the reflected first component and exact square-root normalization. -/
def sourceSobolevBirkhoffFourierInverse (t : ℝ) :
    (WeightedCoeff (Weight.sobolev t) 2 × WeightedCoeff (Weight.sobolev t) 2) →L[ℂ]
      (WeightedCoeff (Weight.sobolev t) 2 × WeightedCoeff (Weight.sobolev t) 2) :=
  let x := ContinuousLinearMap.fst ℂ (WeightedCoeff (Weight.sobolev t) 2) _
  let y := ContinuousLinearMap.snd ℂ (WeightedCoeff (Weight.sobolev t) 2) _
  let a := (WeightedCoeff.reflection t).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((-1:ℂ)/(Real.sqrt 2:ℂ)) • (x-I • y))
  let b := ((-1:ℂ)/(Real.sqrt 2:ℂ)) • (x+I • y)
  a.prod b

@[simp] theorem sourceSobolevBirkhoffFourierInverse_fst (t : ℝ)
    (v : WeightedCoeff (Weight.sobolev t) 2 × WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    (sourceSobolevBirkhoffFourierInverse t v).1.val n =
      -(v.1.val (-n)-I*v.2.val (-n))/(Real.sqrt 2:ℂ) := by
  change ((WeightedCoeff.reflection t) (((-1:ℂ)/(Real.sqrt 2:ℂ)) • (v.1-I • v.2))).val n = _
  simp only [WeightedCoeff.reflection_apply,WeightedCoeff.smul_val,WeightedCoeff.sub_val]
  ring

@[simp] theorem sourceSobolevBirkhoffFourierInverse_snd (t : ℝ)
    (v : WeightedCoeff (Weight.sobolev t) 2 × WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    (sourceSobolevBirkhoffFourierInverse t v).2.val n =
      -(v.1.val n+I*v.2.val n)/(Real.sqrt 2:ℂ) := by
  change (((-1:ℂ)/(Real.sqrt 2:ℂ)) • (v.1+I • v.2)).val n = _
  simp only [WeightedCoeff.smul_val,WeightedCoeff.add_val]
  ring

/-- The native real target of the original Sobolev Birkhoff bijection. -/
abbrev originalRealSobolevTarget (m : ℕ) :=
  WithLp 2 (WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) 2 ×
    WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) 2)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)

/-- The inverse-minus-inverse-Fourier remainder as an actual h^(m+1)
source pair, using the same global Sobolev inverse and Birkhoff family. -/
def inverseSobolevFourierRemainder (m : ℕ) (z : originalRealSobolevTarget m) :
    WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 × WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 :=
  -(sourceSobolevBirkhoffFourierInverse ((m:ℝ)+1)
    (higherSobolevBirkhoffFourierRemainder m s (originalRealSobolevToHigher m
      ((D.originalWeightedRealSobolevEquiv (by norm_num) m (Nat.cast_nonneg m)).symm z))))

/-- The inverse remainder is real analytic into the space gaining one
derivative at every target, for each positive integer Sobolev order. -/
theorem inverseSobolevFourierRemainder_analytic (m : ℕ) (hm : 1 ≤ m) :
    AnalyticOnNhd ℝ (D.inverseSobolevFourierRemainder m) univ := by
  intro z _
  have h := (D.higherSobolevBirkhoffFourierRemainder_originalReal_analytic m hm _ (mem_univ _)).comp
    (D.originalWeightedRealSobolevEquiv_symm_analytic (by norm_num) m (Nat.cast_nonneg m) z (mem_univ z))
  exact (((sourceSobolevBirkhoffFourierInverse ((m:ℝ)+1)).restrictScalars ℝ).analyticAt _).comp h |>.neg

/-- The inverse identity holds for the actual complex rectangular
coordinates at every native real Sobolev target. -/
theorem birkhoffMap_nativeSobolevInverse_coordinates (m : ℕ)
    (z : originalRealSobolevTarget m) (n : ℤ) :
    let a := (D.originalWeightedRealSobolevEquiv (by norm_num) m (Nat.cast_nonneg m)).symm z
    (sourceBirkhoffMap (by simp) (by norm_num) s (originalWeightedRealSource _ a).val).1 n = z.fst.val.val n ∧
    (sourceBirkhoffMap (by simp) (by norm_num) s (originalWeightedRealSource _ a).val).2 n = z.snd.val.val n := by
  dsimp only
  let w := sourceSobolevSpectralWeight m (Nat.cast_nonneg m)
  let a := (D.originalWeightedRealSobolevEquiv (by norm_num) m (Nat.cast_nonneg m)).symm z
  have h : D.originalWeightedRealMap w a = z :=
    (D.originalWeightedRealSobolevEquiv (by norm_num) m (Nat.cast_nonneg m)).apply_symm_apply z
  have he := D.real_map_complex_inclusion (originalWeightedRealSource w a)
  constructor
  · have hc := congrArg (fun v : Coeff 2 × Coeff 2 => v.1 n) he
    exact hc.symm.trans ((D.originalWeightedRealMap_fst w a n).symm.trans
      (congrArg (fun v => v.fst.val.val n) h))
  · have hc := congrArg (fun v : Coeff 2 × Coeff 2 => v.2 n) he
    exact hc.symm.trans ((D.originalWeightedRealMap_snd w a n).symm.trans
      (congrArg (fun v => v.snd.val.val n) h))

/-- The stronger inverse remainder has exactly the original inverse
minus the explicitly normalized inverse-Fourier coefficients. -/
theorem inverseSobolevFourierRemainder_coordinates (m : ℕ) (hm : 1 ≤ m)
    (z : originalRealSobolevTarget m) (n : ℤ) :
    let a := (D.originalWeightedRealSobolevEquiv (by norm_num) m (Nat.cast_nonneg m)).symm z
    (D.inverseSobolevFourierRemainder m z).1.val n =
      a.val.fst.val n + (z.fst.val.val (-n)-I*z.snd.val.val (-n))/(Real.sqrt 2:ℂ) ∧
    (D.inverseSobolevFourierRemainder m z).2.val n =
      a.val.snd.val n + (z.fst.val.val n+I*z.snd.val.val n)/(Real.sqrt 2:ℂ) := by
  let a := (D.originalWeightedRealSobolevEquiv (by norm_num) m (Nat.cast_nonneg m)).symm z
  let b : realTypeHigherSobolevSourceLocus m :=
    ⟨originalRealSobolevToHigher m a,originalRealSobolevToHigher_real m a⟩
  have he (j : ℤ) := D.higherSobolevBirkhoffFourierRemainder_coordinates m hm b j
  have hφ : higherSobolevSourceInclusion m b.val = (originalWeightedRealSource _ a).val := by
    change higherSobolevSourceInclusion m (originalSobolevToHigher m a.val) = _
    rw [higherSobolevSourceInclusion_originalSobolevToHigher,originalWeightedSourceCLM_real]
  have hmap (j : ℤ) := D.birkhoffMap_nativeSobolevInverse_coordinates m z j
  have hx := congrArg (fun v : CoeffPair 2 => v.fst n)
    (sourceBirkhoffFourierInverse_fourier (higherSobolevSourceInclusion m b.val))
  have hy := congrArg (fun v : CoeffPair 2 => v.snd n)
    (sourceBirkhoffFourierInverse_fourier (higherSobolevSourceInclusion m b.val))
  simp only [sourceBirkhoffFourierInverse_fst,sourceBirkhoffFourierInverse_snd,hφ,
    originalWeightedRealSource_fst,originalWeightedRealSource_snd] at hx hy
  constructor
  · change -(sourceSobolevBirkhoffFourierInverse ((m:ℝ)+1)
      (higherSobolevBirkhoffFourierRemainder m s b.val)).1.val n = _
    rw [sourceSobolevBirkhoffFourierInverse_fst,(he (-n)).1,(he (-n)).2,hφ,(hmap (-n)).1,(hmap (-n)).2]
    rw [← hx]
    ring
  · change -(sourceSobolevBirkhoffFourierInverse ((m:ℝ)+1)
      (higherSobolevBirkhoffFourierRemainder m s b.val)).2.val n = _
    rw [sourceSobolevBirkhoffFourierInverse_snd,(he n).1,(he n).2,hφ,(hmap n).1,(hmap n).2]
    rw [← hy]
    ring

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
