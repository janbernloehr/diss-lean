import NLS.ZakharovShabat.SourceSobolevNativeProjection

/-! # Fourier remainders in the exact real Sobolev spaces

The actual forward and inverse remainders gain one derivative, are real analytic, and are bounded on every native Sobolev ball.
-/

noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat

/-- The signed Fourier transform has real rectangular coordinates on
the original conjugate-reflected real source. -/
theorem sourceBirkhoffFourier_im_eq_zero (a : realTypeSourceSubmodule 2) (n : ℤ) :
    ((sourceBirkhoffFourier a.val).1 n).im = 0 ∧
    ((sourceBirkhoffFourier a.val).2 n).im = 0 := by
  have ha := a.property n
  change a.val.snd n = conj (a.val.fst (-n)) at ha
  simp [sourceBirkhoffFourier_fst,sourceBirkhoffFourier_snd,ha,Complex.div_im]

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)

/-- The canonical forward remainder in the exact native real h^(m+1)
target, with the component-sum norm. -/
def nativeForwardFourierRemainder
    (_D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) (m : ℕ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) :
    originalRealSobolevTarget (m+1) :=
  strongerSobolevRealTargetProjection m
    (higherSobolevBirkhoffFourierRemainder m s (originalRealSobolevToHigher m a))

/-- The canonical inverse remainder in the exact native real H^(m+1)
source, with its original conjugate-reflection condition. -/
def nativeInverseFourierRemainder (m : ℕ) (z : originalRealSobolevTarget m) :
    weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight ((m+1:ℕ):ℝ) (Nat.cast_nonneg (m+1))) :=
  strongerSobolevRealSourceProjection m (D.inverseSobolevFourierRemainder m z)

include D

/-- Reality of the full stronger forward error at each original real source. -/
theorem higherSobolevBirkhoffFourierRemainder_originalReal_im_eq_zero
    (m : ℕ) (hm : 1 ≤ m)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) (n : ℤ) :
    ((higherSobolevBirkhoffFourierRemainder m s (originalRealSobolevToHigher m a)).1.val n).im = 0 ∧
    ((higherSobolevBirkhoffFourierRemainder m s (originalRealSobolevToHigher m a)).2.val n).im = 0 := by
  have he := D.higherSobolevBirkhoffFourierRemainder_coordinates m hm
    ⟨originalRealSobolevToHigher m a,originalRealSobolevToHigher_real m a⟩ n
  have hφ : higherSobolevSourceInclusion m (originalRealSobolevToHigher m a) =
      (originalWeightedRealSource _ a).val := by
    change higherSobolevSourceInclusion m (originalSobolevToHigher m a.val) = _
    rw [higherSobolevSourceInclusion_originalSobolevToHigher,originalWeightedSourceCLM_real]
  have hx := D.coordinates_im_eq_zero_of_realType (originalWeightedRealSource _ a).val
    (originalWeightedRealSource _ a).property n
  have hf := sourceBirkhoffFourier_im_eq_zero (originalWeightedRealSource _ a) n
  rw [he.1,he.2]
  change ((sourceBirkhoffMap (by simp) (by norm_num) s
      (higherSobolevSourceInclusion m (originalRealSobolevToHigher m a))).1 n -
      (sourceBirkhoffFourier (higherSobolevSourceInclusion m (originalRealSobolevToHigher m a))).1 n).im = 0 ∧
    ((sourceBirkhoffMap (by simp) (by norm_num) s
      (higherSobolevSourceInclusion m (originalRealSobolevToHigher m a))).2 n -
      (sourceBirkhoffFourier (higherSobolevSourceInclusion m (originalRealSobolevToHigher m a))).2 n).im = 0
  rw [hφ]
  simp only [sub_im,hx.1,hx.2,hf.1,hf.2,sub_self,and_self]

/-- The stronger inverse error satisfies the exact real source relation. -/
theorem inverseSobolevFourierRemainder_realType (m : ℕ) (hm : 1 ≤ m)
    (z : originalRealSobolevTarget m) (n : ℤ) :
    (D.inverseSobolevFourierRemainder m z).2.val n =
      conj ((D.inverseSobolevFourierRemainder m z).1.val (-n)) := by
  let a := (D.originalWeightedRealSobolevEquiv (by norm_num) m (Nat.cast_nonneg m)).symm z
  have ha := (mem_weightedRealSourceSubmodule_iff _ a.val).mp a.property n
  rw [(D.inverseSobolevFourierRemainder_coordinates m hm z n).2,
    (D.inverseSobolevFourierRemainder_coordinates m hm z (-n)).1]
  simp only [neg_neg,map_add,map_div₀,map_sub,map_mul,Complex.conj_I,Complex.conj_ofReal]
  rw [Complex.conj_eq_iff_im.mpr (WeightedRealCoeff.im_eq_zero _ 2 z.fst n),
    Complex.conj_eq_iff_im.mpr (WeightedRealCoeff.im_eq_zero _ 2 z.snd n)]
  change a.val.snd.val n + _ = conj (a.val.fst.val (-n)) + _
  rw [ha]
  ring

/-- The native real forward realization preserves the full complex
coefficient values of the canonical stronger remainder. -/
theorem nativeForwardFourierRemainder_coordinates (m : ℕ) (hm : 1 ≤ m)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) (n : ℤ) :
    (D.nativeForwardFourierRemainder m a).fst.val.val n =
      (higherSobolevBirkhoffFourierRemainder m s (originalRealSobolevToHigher m a)).1.val n ∧
    (D.nativeForwardFourierRemainder m a).snd.val.val n =
      (higherSobolevBirkhoffFourierRemainder m s (originalRealSobolevToHigher m a)).2.val n :=
  strongerSobolevRealTargetProjection_coordinates m _
    (D.higherSobolevBirkhoffFourierRemainder_originalReal_im_eq_zero m hm a) n

/-- The native real inverse realization preserves every coefficient of
the actual inverse-minus-Fourier-inverse error. -/
theorem nativeInverseFourierRemainder_coordinates (m : ℕ) (hm : 1 ≤ m)
    (z : originalRealSobolevTarget m) (n : ℤ) :
    (D.nativeInverseFourierRemainder m z).val.fst.val n = (D.inverseSobolevFourierRemainder m z).1.val n ∧
    (D.nativeInverseFourierRemainder m z).val.snd.val n = (D.inverseSobolevFourierRemainder m z).2.val n :=
  strongerSobolevRealSourceProjection_coordinates m _ (D.inverseSobolevFourierRemainder_realType m hm z) n

/-- Forward one-smoothing is real analytic with the exact real codomain. -/
theorem nativeForwardFourierRemainder_analytic (m : ℕ) (hm : 1 ≤ m) :
    AnalyticOnNhd ℝ (D.nativeForwardFourierRemainder m) univ := by
  intro a _
  exact ((strongerSobolevRealTargetProjection m).analyticAt _).comp
    (D.higherSobolevBirkhoffFourierRemainder_originalReal_analytic m hm a (mem_univ a))

/-- Inverse one-smoothing is real analytic with the exact real codomain. -/
theorem nativeInverseFourierRemainder_analytic (m : ℕ) (hm : 1 ≤ m) :
    AnalyticOnNhd ℝ (D.nativeInverseFourierRemainder m) univ := by
  intro z _
  exact ((strongerSobolevRealSourceProjection m).analyticAt _).comp
    (D.inverseSobolevFourierRemainder_analytic m hm z (mem_univ z))

/-- Uniform forward bounds in the native real component-sum target norm. -/
theorem nativeForwardFourierRemainder_uniform_ball (m : ℕ) (hm : 1 ≤ m)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : weightedRealSourceSubmodule (p := 2)
      (sourceSobolevSpectralWeight m (Nat.cast_nonneg m)), ‖a‖ ≤ R →
      ‖D.nativeForwardFourierRemainder m a‖ ≤ C := by
  obtain ⟨M,hM,h⟩ := D.higherSobolevBirkhoffFourierRemainder_originalReal_uniform_ball m hm R hR
  let P := strongerSobolevRealTargetProjection m
  refine ⟨‖P‖*M,mul_nonneg (norm_nonneg P) hM,?_⟩
  intro a ha
  exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h a ha) (norm_nonneg P))

/-- Uniform inverse bounds in the native real component-sum source norm. -/
theorem nativeInverseFourierRemainder_uniform_ball (m : ℕ) (hm : 1 ≤ m)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : originalRealSobolevTarget m, ‖z‖ ≤ R →
      ‖D.nativeInverseFourierRemainder m z‖ ≤ C := by
  obtain ⟨M,hM,h⟩ := D.inverseSobolevFourierRemainder_uniform_ball m hm R hR
  let P := strongerSobolevRealSourceProjection m
  refine ⟨‖P‖*M,mul_nonneg (norm_nonneg P) hM,?_⟩
  intro z hz
  exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h z hz) (norm_nonneg P))

/-- The real forward map has the literal Birkhoff-minus-Fourier
coefficients of the original source, in the exact stronger real target. -/
theorem nativeForwardFourierRemainder_literal_coordinates (m : ℕ) (hm : 1 ≤ m)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) (n : ℤ) :
    let φ := originalWeightedRealSource (sourceSobolevSpectralWeight m (Nat.cast_nonneg m)) a
    (D.nativeForwardFourierRemainder m a).fst.val.val n =
      (sourceBirkhoffMap (by simp) (by norm_num) s φ.val).1 n - (sourceBirkhoffFourier φ.val).1 n ∧
    (D.nativeForwardFourierRemainder m a).snd.val.val n =
      (sourceBirkhoffMap (by simp) (by norm_num) s φ.val).2 n - (sourceBirkhoffFourier φ.val).2 n := by
  have he := D.higherSobolevBirkhoffFourierRemainder_coordinates m hm
    ⟨originalRealSobolevToHigher m a,originalRealSobolevToHigher_real m a⟩ n
  have hφ : higherSobolevSourceInclusion m (originalRealSobolevToHigher m a) =
      (originalWeightedRealSource _ a).val := by
    change higherSobolevSourceInclusion m (originalSobolevToHigher m a.val) = _
    rw [higherSobolevSourceInclusion_originalSobolevToHigher,originalWeightedSourceCLM_real]
  have hp := D.nativeForwardFourierRemainder_coordinates m hm a n
  refine ⟨hp.1.trans ?_,hp.2.trans ?_⟩
  · simpa only [Subtype.coe_mk,hφ] using he.1
  · simpa only [Subtype.coe_mk,hφ] using he.2

/-- The real inverse map has the literal inverse-minus-Fourier-inverse
coefficients, preserving the original native inverse at every target. -/
theorem nativeInverseFourierRemainder_literal_coordinates (m : ℕ) (hm : 1 ≤ m)
    (z : originalRealSobolevTarget m) (n : ℤ) :
    let a := (D.originalWeightedRealSobolevEquiv (by norm_num) m (Nat.cast_nonneg m)).symm z
    (D.nativeInverseFourierRemainder m z).val.fst.val n =
      a.val.fst.val n + (z.fst.val.val (-n)-I*z.snd.val.val (-n))/(Real.sqrt 2:ℂ) ∧
    (D.nativeInverseFourierRemainder m z).val.snd.val n =
      a.val.snd.val n + (z.fst.val.val n+I*z.snd.val.val n)/(Real.sqrt 2:ℂ) := by
  have hp := D.nativeInverseFourierRemainder_coordinates m hm z n
  have he := D.inverseSobolevFourierRemainder_coordinates m hm z n
  exact ⟨hp.1.trans he.1,hp.2.trans he.2⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
