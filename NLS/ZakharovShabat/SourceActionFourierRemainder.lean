import NLS.SequenceSpaces.WeightedHilbertProduct
import NLS.ZakharovShabat.SourceSection23OneSmoothing

/-! # The original actions minus squared Fourier coefficients gain one weight

The actual Birkhoff remainder produces an analytic weighted summable
realization of the action error at every positive integer Sobolev order.
The signed Fourier convention and its exact quadratic normalization are retained.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat

/-- The original coefficient weight at an integer Sobolev order. -/
abbrev originalActionSobolevWeight (m : ℕ) : Weight :=
  sourceFrequencyWeight (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))

/-- Forget reality in both native target components, preserving coefficients. -/
def originalSobolevTargetComplexPair (m : ℕ) : originalRealSobolevTarget m →L[ℝ]
    (WeightedCoeff (originalActionSobolevWeight m) 2 × WeightedCoeff (originalActionSobolevWeight m) 2) :=
  ((WeightedRealCoeff.complexCLM _ 2).prodMap (WeightedRealCoeff.complexCLM _ 2)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap

/-- The one-order inclusion used to multiply a stronger remainder by the original coordinates. -/
def originalActionSobolevLower (m : ℕ) :
    WeightedCoeff (originalActionSobolevWeight (m+1)) 2 →L[ℂ]
      WeightedCoeff (originalActionSobolevWeight m) 2 :=
  WeightedCoeff.inclusionCLM _ _ (by
    intro n
    simp only [originalActionSobolevWeight,sourceFrequencyWeight_sobolev]
    exact Weight.sobolev_mono (by simp) n)

/-- Squaring the actual linear Fourier coordinates gives the signed source product. -/
theorem sourceBirkhoffFourier_quadratic_radius (φ : CoeffPair 2) (n : ℤ) :
    ((sourceBirkhoffFourier φ).1 n)^2 + ((sourceBirkhoffFourier φ).2 n)^2 =
      2 * φ.fst (-n) * φ.snd n := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [sourceBirkhoffFourier_fst,sourceBirkhoffFourier_snd]
  field_simp
  simp only [hs,I_sq]
  ring

namespace SourceSection17OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s)

/-- A stronger weighted summable sequence representing the literal original action error. -/
def actionFourierRemainder (m : ℕ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) :
    WeightedCoeff ((originalActionSobolevWeight (m+1)).product (originalActionSobolevWeight m)) 1 :=
  let r := originalSobolevTargetComplexPair (m+1) (D.complex.nativeForwardFourierRemainder m a)
  let z := originalSobolevTargetComplexPair m (D.complex.originalWeightedRealMap _ a)
  (1/2 : ℂ) • (WeightedCoeff.hilbertProduct _ _ r.1 ((2 : ℂ) • z.1-originalActionSobolevLower m r.1) +
    WeightedCoeff.hilbertProduct _ _ r.2 ((2 : ℂ) • z.2-originalActionSobolevLower m r.2))

/-- The stronger sequence map is real analytic on the entire native real Sobolev space. -/
theorem actionFourierRemainder_analytic (m : ℕ) (hm : 1 ≤ m) :
    AnalyticOnNhd ℝ (D.actionFourierRemainder m) univ := by
  intro a _
  have hr := ((originalSobolevTargetComplexPair (m+1)).analyticAt _).comp
    (D.complex.nativeForwardFourierRemainder_analytic m hm a (mem_univ _))
  have hz := ((originalSobolevTargetComplexPair m).analyticAt _).comp
    (D.complex.originalWeightedRealMap_analytic _ a (mem_univ _))
  have hr1 := ((ContinuousLinearMap.fst ℝ
    (WeightedCoeff (originalActionSobolevWeight (m+1)) 2) _).analyticAt _).comp hr
  have hr2 := ((ContinuousLinearMap.snd ℝ
    (WeightedCoeff (originalActionSobolevWeight (m+1)) 2) _).analyticAt _).comp hr
  have hz1 := ((ContinuousLinearMap.fst ℝ
    (WeightedCoeff (originalActionSobolevWeight m) 2) _).analyticAt _).comp hz
  have hz2 := ((ContinuousLinearMap.snd ℝ
    (WeightedCoeff (originalActionSobolevWeight m) 2) _).analyticAt _).comp hz
  have hf (z : WeightedCoeff (originalActionSobolevWeight (m+1)) 2 ×
      WeightedCoeff (originalActionSobolevWeight m) 2) := (((WeightedCoeff.analyticOnNhd_hilbertProduct
    (originalActionSobolevWeight (m+1)) (originalActionSobolevWeight m)) z (mem_univ _)).restrictScalars (𝕜 := ℝ))
  have h1 := (hf _).comp (hr1.prod ((hz1.const_smul (c := (2:ℂ))).sub
    (((originalActionSobolevLower m).restrictScalars ℝ).analyticAt _ |>.comp hr1)))
  have h2 := (((WeightedCoeff.analyticOnNhd_hilbertProduct
    (originalActionSobolevWeight (m+1)) (originalActionSobolevWeight m)) _ (mem_univ _)).restrictScalars (𝕜 := ℝ)).comp
    (hr2.prod ((hz2.const_smul (c := (2:ℂ))).sub
      (((originalActionSobolevLower m).restrictScalars ℝ).analyticAt _ |>.comp hr2)))
  exact (h1.add h2).const_smul (c := (1/2:ℂ))

/-- Every stronger coefficient is exactly the indexed action minus its Fourier product. -/
theorem actionFourierRemainder_coordinates (m : ℕ) (hm : 1 ≤ m)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) (n : ℤ) :
    let φ := originalWeightedRealSource (sourceSobolevSpectralWeight m (Nat.cast_nonneg m)) a
    (D.actionFourierRemainder m a).val n =
      sourceIndexedAction (by simp) (by norm_num) n φ.val - φ.val.fst (-n) * φ.val.snd n := by
  let φ := originalWeightedRealSource (sourceSobolevSpectralWeight m (Nat.cast_nonneg m)) a
  have hr := D.complex.nativeForwardFourierRemainder_literal_coordinates m hm a n
  have hz := D.complex.real_map_complex_inclusion φ
  have hx := congrArg (fun z : Coeff 2 × Coeff 2 => z.1 n) hz
  have hy := congrArg (fun z : Coeff 2 × Coeff 2 => z.2 n) hz
  have hI := D.indexed_action_radius φ.val (D.complex.real_subset φ.property) n
  have hF := sourceBirkhoffFourier_quadratic_radius φ.val n
  simp only [actionFourierRemainder,WeightedCoeff.smul_val,WeightedCoeff.add_val,
    WeightedCoeff.hilbertProduct_apply,WeightedCoeff.sub_val,originalActionSobolevLower,
    WeightedCoeff.inclusionCLM_apply]
  change (1/2 : ℂ) * ((D.complex.nativeForwardFourierRemainder m a).fst.val.val n *
      (2 * (D.complex.originalWeightedRealMap _ a).fst.val.val n -
        (D.complex.nativeForwardFourierRemainder m a).fst.val.val n) +
      (D.complex.nativeForwardFourierRemainder m a).snd.val.val n *
      (2 * (D.complex.originalWeightedRealMap _ a).snd.val.val n -
        (D.complex.nativeForwardFourierRemainder m a).snd.val.val n)) = _
  rw [hr.1,hr.2,D.complex.originalWeightedRealMap_fst,D.complex.originalWeightedRealMap_snd]
  change ((sourceRealBirkhoffMap _ _ s φ).1 n : ℂ) = _ at hx
  change ((sourceRealBirkhoffMap _ _ s φ).2 n : ℂ) = _ at hy
  rw [hx,hy]
  linear_combination (1/2 : ℂ) * hI - (1/2 : ℂ) * hF

/-- On the real source the Fourier product is the squared modulus of the reflected first coefficient. -/
theorem actionFourierRemainder_fourier_square (m : ℕ) (hm : 1 ≤ m)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) (n : ℤ) :
    let φ := originalWeightedRealSource (sourceSobolevSpectralWeight m (Nat.cast_nonneg m)) a
    (D.actionFourierRemainder m a).val n =
      sourceIndexedAction (by simp) (by norm_num) n φ.val - (‖φ.val.fst (-n)‖^2 : ℝ) := by
  rw [D.actionFourierRemainder_coordinates m hm a n]
  dsimp only
  let φ := originalWeightedRealSource (sourceSobolevSpectralWeight m (Nat.cast_nonneg m)) a
  have hφ := φ.property n
  change φ.val.snd n = conj (φ.val.fst (-n)) at hφ
  change _ - φ.val.fst (-n) * φ.val.snd n = _
  rw [hφ,Complex.mul_conj,Complex.normSq_eq_norm_sq]

/-- The stronger action weight is exactly the standard weight of order 2m+1. -/
theorem actionFourierRemainder_weight (m : ℕ) (n : ℤ) :
    (originalActionSobolevWeight (m+1)).product (originalActionSobolevWeight m) n =
      (1+|(n:ℝ)|)^(2*m+1) := by
  simp only [Weight.product_apply,originalActionSobolevWeight,sourceFrequencyWeight_sobolev]
  rw [← Weight.sobolev_add]
  have he : ((m+1:ℕ):ℝ)+(m:ℝ) = ((2*m+1:ℕ):ℝ) := by push_cast; ring
  rw [he,Weight.sobolev_apply,Real.rpow_natCast]

include D in
/-- The literal action error has an extra summable Sobolev weight at every signed index. -/
theorem summable_actionFourier_error (m : ℕ) (hm : 1 ≤ m)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) :
    let φ := originalWeightedRealSource (sourceSobolevSpectralWeight m (Nat.cast_nonneg m)) a
    Summable (fun n : ℤ => (1+|(n:ℝ)|)^(2*m+1) *
      ‖sourceIndexedAction (by simp) (by norm_num) n φ.val - (‖φ.val.fst (-n)‖^2 : ℝ)‖) := by
  let u := (originalActionSobolevWeight (m+1)).product (originalActionSobolevWeight m)
  have h : Summable (fun n : ℤ => ‖(u n : ℂ)*(D.actionFourierRemainder m a).val n‖) :=
    (D.actionFourierRemainder m a).property.norm.summable_of_one
  apply h.congr
  intro n
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (u.positive n).le]
  rw [show u n = (1+|(n:ℝ)|)^(2*m+1) from actionFourierRemainder_weight m n,
    D.actionFourierRemainder_fourier_square m hm a n]

end SourceSection17OriginalData
end NLS.ZakharovShabat
