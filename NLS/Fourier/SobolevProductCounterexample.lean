import NLS.Fourier.PeriodicSobolevEmbedding
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-!
# Counterexample to the constant in the printed estimate (A.4)

The finite coefficient sequences u = 2δ₀+δ₁ and v = δ₀+⋯+δ₄ satisfy
‖u‖_{FL^{1,2}}² = 8, ‖v‖_{FL²}² = 5, and ‖uv‖_{FL²}² = 41 > 40.
They give original periodic-distribution counterexamples at every positive
physical period. At period two the proof's rescaled weight also equals the
Section 2 weight, so that convention cannot restore the printed estimate.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace NLS

/-- The finite multiplier coefficients 2δ₀+δ₁. -/
def a8Multiplier : ℤ →₀ ℂ := Finsupp.single 0 2 + Finsupp.single 1 1

/-- The finite input coefficients δ₀+δ₁+δ₂+δ₃+δ₄. -/
def a8Input : ℤ →₀ ℂ := Finsupp.single 0 1 + Finsupp.single 1 1 +
  Finsupp.single 2 1 + Finsupp.single 3 1 + Finsupp.single 4 1

/-- The product coefficients 2δ₀+3δ₁+3δ₂+3δ₃+3δ₄+δ₅. -/
def a8Output : ℤ →₀ ℂ := Finsupp.single 0 2 + Finsupp.single 1 3 +
  Finsupp.single 2 3 + Finsupp.single 3 3 + Finsupp.single 4 3 + Finsupp.single 5 1

/-- Exact finite convolution for the counterexample. -/
theorem a8Convolution :
    Coeff.convolution (Coeff.ofFinsupp (p := 2) a8Input) (Coeff.ofFinsupp (p := 1) a8Multiplier) =
      Coeff.ofFinsupp a8Output := by
  have hs (k : ℤ) (z : ℂ) : Coeff.ofFinsupp (p := 1) (Finsupp.single k z) = lp.single 1 k z := by
    ext n
    simp [Coeff.ofFinsupp_apply,lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [a8Multiplier,map_add,hs,hs,Coeff.convolution_add_right,
    Coeff.convolution_single_right,Coeff.convolution_single_right]
  ext n
  simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    Coeff.shift_apply,Coeff.ofFinsupp_apply,sub_zero]
  change (2:ℂ) * a8Input n + 1 * a8Input (n-1) = a8Output n
  by_cases hn : 0 ≤ n ∧ n ≤ 5
  · obtain ⟨hn0,hn5⟩ := hn
    interval_cases n <;> norm_num [a8Input,a8Output,Finsupp.single_apply]
  · simp (disch := omega) [a8Input,a8Output]

/-- The input has squared unweighted ℓ² norm five. -/
theorem a8Input_norm_sq : ‖Coeff.ofFinsupp (p := 2) a8Input‖^2 = 5 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) (Coeff.ofFinsupp (p := 2) a8Input)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,Coeff.ofFinsupp_apply] at h
  rw [h,tsum_eq_sum (s := {0,1,2,3,4})]
  · norm_num [a8Input,Finsupp.single_apply]
  · intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    simp_all [a8Input,Finsupp.single_apply,eq_comm]

/-- The output has squared unweighted ℓ² norm forty-one. -/
theorem a8Output_norm_sq : ‖Coeff.ofFinsupp (p := 2) a8Output‖^2 = 41 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) (Coeff.ofFinsupp (p := 2) a8Output)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,Coeff.ofFinsupp_apply] at h
  rw [h,tsum_eq_sum (s := {0,1,2,3,4,5})]
  · norm_num [a8Output,Finsupp.single_apply]
  · intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    simp_all [a8Output,Finsupp.single_apply,eq_comm]

/-- The multiplier has squared weighted ℓ² norm eight. -/
theorem a8Multiplier_weighted_norm_sq :
    ‖WeightedCoeff.ofFinsupp (Weight.sobolev 1) 2 a8Multiplier‖^2 = 8 := by
  let a := WeightedCoeff.ofFinsupp (Weight.sobolev 1) 2 a8Multiplier
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal)
    (WeightedCoeff.weightIsometry (Weight.sobolev 1) 2 a)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,LinearIsometryEquiv.norm_map] at h
  rw [h,tsum_eq_sum (s := {0,1})]
  · change ∑ n ∈ ({0,1}:Finset ℤ), ‖((Weight.sobolev 1 n):ℂ) * a8Multiplier n‖^2 = _
    norm_num [a8Multiplier,Finsupp.single_apply,Weight.sobolev_apply]
  · intro n hn
    change ‖((Weight.sobolev 1 n):ℂ) * a8Multiplier n‖^2 = 0
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    simp [a8Multiplier,Ne.symm hn.1,Ne.symm hn.2]

/-- The coefficient-level product violates the printed constant-one estimate. -/
theorem a8_constant_one_fails :
    ‖WeightedCoeff.ofFinsupp (Weight.sobolev 1) 2 a8Multiplier‖ *
      ‖Coeff.ofFinsupp (p := 2) a8Input‖ <
    ‖Coeff.convolution (Coeff.ofFinsupp (p := 2) a8Input) (Coeff.ofFinsupp (p := 1) a8Multiplier)‖ := by
  rw [a8Convolution]
  have hu := a8Multiplier_weighted_norm_sq
  have hv := a8Input_norm_sq
  have hw := a8Output_norm_sq
  have hs : (‖WeightedCoeff.ofFinsupp (Weight.sobolev 1) 2 a8Multiplier‖ *
      ‖Coeff.ofFinsupp (p := 2) a8Input‖)^2 < ‖Coeff.ofFinsupp (p := 2) a8Output‖^2 := by
    rw [mul_pow,hu,hv,hw]
    norm_num
  nlinarith [norm_nonneg (Coeff.ofFinsupp (p := 2) a8Output)]


namespace Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

/-- The finite multiplier as an original FL^{1,2} distribution. -/
def a8OriginalMultiplier : PeriodicFourierLebesgue L (Weight.sobolev 1) 2 :=
  (coefficientsIsometry (Weight.sobolev 1) 2 (Weight.hasTemperedInverse_sobolev 1)).symm
    (WeightedCoeff.ofFinsupp (Weight.sobolev 1) 2 a8Multiplier)

/-- The finite input as an original FL² distribution. -/
def a8OriginalInput : PeriodicFourierLebesgue L Weight.one 2 :=
  (unweightedCoefficients 2).symm (Coeff.ofFinsupp a8Input)

/-- The original multiplier has exactly the stated finite coefficients. -/
theorem a8OriginalMultiplier_coefficient (n : ℤ) :
    (a8OriginalMultiplier (L := L)).val (mode (-n)) = a8Multiplier n := by
  change ((coefficientsIsometry (Weight.sobolev 1) 2 (Weight.hasTemperedInverse_sobolev 1))
    ((coefficientsIsometry (Weight.sobolev 1) 2 (Weight.hasTemperedInverse_sobolev 1)).symm
      (WeightedCoeff.ofFinsupp (Weight.sobolev 1) 2 a8Multiplier))).val n = _
  rw [LinearIsometryEquiv.apply_symm_apply,WeightedCoeff.ofFinsupp_apply]

/-- The Sobolev inclusion recovers the multiplier in ℓ¹. -/
theorem a8OriginalMultiplier_wienerCoefficients :
    unweightedCoefficients 1 (sobolevToWiener (by norm_num) (a8OriginalMultiplier (L := L))) =
      Coeff.ofFinsupp a8Multiplier := by
  ext n
  rw [unweightedCoefficients_apply,sobolevToWiener_coefficient,a8OriginalMultiplier_coefficient,Coeff.ofFinsupp_apply]

/-- The actual physical polynomial 2 + exp(i·2πx/L). -/
def a8MultiplierPolynomial : C(AddCircle L,ℂ) := continuousFourierPolynomial {0,1} a8Multiplier

/-- The actual physical polynomial with unit coefficients at frequencies zero through four. -/
def a8InputPolynomial : C(AddCircle L,ℂ) := continuousFourierPolynomial {0,1,2,3,4} a8Input

/-- The original multiplier is integration against its actual finite polynomial. -/
theorem a8OriginalMultiplier_eq_ofContinuous : (a8OriginalMultiplier (L := L)).val =
    Distribution.ofContinuous a8MultiplierPolynomial := by
  apply Distribution.ext_coefficients
  intro n
  rw [a8OriginalMultiplier_coefficient,Distribution.ofContinuous_coefficient,
    a8MultiplierPolynomial,continuousFourierPolynomial_coefficient]
  by_cases hn : n ∈ ({0,1} : Finset ℤ)
  · rw [if_pos hn]
  · rw [if_neg hn]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    simp [a8Multiplier,Ne.symm hn.1,Ne.symm hn.2]

/-- The original input is integration against its actual finite polynomial. -/
theorem a8OriginalInput_eq_ofContinuous : (a8OriginalInput (L := L)).val =
    Distribution.ofContinuous a8InputPolynomial := by
  apply Distribution.ext_coefficients
  intro n
  rw [← unweightedCoefficients_apply,a8OriginalInput,LinearIsometryEquiv.apply_symm_apply,
    Coeff.ofFinsupp_apply,Distribution.ofContinuous_coefficient,
    a8InputPolynomial,continuousFourierPolynomial_coefficient]
  by_cases hn : n ∈ ({0,1,2,3,4} : Finset ℤ)
  · rw [if_pos hn]
  · rw [if_neg hn]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    simp_all [a8Input]

/-- The original multiplier has squared Sobolev norm eight. -/
theorem a8OriginalMultiplier_norm_sq : ‖a8OriginalMultiplier (L := L)‖^2 = 8 := by
  simpa only [a8OriginalMultiplier,LinearIsometryEquiv.norm_map] using a8Multiplier_weighted_norm_sq

/-- The original input has squared Fourier–Lebesgue norm five. -/
theorem a8OriginalInput_norm_sq : ‖a8OriginalInput (L := L)‖^2 = 5 := by
  simpa only [a8OriginalInput,LinearIsometryEquiv.norm_map] using a8Input_norm_sq

/-- The counterexample product is actual pointwise multiplication of the two polynomials. -/
theorem a8OriginalProduct_eq_ofContinuous :
    (sobolevProduct (by norm_num) (a8OriginalMultiplier (L := L)) a8OriginalInput).val =
      Distribution.ofContinuous (a8MultiplierPolynomial * a8InputPolynomial) := by
  have hm : continuousRepresentative (sobolevToWiener (by norm_num) (a8OriginalMultiplier (L := L))) =
      a8MultiplierPolynomial := by
    apply Distribution.ofContinuous_injective
    rw [sobolevToWiener_continuous_represents,a8OriginalMultiplier_eq_ofContinuous]
  unfold sobolevProduct
  rw [youngProduct_comm,youngProduct_eq_ofContinuous _ _ _ _ a8OriginalInput_eq_ofContinuous.symm,hm,mul_comm]

/-- The original product has squared norm forty-one at every positive period. -/
theorem a8OriginalProduct_norm_sq :
    ‖sobolevProduct (by norm_num) (a8OriginalMultiplier (L := L)) a8OriginalInput‖^2 = 41 := by
  simp only [sobolevProduct,youngProduct,LinearIsometryEquiv.norm_map,
    a8OriginalMultiplier_wienerCoefficients,a8OriginalInput,LinearIsometryEquiv.apply_symm_apply]
  rw [Coeff.youngConvolution_comm,Coeff.youngConvolution_eq_convolution,a8Convolution,a8Output_norm_sq]

/-- The printed estimate fails on the original spaces at every positive period. -/
theorem a8Original_constant_one_fails :
    ‖a8OriginalMultiplier (L := L)‖ * ‖a8OriginalInput (L := L)‖ <
      ‖sobolevProduct (by norm_num) (a8OriginalMultiplier (L := L)) a8OriginalInput‖ := by
  have hu := a8OriginalMultiplier_norm_sq (L := L)
  have hv := a8OriginalInput_norm_sq (L := L)
  have hw := a8OriginalProduct_norm_sq (L := L)
  have hs : (‖a8OriginalMultiplier (L := L)‖ * ‖a8OriginalInput (L := L)‖)^2 <
      ‖sobolevProduct (by norm_num) (a8OriginalMultiplier (L := L)) a8OriginalInput‖^2 := by
    rw [mul_pow,hu,hv,hw]
    norm_num
  nlinarith [norm_nonneg (sobolevProduct (by norm_num) (a8OriginalMultiplier (L := L)) a8OriginalInput)]

/-- Existence of original-distribution counterexamples to the printed estimate (A.4). -/
theorem exists_sobolevProduct_norm_gt_one :
    ∃ (u : PeriodicFourierLebesgue L (Weight.sobolev 1) 2) (v : PeriodicFourierLebesgue L Weight.one 2),
      ‖u‖ * ‖v‖ < ‖sobolevProduct (by norm_num) u v‖ :=
  ⟨a8OriginalMultiplier,a8OriginalInput,a8Original_constant_one_fails⟩


end Fourier.PeriodicFourierLebesgue
end NLS
