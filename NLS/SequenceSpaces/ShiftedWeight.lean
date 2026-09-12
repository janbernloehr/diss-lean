import NLS.SequenceSpaces.SpectralWeight
import NLS.SequenceSpaces.WeightedMultiplier
import NLS.SequenceSpaces.Translation

/-!
# Shifted weighted Fourier norms

The scalar norm in Section 6 has weight `w(n+i)` at the original coefficient
`a(n)`. It equals the ordinary weighted norm after multiplication by the
Fourier wave with index `i`. Translated weights define the same space, with
explicit comparison factor `w(i)` in both directions.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- Translate the weight, retaining the original coefficient indices. -/
def Weight.shift (w : Weight) (i : ℤ) : Weight := ⟨fun n => w (n + i), fun n => w.positive (n + i)⟩

@[simp] theorem Weight.shift_apply (w : Weight) (i n : ℤ) : w.shift i n = w (n + i) := rfl

namespace SpectralWeight
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source's lower bound on weights gives a contractive unweighted coefficient inclusion. -/
def toCoeff (w : SpectralWeight) : WeightedCoeff w.toWeight p →L[ℂ] Coeff p :=
  (WeightedCoeff.weightIsometry Weight.one p).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (WeightedCoeff.inclusionCLM w.toWeight Weight.one (fun n => w.one_le n))

@[simp] theorem toCoeff_apply (w : SpectralWeight) (a : WeightedCoeff w.toWeight p) (n : ℤ) :
    toCoeff w a n = a.val n := by
  change (Weight.one n : ℂ) * (WeightedCoeff.inclusionCLM _ _ _ a).val n = _
  rw [Weight.one_apply, Complex.ofReal_one, one_mul]
  exact WeightedCoeff.inclusionCLM_apply _ _ _ a n

theorem norm_toCoeff_le (w : SpectralWeight) (a : WeightedCoeff w.toWeight p) : ‖toCoeff w a‖ ≤ ‖a‖ := by
  change ‖(WeightedCoeff.weightIsometry Weight.one p) (WeightedCoeff.inclusionCLM _ _ _ a)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact WeightedCoeff.norm_inclusionCLM_le _ _ _ a

/-- Identity on raw coefficients, from the original weight to its translate. -/
def toShift (w : SpectralWeight) (i : ℤ) :
    WeightedCoeff w.toWeight p →L[ℂ] WeightedCoeff (w.toWeight.shift i) p :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun _ => 1) (w i) (w.positive i).le (by
    intro n
    simpa only [norm_one, mul_one, one_mul, Weight.shift_apply, toWeight_apply, mul_comm] using w.add_le n i)

/-- Identity on raw coefficients in the reverse direction. -/
def fromShift (w : SpectralWeight) (i : ℤ) :
    WeightedCoeff (w.toWeight.shift i) p →L[ℂ] WeightedCoeff w.toWeight p :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun _ => 1) (w i) (w.positive i).le (by
    intro n
    simpa only [norm_one, mul_one, one_mul, Weight.shift_apply, toWeight_apply, mul_comm] using w.le_shift_mul n i)

@[simp] theorem toShift_apply (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff w.toWeight p) (n : ℤ) :
    (toShift w i a).val n = a.val n := one_mul _

@[simp] theorem fromShift_apply (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff (w.toWeight.shift i) p) (n : ℤ) :
    (fromShift w i a).val n = a.val n := one_mul _

theorem norm_toShift_le (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff w.toWeight p) :
    ‖toShift w i a‖ ≤ w i * ‖a‖ :=
  WeightedCoeff.norm_weightedMultiplier_le _ _ _ _ (w.positive i).le (by
    intro n
    simpa only [norm_one, mul_one, one_mul, Weight.shift_apply, toWeight_apply, mul_comm] using w.add_le n i) a

theorem norm_fromShift_le (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff (w.toWeight.shift i) p) :
    ‖fromShift w i a‖ ≤ w i * ‖a‖ :=
  WeightedCoeff.norm_weightedMultiplier_le _ _ _ _ (w.positive i).le (by
    intro n
    simpa only [norm_one, mul_one, one_mul, Weight.shift_apply, toWeight_apply, mul_comm] using w.le_shift_mul n i) a

/-- All shifted weights give continuously equivalent spaces without changing raw coefficients. -/
def shiftEquiv (w : SpectralWeight) (i : ℤ) :
    WeightedCoeff w.toWeight p ≃L[ℂ] WeightedCoeff (w.toWeight.shift i) p where
  toLinearEquiv :=
    { toLinearMap := (toShift w i).toLinearMap
      invFun := fromShift w i
      left_inv a := by
        change fromShift w i (toShift w i a) = a
        apply Subtype.ext
        funext n
        simp only [fromShift_apply, toShift_apply]
      right_inv a := by
        change toShift w i (fromShift w i a) = a
        apply Subtype.ext
        funext n
        simp only [toShift_apply, fromShift_apply] }
  continuous_toFun := (toShift w i).continuous
  continuous_invFun := (fromShift w i).continuous

/-- The source's scalar shifted norm, on the existing unshifted coefficient space. -/
def shiftedNorm (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff w.toWeight p) : ℝ := ‖toShift w i a‖

theorem shiftedNorm_le (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff w.toWeight p) :
    shiftedNorm w i a ≤ w i * ‖a‖ := norm_toShift_le w i a

theorem norm_le_shiftedNorm (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff w.toWeight p) :
    ‖a‖ ≤ w i * shiftedNorm w i a := by
  have h := norm_fromShift_le w i (toShift w i a)
  have he : fromShift w i (toShift w i a) = a := (shiftEquiv w i).symm_apply_apply a
  rwa [he] at h

/-- The weighted energy terms are summable for every finite Banach exponent. -/
theorem summable_shiftedNorm_terms (w : SpectralWeight) (hp : p ≠ ⊤) (i : ℤ) (a : WeightedCoeff w.toWeight p) :
    Summable (fun n : ℤ => w (n + i) ^ p.toReal * ‖a.val n‖ ^ p.toReal) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have h := (lp.memℓp (WeightedCoeff.weightEquiv _ p (toShift w i a))).summable hp0
  simpa only [WeightedCoeff.weightEquiv_apply, toShift_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Weight.shift_apply, abs_of_pos (w.positive _),
    Real.mul_rpow (w.positive _).le (norm_nonneg _)] using h

/-- The exact finite-exponent scalar formula in Section 6. -/
theorem shiftedNorm_rpow_eq_tsum (w : SpectralWeight) (hp : p ≠ ⊤) (i : ℤ) (a : WeightedCoeff w.toWeight p) :
    shiftedNorm w i a ^ p.toReal = ∑' n : ℤ, w (n + i) ^ p.toReal * ‖a.val n‖ ^ p.toReal := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  rw [shiftedNorm, WeightedCoeff.norm_eq, lp.norm_rpow_eq_tsum hp0]
  apply tsum_congr
  intro n
  simp only [WeightedCoeff.weightEquiv_apply, toShift_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Weight.shift_apply, abs_of_pos (w.positive _),
    Real.mul_rpow (w.positive _).le (norm_nonneg _)]

/-- Reindexing converts a shifted weighted class isometrically into the original weighted space. -/
def modulationIsometry (w : SpectralWeight) (i : ℤ) :
    WeightedCoeff (w.toWeight.shift i) p ≃ₗᵢ[ℂ] WeightedCoeff w.toWeight p :=
  ((WeightedCoeff.weightIsometry _ p).trans (Coeff.shift i)).trans (WeightedCoeff.weightIsometry _ p).symm

@[simp] theorem modulationIsometry_apply (w : SpectralWeight) (i : ℤ)
    (a : WeightedCoeff (w.toWeight.shift i) p) (n : ℤ) :
    (modulationIsometry w i a).val n = a.val (n - i) := by
  change (w.toWeight.shift i (n - i) : ℂ) * a.val (n - i) / (w.toWeight n : ℂ) = _
  simp only [Weight.shift_apply, sub_add_cancel]
  exact mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero n)

/-- Multiplication by a Fourier wave acts by translating the actual coefficients. -/
def modulation (w : SpectralWeight) (i : ℤ) : WeightedCoeff w.toWeight p ≃L[ℂ] WeightedCoeff w.toWeight p :=
  (shiftEquiv w i).trans (modulationIsometry w i).toContinuousLinearEquiv

@[simp] theorem modulation_apply (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff w.toWeight p) (n : ℤ) :
    (modulation w i a).val n = a.val (n - i) := by
  change (modulationIsometry w i (toShift w i a)).val n = _
  rw [modulationIsometry_apply, toShift_apply]

/-- The weighted modulation agrees with the existing unweighted Fourier shift. -/
theorem toCoeff_modulation (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff w.toWeight p) :
    toCoeff w (modulation w i a) = Coeff.shift i (toCoeff w a) := by
  ext n
  simp only [toCoeff_apply, modulation_apply, Coeff.shift_apply]

/-- The shifted norm equals the ordinary weighted norm after actual Fourier modulation. -/
theorem norm_modulation (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff w.toWeight p) :
    ‖modulation w i a‖ = shiftedNorm w i a := by
  change ‖modulationIsometry w i (shiftEquiv w i a)‖ = ‖toShift w i a‖
  rw [LinearIsometryEquiv.norm_map]
  rfl

theorem norm_modulation_le (w : SpectralWeight) (i : ℤ) (a : WeightedCoeff w.toWeight p) :
    ‖modulation w i a‖ ≤ w i * ‖a‖ := by rw [norm_modulation]; exact shiftedNorm_le w i a

/-- Fourier modulations add their signed frequencies. -/
theorem modulation_add (w : SpectralWeight) (i j : ℤ) (a : WeightedCoeff w.toWeight p) :
    modulation w (i + j) a = modulation w j (modulation w i a) := by
  apply Subtype.ext
  funext n
  simp only [modulation_apply]
  rw [show n - (i + j) = n - j - i by omega]

@[simp] theorem modulation_zero (w : SpectralWeight) (a : WeightedCoeff w.toWeight p) : modulation w 0 a = a := by
  apply Subtype.ext
  funext n
  simp only [modulation_apply, sub_zero]

@[simp] theorem shiftedNorm_zero (w : SpectralWeight) (a : WeightedCoeff w.toWeight p) : shiftedNorm w 0 a = ‖a‖ := by
  rw [← norm_modulation, modulation_zero]

/-- Changing the shift by `j` costs at most `w(j)`, independently of the first shift. -/
theorem shiftedNorm_add_le (w : SpectralWeight) (i j : ℤ) (a : WeightedCoeff w.toWeight p) :
    shiftedNorm w (i + j) a ≤ w j * shiftedNorm w i a := by
  rw [← norm_modulation, modulation_add]
  simpa only [norm_modulation] using norm_modulation_le w j (modulation w i a)

end SpectralWeight
end NLS
