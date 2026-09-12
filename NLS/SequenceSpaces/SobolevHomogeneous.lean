import NLS.SequenceSpaces.SobolevDerivative

/-!
# Homogeneous and inhomogeneous Hilbert Sobolev coefficients

Square summability plus the homogeneous fractional moment is equivalent to
the project's `(1+|n|)^s` weighted square summability. The estimates retain
explicit constants and the zero Fourier mode.
-/

noncomputable section
open scoped ENNReal
namespace NLS
namespace Weight

/-- The squared Sobolev-weighted coefficient has the expected exponent `2s`. -/
theorem norm_sobolev_mul_sq (s : ℝ) (n : ℤ) (z : ℂ) :
    ‖(sobolev s n : ℂ) * z‖ ^ 2 = (1 + |(n : ℝ)|) ^ (2 * s) * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sobolev s |>.positive n).le,
    mul_pow, sobolev_apply, ← Real.rpow_two ((1 + |(n : ℝ)|) ^ s),
    ← Real.rpow_mul (by positivity)]
  congr 2
  ring

/-- A uniform comparison between inhomogeneous and homogeneous nonnegative powers. -/
theorem one_add_rpow_le {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    (1 + x) ^ r ≤ (2 : ℝ) ^ r * (1 + x ^ r) := by
  by_cases hx₁ : x ≤ 1
  · calc
      (1 + x) ^ r ≤ (2 : ℝ) ^ r := Real.rpow_le_rpow (by positivity) (by linarith) hr
      _ ≤ (2 : ℝ) ^ r * (1 + x ^ r) := by
        nlinarith [Real.rpow_nonneg hx r, Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r]
  · calc
      (1 + x) ^ r ≤ (2 * x) ^ r := Real.rpow_le_rpow (by positivity) (by linarith) hr
      _ = (2 : ℝ) ^ r * x ^ r := Real.mul_rpow (by norm_num) hx
      _ ≤ (2 : ℝ) ^ r * (1 + x ^ r) := by
        nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r]

end Weight
namespace Coeff

/-- On `ℓ²`, homogeneous Sobolev moment summability is exactly weighted `ℓ²` membership. -/
theorem memlp_sobolev_iff_homogeneous {s : ℝ} (hs : 0 ≤ s) (a : Coeff 2) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ) * a n) 2 ↔
      Summable (fun n : ℤ => |(n : ℝ)| ^ (2 * s) * ‖a n‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Weight.norm_sobolev_mul_sq]
  constructor
  · intro hw
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hw
    intro n
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by positivity)
  · intro hh
    have ha : Summable (fun n : ℤ => ‖a n‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (lp.memℓp a).summable (by norm_num)
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ ((ha.add hh).mul_left ((2 : ℝ) ^ (2 * s)))
    intro n
    have hw := mul_le_mul_of_nonneg_right
      (Weight.one_add_rpow_le (show 0 ≤ 2 * s by positivity) (abs_nonneg (n : ℝ))) (sq_nonneg ‖a n‖)
    simpa only [add_mul, one_mul, mul_assoc] using hw

end Coeff
namespace WeightedCoeff

/-- Forgetting a nonnegative Sobolev weight is a contractive linear map into unweighted coefficients. -/
def sobolevToL2 {s : ℝ} (hs : 0 ≤ s) : WeightedCoeff (Weight.sobolev s) 2 →L[ℂ] Coeff 2 :=
  (weightIsometry (Weight.sobolev 0) 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sobolevInclusion hs)

@[simp] theorem sobolevToL2_apply {s : ℝ} (hs : 0 ≤ s)
    (a : WeightedCoeff (Weight.sobolev s) 2) (n : ℤ) : sobolevToL2 hs a n = a.val n := by
  change (Weight.sobolev 0 n : ℂ) * (sobolevInclusion hs a).val n = _
  simp [Weight.sobolev_apply]

theorem norm_sobolevToL2_le {s : ℝ} (hs : 0 ≤ s) (a : WeightedCoeff (Weight.sobolev s) 2) :
    ‖sobolevToL2 hs a‖ ≤ ‖a‖ := norm_sobolevInclusion_le hs a

/-- Exact square energy in the project's weighted norm. -/
theorem hasSum_sobolev_sq (s : ℝ) (a : WeightedCoeff (Weight.sobolev s) 2) :
    HasSum (fun n : ℤ => (1 + |(n : ℝ)|) ^ (2 * s) * ‖a.val n‖ ^ 2) (‖a‖ ^ 2) := by
  have hh := lp.hasSum_norm (p := 2) (by norm_num) (weightEquiv (Weight.sobolev s) 2 a)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, weightEquiv_apply,
    Weight.norm_sobolev_mul_sq, ← norm_eq] using hh

/-- Every nonnegative weighted sequence has a summable homogeneous moment. -/
theorem summable_homogeneous {s : ℝ} (hs : 0 ≤ s) (a : WeightedCoeff (Weight.sobolev s) 2) :
    Summable (fun n : ℤ => |(n : ℝ)| ^ (2 * s) * ‖a.val n‖ ^ 2) := by
  have h := Coeff.memlp_sobolev_iff_homogeneous hs (sobolevToL2 hs a)
  simp only [sobolevToL2_apply] at h
  exact h.mp a.property

/-- Homogeneous energy is bounded by the weighted norm squared. -/
theorem homogeneous_tsum_le_norm_sq {s : ℝ} (hs : 0 ≤ s) (a : WeightedCoeff (Weight.sobolev s) 2) :
    (∑' n : ℤ, |(n : ℝ)| ^ (2 * s) * ‖a.val n‖ ^ 2) ≤ ‖a‖ ^ 2 := by
  apply hasSum_le _ (summable_homogeneous hs a).hasSum (hasSum_sobolev_sq s a)
  intro n
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by positivity)) (sq_nonneg _)

/-- Conversely, the unweighted energy and homogeneous moment bound the weighted norm. -/
theorem norm_sq_le_homogeneous {s : ℝ} (hs : 0 ≤ s) (a : WeightedCoeff (Weight.sobolev s) 2) :
    ‖a‖ ^ 2 ≤ (2 : ℝ) ^ (2 * s) * (‖sobolevToL2 hs a‖ ^ 2 +
      ∑' n : ℤ, |(n : ℝ)| ^ (2 * s) * ‖a.val n‖ ^ 2) := by
  have ha : HasSum (fun n : ℤ => ‖a.val n‖ ^ 2) (‖sobolevToL2 hs a‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, sobolevToL2_apply] using
      lp.hasSum_norm (p := 2) (by norm_num) (sobolevToL2 hs a)
  apply hasSum_le _ (hasSum_sobolev_sq s a)
    ((ha.add (summable_homogeneous hs a).hasSum).mul_left ((2 : ℝ) ^ (2 * s)))
  intro n
  have hw := mul_le_mul_of_nonneg_right
    (Weight.one_add_rpow_le (show 0 ≤ 2 * s by positivity) (abs_nonneg (n : ℝ))) (sq_nonneg ‖a.val n‖)
  simpa only [add_mul, one_mul, mul_assoc] using hw

end WeightedCoeff
end NLS
