import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.Embedding
import NLS.SequenceSpaces.SobolevEmbedding

/-!
# Weighted Hölder embeddings between Banach exponents

A weight ratio in `ℓʳ` gives an embedding from weighted `ℓᵖ` to weighted `ℓᑫ`
when `1/q = 1/p + 1/r`. For Sobolev weights, the strict summability threshold
is `(s-t) r > 1`. This is the coefficient estimate used in Appendix A.9.
-/

noncomputable section
open scoped ENNReal
namespace NLS
namespace Coeff
variable {p r q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] [Fact (1 ≤ q)]
variable [p.HolderTriple r q]

private theorem complex_mul_norm_le : ‖ContinuousLinearMap.mul ℂ ℂ‖ ≤ (1 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using ContinuousLinearMap.opNorm_mul_apply_le ℂ ℂ x

/-- Pointwise Hölder multiplication for any Banach Hölder triple. -/
def holderProduct : Coeff p →L[ℂ] Coeff r →L[ℂ] Coeff q :=
  lp.holderL q (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
    (K := 1) (fun _ => complex_mul_norm_le)

@[simp] theorem holderProduct_apply (a : Coeff p) (b : Coeff r) (n : ℤ) :
    holderProduct (q := q) a b n = a n * b n := rfl

/-- The Hölder constant for scalar pointwise multiplication is one. -/
theorem norm_holderProduct_le (a : Coeff p) (b : Coeff r) :
    ‖holderProduct (q := q) a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h : ‖holderProduct (p := p) (r := r) (q := q)‖ ≤ 1 :=
    lp.norm_holderL_le q (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
      (K := 1) (fun _ => complex_mul_norm_le)
  calc
    _ ≤ ‖holderProduct (p := p) (r := r) (q := q)‖ * ‖a‖ * ‖b‖ :=
      (holderProduct (p := p) (r := r) (q := q)).le_opNorm₂ _ _
    _ ≤ ‖a‖ * ‖b‖ := by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (norm_nonneg a)) (norm_nonneg b)

end Coeff
namespace Weight

/-- A Sobolev reciprocal belongs to a finite sequence exponent above the strict threshold. -/
theorem inverse_sobolev_memlp {r : ℝ≥0∞} (hr : 0 < r.toReal) {d : ℝ}
    (hd : 1 < d * r.toReal) : Memℓp (fun n : ℤ => (sobolev d n : ℂ)⁻¹) r := by
  rw [memℓp_gen_iff hr]
  apply (summable_inverse_bracket hd).congr
  intro n
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ((sobolev d).positive n)]
  rw [Real.inv_rpow ((sobolev d).positive n).le]
  simp only [sobolev_apply, ← Real.rpow_mul (by positivity : 0 ≤ 1 + |(n : ℝ)|), one_div]

/-- The Sobolev reciprocal summability condition is exact, including failure at equality. -/
theorem inverse_sobolev_memlp_iff {r : ℝ≥0∞} (hr : 0 < r.toReal) (d : ℝ) :
    Memℓp (fun n : ℤ => (sobolev d n : ℂ)⁻¹) r ↔ 1 < d * r.toReal := by
  refine ⟨?_, inverse_sobolev_memlp hr⟩
  intro h
  have hs := (memℓp_gen_iff hr).mp h
  have hs' : Summable (fun n : ℤ => 1 / (1 + |(n : ℝ)|) ^ (d * r.toReal)) := by
    apply hs.congr
    intro n
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ((sobolev d).positive n)]
    rw [Real.inv_rpow ((sobolev d).positive n).le]
    simp only [sobolev_apply, ← Real.rpow_mul (by positivity : 0 ≤ 1 + |(n : ℝ)|), one_div]
  have hn := hs'.comp_injective (Nat.cast_injective (R := ℤ))
  apply (Real.summable_one_div_nat_add_rpow 1 (d * r.toReal)).mp
  convert! hn using 1
  funext n
  simp [abs_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity), add_comm]

/-- At infinity, zero regularity gain is permitted. -/
theorem inverse_sobolev_memlp_top {d : ℝ} (hd : 0 ≤ d) :
    Memℓp (fun n : ℤ => (sobolev d n : ℂ)⁻¹) ⊤ := by
  apply memℓp_infty
  refine ⟨1, ?_⟩
  rintro y ⟨n, rfl⟩
  change ‖(sobolev d n : ℂ)⁻¹‖ ≤ 1
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ((sobolev d).positive n)]
  exact inv_le_one_of_one_le₀
    (Real.one_le_rpow (le_add_of_nonneg_right (abs_nonneg _)) hd)

/-- A ratio of Sobolev weights is exactly the reciprocal of their regularity difference. -/
theorem sobolev_ratio (s t : ℝ) (n : ℤ) :
    (sobolev t n : ℂ) / (sobolev s n : ℂ) = (sobolev (s - t) n : ℂ)⁻¹ := by
  have he : sobolev (s - t) n * sobolev t n = sobolev s n := by
    rw [← sobolev_add, sub_add_cancel]
  have hec := congrArg (fun x : ℝ => (x : ℂ)) he
  push_cast at hec
  rw [← hec]
  have hdiv (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) : b / (a * b) = a⁻¹ := by
    field_simp
  exact hdiv _ _ ((sobolev (s - t)).complex_ne_zero n) ((sobolev t).complex_ne_zero n)

end Weight
namespace WeightedCoeff
variable {p r q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] [Fact (1 ≤ q)]
variable [p.HolderTriple r q]

/-- The target-to-source weight ratio in the Hölder multiplier class. -/
def weightRatio (w v : Weight) (h : Memℓp (fun n : ℤ => (v n : ℂ) / (w n : ℂ)) r) : Coeff r :=
  ⟨fun n => (v n : ℂ) / (w n : ℂ), h⟩

/-- General weighted embedding with a summable weight ratio. -/
def holderInclusion (w v : Weight) (h : Memℓp (fun n : ℤ => (v n : ℂ) / (w n : ℂ)) r) :
    WeightedCoeff w p →L[ℂ] WeightedCoeff v q :=
  (weightIsometry v q).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((Coeff.holderProduct (q := q)).flip (weightRatio w v h)).comp
      (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem holderInclusion_apply (w v : Weight)
    (h : Memℓp (fun n : ℤ => (v n : ℂ) / (w n : ℂ)) r)
    (a : WeightedCoeff w p) (n : ℤ) : (holderInclusion (q := q) w v h a).val n = a.val n := by
  change ((w n : ℂ) * a.val n * ((v n : ℂ) / (w n : ℂ))) / (v n : ℂ) = _
  field_simp [w.complex_ne_zero n, v.complex_ne_zero n]

/-- The explicit embedding constant is the Hölder norm of the weight ratio. -/
theorem norm_holderInclusion_le (w v : Weight)
    (h : Memℓp (fun n : ℤ => (v n : ℂ) / (w n : ℂ)) r) (a : WeightedCoeff w p) :
    ‖holderInclusion (q := q) w v h a‖ ≤ ‖weightRatio w v h‖ * ‖a‖ := by
  change ‖(weightIsometry v q).symm
    (Coeff.holderProduct (q := q) (weightIsometry w p a) (weightRatio w v h))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map, mul_comm] using
    Coeff.norm_holderProduct_le (q := q) (weightIsometry w p a) (weightRatio w v h)

theorem holderInclusion_injective (w v : Weight)
    (h : Memℓp (fun n : ℤ => (v n : ℂ) / (w n : ℂ)) r) :
    Function.Injective (holderInclusion (p := p) (q := q) w v h) := by
  intro a b hab
  apply Subtype.ext
  funext n
  simpa only [holderInclusion_apply] using congrArg (fun c => c.val n) hab

/-- Sobolev gain compensates for a decrease in sequence exponent at the strict threshold. -/
def sobolevHolderInclusion (s t : ℝ) (hr : r ≠ ⊤) (h : 1 < (s - t) * r.toReal) :
    WeightedCoeff (Weight.sobolev s) p →L[ℂ] WeightedCoeff (Weight.sobolev t) q :=
  holderInclusion _ _ (by
    simp only [Weight.sobolev_ratio]
    exact Weight.inverse_sobolev_memlp
      (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le Fact.out)) hr) h)

@[simp] theorem sobolevHolderInclusion_apply (s t : ℝ) (hr : r ≠ ⊤)
    (h : 1 < (s - t) * r.toReal) (a : WeightedCoeff (Weight.sobolev s) p) (n : ℤ) :
    (sobolevHolderInclusion (q := q) s t hr h a).val n = a.val n :=
  holderInclusion_apply _ _ _ a n

/-- The explicit Sobolev Hölder constant, without claiming a unit embedding norm. -/
def sobolevHolderConstant (s t : ℝ) (hr : r ≠ ⊤) (h : 1 < (s - t) * r.toReal) : ℝ :=
  ‖(⟨fun n : ℤ => (Weight.sobolev (s - t) n : ℂ)⁻¹,
    Weight.inverse_sobolev_memlp
      (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le Fact.out)) hr) h⟩ : Coeff r)‖

theorem norm_sobolevHolderInclusion_le (s t : ℝ) (hr : r ≠ ⊤)
    (h : 1 < (s - t) * r.toReal) (a : WeightedCoeff (Weight.sobolev s) p) :
    ‖sobolevHolderInclusion (q := q) s t hr h a‖ ≤ sobolevHolderConstant s t hr h * ‖a‖ := by
  have hb := norm_holderInclusion_le (q := q) (Weight.sobolev s) (Weight.sobolev t)
    (by
      simp only [Weight.sobolev_ratio]
      exact Weight.inverse_sobolev_memlp
        (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le Fact.out)) hr) h) a
  have he : weightRatio (Weight.sobolev s) (Weight.sobolev t) (by
      simp only [Weight.sobolev_ratio]
      exact Weight.inverse_sobolev_memlp
        (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le Fact.out)) hr) h) =
      (⟨fun n : ℤ => (Weight.sobolev (s - t) n : ℂ)⁻¹,
        Weight.inverse_sobolev_memlp
          (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le Fact.out)) hr) h⟩ : Coeff r) := by
    ext n
    exact Weight.sobolev_ratio s t n
  rw [he] at hb
  exact hb

end WeightedCoeff
end NLS
