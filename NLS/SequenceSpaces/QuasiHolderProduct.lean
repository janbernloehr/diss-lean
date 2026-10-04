import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul

/-! # Scalar Hölder products below exponent one

The coefficient product and its norm estimate do not require the target
sequence exponent to be at least one. This is needed for products of
spectral gaps and critical quotients when `1 < p < 2`.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

theorem holderTriple_half (p : ℝ≥0∞) : p.HolderTriple p (p/2) := by
  rw [ENNReal.holderTriple_iff,ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    div_eq_mul_inv,two_mul]

theorem halfExponent_eq_div {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    ENNReal.ofReal (p.toReal/2) = p/2 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_toReal hp]
  norm_num

variable {p q r : ℝ≥0∞} [p.HolderTriple q r]

private theorem complex_mul_norm_le : ‖ContinuousLinearMap.mul ℂ ℂ‖ ≤ (1 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using ContinuousLinearMap.opNorm_mul_apply_le ℂ ℂ x

/-- Pointwise multiplication for any Hölder triple, including quasi-normed targets. -/
def quasiHolderProduct (a : Coeff p) (b : Coeff q) : Coeff r :=
  lp.holder r (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
    (K := 1) (fun _ => complex_mul_norm_le) a b

@[simp] theorem quasiHolderProduct_apply (a : Coeff p) (b : Coeff q) (n : ℤ) :
    quasiHolderProduct (r := r) a b n = a n*b n := rfl

/-- The scalar Hölder constant remains one for all positive finite exponents. -/
theorem norm_quasiHolderProduct_le (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (a : Coeff p) (b : Coeff q) :
    ‖quasiHolderProduct (r := r) a b‖ ≤ ‖a‖*‖b‖ := by
  have ht := ENNReal.HolderTriple.toReal r hp hq
  apply lp.norm_le_of_forall_sum_le ht.pos' (mul_nonneg (lp.norm_nonneg' a) (lp.norm_nonneg' b))
  intro s
  have h := Memℓp.holder_gen_bound r hp hq
    (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
    (K := 1) (fun _ => complex_mul_norm_le) zero_le_one
    (Real.rpow_nonneg (lp.norm_nonneg' a) _)
    (lp.sum_rpow_le_norm_rpow hp a) (lp.sum_rpow_le_norm_rpow hq b) s
  change ∑ i ∈ s, ‖a i*b i‖ ^ r.toReal ≤ _ at h ⊢
  apply h.trans_eq
  rw [Real.one_rpow,one_mul,← Real.rpow_mul (lp.norm_nonneg' a),
    ← Real.rpow_mul (lp.norm_nonneg' b),mul_div_cancel₀ _ hp.ne',mul_div_cancel₀ _ hq.ne',
    Real.mul_rpow (lp.norm_nonneg' a) (lp.norm_nonneg' b)]

end NLS.Coeff
