import NLS.SequenceSpaces.Weighted
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# The finite-exponent Fourier pair norm

Chapter 1, equation (1.2), uses the sum of both component coefficient energies.
`CoeffPair` and `WeightedCoeffPair` carry that actual norm for finite `p ≥ 1`.
Their continuous linear equivalences with maximum-norm products preserve the
coefficients and give explicit norm comparisons. The `p = ∞` norm in the
source is different and is implemented in `NLS.SequenceSpaces.PairNormInfty`.
-/

noncomputable section
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Raising a finite product `lp` norm to its exponent gives the two component energies. -/
theorem norm_withLp_prod_rpow {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (hp : p ≠ ⊤) (u : WithLp p (E × F)) :
    ‖u‖ ^ p.toReal = ‖u.fst‖ ^ p.toReal + ‖u.snd‖ ^ p.toReal := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  rw [WithLp.prod_norm_eq_add hp0, ← Real.rpow_mul (by positivity),
    one_div_mul_cancel hp0.ne', Real.rpow_one]

/-- The sum norm dominates the maximum norm, without changing the underlying pair. -/
theorem norm_ofLp_prod_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (u : WithLp p (E × F)) : ‖u.ofLp‖ ≤ ‖u‖ :=
  max_le (WithLp.norm_fst_le E u) (WithLp.norm_snd_le E u)

/-- The reverse comparison has the sharp factor `2^(1/p)`. -/
theorem norm_withLp_prod_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (hp : p ≠ ⊤) (u : WithLp p (E × F)) :
    ‖u‖ ≤ (2 : ℝ) ^ (1 / p.toReal) * ‖u.ofLp‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  calc
    ‖u‖ = (‖u.fst‖ ^ p.toReal + ‖u.snd‖ ^ p.toReal) ^ (1 / p.toReal) :=
      WithLp.prod_norm_eq_add hp0 u
    _ ≤ (‖u.ofLp‖ ^ p.toReal + ‖u.ofLp‖ ^ p.toReal) ^ (1 / p.toReal) := by
      gcongr
      · exact norm_fst_le u.ofLp
      · exact norm_snd_le u.ofLp
    _ = (2 : ℝ) ^ (1 / p.toReal) * ‖u.ofLp‖ := by
      rw [← two_mul, Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hp0.ne', Real.rpow_one]

/-- Two Fourier coefficient sequences with the finite-exponent component-sum norm. -/
abbrev CoeffPair (p : ℝ≥0∞) := WithLp p (Coeff p × Coeff p)

namespace CoeffPair

/-- Changing to the maximum norm preserves every coefficient and the complex linear topology. -/
def toMax (p : ℝ≥0∞) [Fact (1 ≤ p)] : CoeffPair p ≃L[ℂ] Coeff p × Coeff p :=
  WithLp.prodContinuousLinearEquiv p ℂ _ _

@[simp] theorem toMax_apply (u : CoeffPair p) : toMax p u = u.ofLp := rfl

@[simp] theorem toMax_symm_apply (u : Coeff p × Coeff p) :
    (toMax p).symm u = WithLp.toLp p u := rfl

/-- The exact coefficient energy in equation (1.2), at regularity zero. -/
theorem norm_rpow_eq_tsum (hp : p ≠ ⊤) (u : CoeffPair p) :
    ‖u‖ ^ p.toReal = ∑' n : ℤ, (‖u.fst n‖ ^ p.toReal + ‖u.snd n‖ ^ p.toReal) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  rw [norm_withLp_prod_rpow hp, lp.norm_rpow_eq_tsum hp0, lp.norm_rpow_eq_tsum hp0,
    Summable.tsum_add (u.fst.property.summable hp0) (u.snd.property.summable hp0)]

/-- The source's finite-`p` pair norm is the `p`-th root of the combined Fourier energy. -/
theorem norm_eq_tsum_rpow (hp : p ≠ ⊤) (u : CoeffPair p) :
    ‖u‖ = (∑' n : ℤ, (‖u.fst n‖ ^ p.toReal + ‖u.snd n‖ ^ p.toReal)) ^ (1 / p.toReal) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  rw [← norm_rpow_eq_tsum hp u, ← Real.rpow_mul (norm_nonneg _),
    mul_one_div_cancel hp0.ne', Real.rpow_one]

/-- Moving to the maximum norm is contractive. -/
theorem norm_toMax_le (u : CoeffPair p) : ‖toMax p u‖ ≤ ‖u‖ := norm_ofLp_prod_le u

/-- The exact reverse norm-comparison constant for the existing coefficient parameter space. -/
theorem norm_toMax_symm_le (hp : p ≠ ⊤) (u : Coeff p × Coeff p) :
    ‖(toMax p).symm u‖ ≤ (2 : ℝ) ^ (1 / p.toReal) * ‖u‖ :=
  norm_withLp_prod_le hp (WithLp.toLp p u)

/-- Equal components attain the factor `2^(1/p)`, so the reverse comparison is sharp. -/
theorem norm_diagonal (hp : p ≠ ⊤) (a : Coeff p) :
    ‖(toMax p).symm (a, a)‖ = (2 : ℝ) ^ (1 / p.toReal) * ‖a‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  rw [WithLp.prod_norm_eq_add hp0]
  change (‖a‖ ^ p.toReal + ‖a‖ ^ p.toReal) ^ (1 / p.toReal) = _
  rw [← two_mul, Real.mul_rpow (by norm_num) (by positivity),
    ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hp0.ne', Real.rpow_one]

end CoeffPair

/-- Two weighted Fourier sequences with the finite-exponent component-sum norm. -/
abbrev WeightedCoeffPair (w : Weight) (p : ℝ≥0∞) :=
  WithLp p (WeightedCoeff w p × WeightedCoeff w p)

namespace WeightedCoeffPair

/-- The weighted pair topology agrees with the existing maximum-norm domain topology. -/
def toMax (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WeightedCoeffPair w p ≃L[ℂ] WeightedCoeff w p × WeightedCoeff w p :=
  WithLp.prodContinuousLinearEquiv p ℂ _ _

@[simp] theorem toMax_apply (w : Weight) (u : WeightedCoeffPair w p) : toMax w p u = u.ofLp := rfl

/-- The combined weighted coefficient energy, for every positive weight. -/
theorem norm_rpow_eq_tsum (hp : p ≠ ⊤) (w : Weight) (u : WeightedCoeffPair w p) :
    ‖u‖ ^ p.toReal = ∑' n : ℤ, (w n) ^ p.toReal *
      (‖u.fst.val n‖ ^ p.toReal + ‖u.snd.val n‖ ^ p.toReal) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  have h₁ := lp.hasSum_norm hp0 (WeightedCoeff.weightEquiv w p u.fst)
  have h₂ := lp.hasSum_norm hp0 (WeightedCoeff.weightEquiv w p u.snd)
  rw [norm_withLp_prod_rpow hp, WeightedCoeff.norm_eq, WeightedCoeff.norm_eq]
  have h := (h₁.add h₂).tsum_eq.symm
  simpa only [WeightedCoeff.weightEquiv_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (w.positive _), Real.mul_rpow (w.positive _).le (norm_nonneg _),
    ← mul_add] using h

/-- Equation (1.2) at arbitrary real Sobolev regularity, with its exact `sp` exponent. -/
theorem sobolev_norm_rpow_eq_tsum (hp : p ≠ ⊤) (s : ℝ) (u : WeightedCoeffPair (Weight.sobolev s) p) :
    ‖u‖ ^ p.toReal = ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (s * p.toReal) *
      (‖u.fst.val n‖ ^ p.toReal + ‖u.snd.val n‖ ^ p.toReal) := by
  rw [norm_rpow_eq_tsum hp]
  simp only [Weight.sobolev_apply, ← Real.rpow_mul (by positivity : 0 ≤ 1 + |(_ : ℝ)|)]

/-- The weighted maximum norm is bounded by the dissertation's sum norm. -/
theorem norm_toMax_le (w : Weight) (u : WeightedCoeffPair w p) : ‖toMax w p u‖ ≤ ‖u‖ :=
  norm_ofLp_prod_le u

/-- The reverse comparison for arbitrary weighted pair domains. -/
theorem norm_toMax_symm_le (hp : p ≠ ⊤) (w : Weight) (u : WeightedCoeff w p × WeightedCoeff w p) :
    ‖(toMax w p).symm u‖ ≤ (2 : ℝ) ^ (1 / p.toReal) * ‖u‖ :=
  norm_withLp_prod_le hp (WithLp.toLp p u)

end WeightedCoeffPair
end NLS
