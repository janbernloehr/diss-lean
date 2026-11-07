import NLS.SequenceSpaces.SignedPositiveSplice
import NLS.SequenceSpaces.WeightedMultiplier
import Mathlib.Analysis.Real.Pi.Bounds

/-! Even extension of positive samples divided by their original free
frequency pi*n. This fixed linear operation gains a full Sobolev order
in every Banach exponent and sets the central coefficient to zero. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Coeff

def evenReciprocalSymbol (k : ℤ) : ℂ :=
  if k = 0 then 0 else ((Real.pi : ℂ) * (k.natAbs : ℕ))⁻¹

theorem evenReciprocalSymbol_weight_bound (k : ℤ) :
    Weight.sobolev 1 k * ‖evenReciprocalSymbol k‖ ≤ 2 * Weight.one k := by
  by_cases hk : k = 0
  · simp only [evenReciprocalSymbol, if_pos hk, norm_zero, mul_zero, Weight.one_apply]
    norm_num
  · have hn : (1 : ℝ) ≤ (k.natAbs : ℕ) := by
      exact_mod_cast (Int.natAbs_pos.mpr hk)
    have hpi : 0 < Real.pi * (k.natAbs : ℕ) := mul_pos Real.pi_pos (by linarith)
    simp only [evenReciprocalSymbol, if_neg hk, norm_inv, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_natCast,
      Weight.sobolev_apply, Real.rpow_one, Weight.one_apply]
    rw [mul_inv_le_iff₀ hpi]
    have he : |(k : ℝ)| = (k.natAbs : ℕ) := by simp
    rw [he]
    nlinarith [Real.pi_gt_three]

def sobolevEvenReciprocal (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Coeff p →L[ℂ] WeightedCoeff (Weight.sobolev 1) p :=
  (WeightedCoeff.weightedMultiplierCLM Weight.one (Weight.sobolev 1)
    evenReciprocalSymbol 2 (by norm_num) evenReciprocalSymbol_weight_bound).comp
      ((WeightedCoeff.weightIsometry Weight.one p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (Coeff.signedPositiveSplice.comp
          ((ContinuousLinearMap.id ℂ (Coeff p)).prod (ContinuousLinearMap.id ℂ (Coeff p)))))

theorem sobolevEvenReciprocal_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Coeff p) (k : ℤ) :
    (sobolevEvenReciprocal p a).val k =
      if k = 0 then 0 else a (k.natAbs : ℤ) / ((Real.pi : ℂ) * (k.natAbs : ℕ)) := by
  change evenReciprocalSymbol k *
    (Coeff.signedPositiveSplice (a,a) k / (Weight.one k : ℂ)) = _
  simp only [Weight.one_apply, ofReal_one, div_one]
  by_cases hk : k = 0
  · simp only [evenReciprocalSymbol, if_pos hk, zero_mul]
  · simp only [evenReciprocalSymbol, if_neg hk]
    rcases lt_or_gt_of_ne hk with hkn | hkp
    · rw [Coeff.signedPositiveSplice_negative _ _ k hkn,
        show (k.natAbs : ℤ) = -k by omega]
      exact (div_eq_inv_mul _ _).symm
    · rw [Coeff.signedPositiveSplice_positive _ _ k hkp,
        show (k.natAbs : ℤ) = k by omega]
      exact (div_eq_inv_mul _ _).symm

end NLS.Coeff
