import NLS.ZakharovShabat.ComplementaryL1
import NLS.SequenceSpaces.ConjugateDuality
import NLS.SequenceSpaces.Multiplier

/-!
# Reciprocal row estimates for the diagonal coefficient

The actual diagonal Fourier row is dominated in its conjugate norm by a
parameter-independent punctured lattice row. The norm retains the shifted
potential coefficients needed for the frequency summation in Lemma 6.8(i).
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The actual row in physical frequency coordinates, with its removed resonant denominator. -/
def complementaryPotentialRow (hq : 1 < q) (a : Coeff p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) : Coeff q :=
  Coeff.multiplier (Coeff.reindex (Equiv.subLeft n) (Coeff.exponentInclusion le_top a))
    (complementaryReciprocal hq n z hz true)

@[simp] theorem complementaryPotentialRow_apply (hq : 1 < q) (a : Coeff p) (n : ℤ)
    (z : ℂ) (hz : z ∈ resonantStrip n) (k : ℤ) :
    complementaryPotentialRow hq a n z hz k = a (n-k) * complementarySymbol n z (-k) := rfl

/-- The parameter-independent reciprocal row majorant, in exactly the same sequence exponent. -/
def complementaryRowEnvelope (hq : 1 < q) (a : Coeff p) (n : ℤ) : Coeff q :=
  Coeff.multiplier (Coeff.reindex (Equiv.subLeft n) (Coeff.exponentInclusion le_top a))
    (Coeff.reindex ((freeFrequencyEquiv true).trans (Equiv.subRight n)) (Coeff.puncturedLattice q hq))

@[simp] theorem complementaryRowEnvelope_apply (hq : 1 < q) (a : Coeff p) (n k : ℤ) :
    complementaryRowEnvelope hq a n k = a (n-k) * Coeff.puncturedLattice q hq (-k-n) := rfl

/-- The actual spectral row is dominated uniformly throughout the full closed strip. -/
theorem norm_complementaryPotentialRow_le (hq : 1 < q) (a : Coeff p) (n : ℤ)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖complementaryPotentialRow hq a n z hz‖ ≤ ‖complementaryRowEnvelope hq a n‖ := by
  apply lp.norm_mono (zero_lt_one.trans hq).ne'
  intro k
  simp only [complementaryPotentialRow_apply, complementaryRowEnvelope_apply, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_complementarySymbol_le_lattice hq hz (-k)) (norm_nonneg _)

/-- Every row has a finite bound depending only on the potential norm and reciprocal exponent. -/
theorem norm_complementaryRowEnvelope_le (hq : 1 < q) (a : Coeff p) (n : ℤ) :
    ‖complementaryRowEnvelope hq a n‖ ≤ ‖a‖ * ‖Coeff.puncturedLattice q hq‖ := by
  apply (Coeff.norm_multiplier_le _ _).trans
  rw [Coeff.norm_reindex, Coeff.norm_reindex]
  exact mul_le_mul_of_nonneg_right (Coeff.norm_exponentInclusion_le le_top a) (norm_nonneg _)

/-- Absolute convergence of the diagonal row against a conjugate input. -/
theorem summable_complementaryRow [p.HolderConjugate q] (hq : 1 < q) (a b : Coeff p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    Summable (fun k : ℤ => a (n-k) * complementarySymbol n z (-k) * b k) := by
  simpa only [complementaryPotentialRow_apply, mul_comm (b _)] using
    (Coeff.summable_norm_dualPairing b (complementaryPotentialRow hq a n z hz)).of_norm

/-- Hölder's inequality for the exact diagonal Fourier row, with its conjugate row norm retained. -/
theorem norm_tsum_complementaryRow_le [p.HolderConjugate q] (hq : 1 < q) (a b : Coeff p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖∑' k : ℤ, a (n-k) * complementarySymbol n z (-k) * b k‖ ≤
      ‖b‖ * ‖complementaryRowEnvelope hq a n‖ := by
  have he : (∑' k : ℤ, a (n-k) * complementarySymbol n z (-k) * b k) =
      Coeff.dualPairing b (complementaryPotentialRow hq a n z hz) := by
    rw [Coeff.dualPairing_apply]
    apply tsum_congr
    intro k
    rw [complementaryPotentialRow_apply, mul_comm (b k)]
  rw [he]
  exact (Coeff.norm_dualPairing_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_complementaryPotentialRow_le hq a n z hz) (norm_nonneg _))

/-- The row norm is precisely the reciprocal sum in the source's signed Fourier basis.
Division by zero makes the excluded term vanish. -/
theorem norm_complementaryRowEnvelope_eq (hq : 1 < q) (hqt : q ≠ ⊤) (a : Coeff p) (n : ℤ) :
    ‖complementaryRowEnvelope hq a n‖ =
      (∑' m : ℤ, (‖a (n+m)‖ / |((m-n : ℤ) : ℝ)|) ^ q.toReal) ^ (1/q.toReal) := by
  rw [lp.norm_eq_tsum_rpow (ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt)]
  congr 1
  rw [← (freeFrequencyEquiv true).tsum_eq]
  apply tsum_congr
  intro m
  simp only [freeFrequencyEquiv_apply, freeFrequency_true, complementaryRowEnvelope_apply,
    sub_neg_eq_add, neg_neg, norm_mul, Coeff.puncturedLattice_apply]
  by_cases hm : m = n
  · simp [hm]
  · simp only [if_neg (sub_ne_zero.mpr hm), norm_inv, Complex.norm_intCast, div_eq_mul_inv]

end NLS.ZakharovShabat
