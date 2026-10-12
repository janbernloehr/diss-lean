import NLS.SequenceSpaces.PairNorm
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.ENNReal.Holder

/-! # The exact two-component lp-to-l1 comparison factor -/
noncomputable section
open scoped ENNReal
namespace NLS.CoeffPair

/-- Conversion of a two-component p-norm to the sum of component norms. -/
def l1Factor (p : ℝ≥0∞) : ℝ := (2 : ℝ)^(1-1/p.toReal)

@[simp] theorem l1Factor_one : l1Factor 1 = 1 := by simp [l1Factor]

theorem l1Factor_pos (p : ℝ≥0∞) : 0 < l1Factor p := by unfold l1Factor; positivity

theorem l1Factor_le_two (p : ℝ≥0∞) : l1Factor p ≤ 2 := by
  calc
    _ ≤ (2 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (sub_le_self _ (one_div_nonneg.mpr ENNReal.toReal_nonneg))
    _ = 2 := Real.rpow_one _

/-- The factor compensates exactly for the norm of two equal unit components. -/
theorem l1Factor_mul_rpow (p : ℝ≥0∞) : l1Factor p * (2 : ℝ)^(1/p.toReal) = 2 := by
  rw [l1Factor, ← Real.rpow_add (by norm_num), sub_add_cancel, Real.rpow_one]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original l1 pair norm is the sum of its component norms. -/
theorem norm_one_eq_sum (a : CoeffPair 1) : ‖a‖ = ‖a.fst‖+‖a.snd‖ := by
  simpa only [ENNReal.toReal_one, Real.rpow_one] using
    norm_withLp_prod_rpow (p := 1) (by norm_num) a

/-- Hölder on the two components, including the endpoint p=1. -/
theorem componentNormSum_le (hp : p ≠ ⊤) (a : CoeffPair p) :
    ‖a.fst‖+‖a.snd‖ ≤ l1Factor p*‖a‖ := by
  by_cases hp1 : p = 1
  · subst p
    rw [l1Factor_one, one_mul, norm_one_eq_sum]
  have hp1' : 1 < p := lt_of_le_of_ne Fact.out (Ne.symm hp1)
  have hq : p.conjExponent ≠ ⊤ := ne_of_lt
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1')
  have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hpp : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun i : Bool => if i then ‖a.fst‖ else ‖a.snd‖) (g := fun _ : Bool => (1 : ℝ)) hpq
    (fun i _ => by cases i <;> simp) (fun _ _ => by norm_num)
  have he : 1/p.conjExponent.toReal = 1-1/p.toReal := by
    simp only [one_div]
    linarith [hpq.inv_add_inv_eq_one]
  rw [l1Factor, WithLp.prod_norm_eq_add hpp]
  simpa [he, add_comm, mul_comm] using hh

/-- Equal nonzero components attain the comparison factor. -/
theorem l1Factor_mul_norm_diagonal (hp : p ≠ ⊤) (a : Coeff p) :
    l1Factor p*‖(toMax p).symm (a,a)‖ = 2*‖a‖ := by
  rw [norm_diagonal hp, ← mul_assoc, l1Factor, ← Real.rpow_add (by norm_num)]
  ring_nf
  simp [mul_comm]

end NLS.CoeffPair
