import NLS.SequenceSpaces.RealCoeff
import NLS.SequenceSpaces.ReciprocalSeries
import Mathlib.Analysis.PSeries

/-!
# A real eighth-power summable sequence with nonsummable fourth powers

The explicit sequence `|n|^(-1/4)`, with value zero at the origin,
provides a target for the local inverse Birkhoff chart in the audit of
Remark 10.9. Every nonzero real multiple has squares outside ℓ².
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- The reciprocal quarter-power sequence on the integer lattice. -/
def quarterPowerWitness (n : ℤ) : ℝ := |(n : ℝ)| ^ (-(1/4 : ℝ))

theorem quarterPowerWitness_nonneg (n : ℤ) : 0 ≤ quarterPowerWitness n :=
  Real.rpow_nonneg (abs_nonneg _) _

theorem quarterPowerWitness_pow (n : ℤ) (k : ℕ) :
    quarterPowerWitness n ^ k = |(n : ℝ)| ^ (-(1/4 : ℝ) * k) := by
  rw [quarterPowerWitness,← Real.rpow_natCast,← Real.rpow_mul (abs_nonneg _)]

theorem memℓp_quarterPowerWitness : Memℓp quarterPowerWitness 8 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (8 : ℝ≥0∞).toReal)]
  have hs := ReciprocalSeries.summable_int_shifted_rpow
    (α := 0) (q := 2) (by norm_num) (by norm_num)
  convert hs using 1
  funext n
  simp only [ENNReal.toReal_ofNat,Real.norm_of_nonneg (quarterPowerWitness_nonneg n),
    Real.rpow_ofNat,quarterPowerWitness_pow]
  by_cases hn : n = 0
  · subst n
    norm_num
  · rw [if_neg hn,zero_add]
    norm_num only [show -(1/4 : ℝ) * (8 : ℕ) = -2 by norm_num]

/-- The real ℓ⁸ coefficient used as inverse-chart data. -/
def quarterPowerCoeff : RealCoeff 8 := ⟨quarterPowerWitness,memℓp_quarterPowerWitness⟩

@[simp] theorem quarterPowerCoeff_apply (n : ℤ) : quarterPowerCoeff n = quarterPowerWitness n := rfl

theorem not_memℓp_quarterPowerWitness_sq :
    ¬ Memℓp (fun n : ℤ => (quarterPowerWitness n : ℂ)^2) 2 := by
  intro h
  have hs := (h.summable (by norm_num)).comp_injective (i := fun n : ℕ => (n : ℤ))
    (by intro a b hab; dsimp only at hab; exact_mod_cast hab)
  have he (n : ℕ) : ‖(quarterPowerWitness (n : ℤ) : ℂ)^2‖ ^ (2 : ℝ≥0∞).toReal =
      (n : ℝ)^(-1 : ℝ) := by
    simp only [norm_pow,Complex.norm_real,
      Real.norm_of_nonneg (quarterPowerWitness_nonneg _),ENNReal.toReal_ofNat,
      Real.rpow_ofNat]
    rw [← pow_mul,quarterPowerWitness_pow]
    norm_num
  simp only [Function.comp_def,he] at hs
  have := Real.summable_nat_rpow.mp hs
  linarith

/-- Nonzero real scaling cannot remove the failure of square summability. -/
theorem not_memℓp_smul_quarterPowerWitness_sq (t : ℝ) (ht : t ≠ 0) :
    ¬ Memℓp (fun n : ℤ => ((t * quarterPowerWitness n : ℝ) : ℂ)^2) 2 := by
  intro h
  apply not_memℓp_quarterPowerWitness_sq
  have hs := h.const_smul (((t : ℂ)^2)⁻¹)
  convert hs using 1
  funext n
  simp only [Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,mul_pow]
  rw [← mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ht)),one_mul]

end NLS
