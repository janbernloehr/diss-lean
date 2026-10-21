import NLS.Fourier.PeriodOneCoefficients
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.Fourier

/-- One-sided geometric Fourier coefficients in the original unit-period index. -/
def geometricPeriodOneCoefficients (q : ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then q^n.toNat else 0

@[simp] theorem geometricPeriodOneCoefficients_nat (q : ℂ) (n : ℕ) :
    geometricPeriodOneCoefficients q n = q^n := by simp [geometricPeriodOneCoefficients]

@[simp] theorem geometricPeriodOneCoefficients_negSucc (q : ℂ) (n : ℕ) :
    geometricPeriodOneCoefficients q (-(n+1)) = 0 := by
  simp only [geometricPeriodOneCoefficients]
  rw [if_neg (by omega)]

/-- The geometric coefficients are absolutely summable whenever the ratio is inside the disk. -/
theorem geometricPeriodOneCoefficients_mem (q : ℂ) (hq : ‖q‖ < 1) :
    Memℓp (geometricPeriodOneCoefficients q) 1 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (1:ℝ≥0∞).toReal)).mpr
  simp only [ENNReal.toReal_one,Real.rpow_one]
  apply Summable.of_nat_of_neg_add_one
  · simpa only [geometricPeriodOneCoefficients_nat,norm_pow] using
      summable_geometric_of_lt_one (norm_nonneg q) hq
  · simp only [geometricPeriodOneCoefficients_negSucc,norm_zero,summable_zero]

/-- The actual l1 sequence, retaining every coefficient. -/
def geometricPeriodOneData (q : ℂ) (hq : ‖q‖ < 1) : Coeff 1 :=
  ⟨geometricPeriodOneCoefficients q,geometricPeriodOneCoefficients_mem q hq⟩

@[simp] theorem geometricPeriodOneData_apply (q : ℂ) (hq : ‖q‖ < 1) (n : ℤ) :
    geometricPeriodOneData q hq n = geometricPeriodOneCoefficients q n := rfl

private theorem wave_even_nat_pow (n : ℕ) (x : ℝ) : wave (2*n) x = (wave 2 x)^n := by
  simp only [wave,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,← Complex.exp_nat_mul]
  congr 1
  ring

/-- The actual Fourier synthesis is the classical geometric rational function. -/
theorem periodOneSynthesis_geometric (q : ℂ) (hq : ‖q‖ < 1) (x : ℝ) :
    periodOneSynthesis (geometricPeriodOneData q hq) x = (1-q*wave 2 x)⁻¹ := by
  have hr : ‖q*wave 2 x‖ < 1 := by simpa [norm_mul,wave,Complex.norm_exp] using hq
  let f : ℤ → ℂ := fun n => geometricPeriodOneData q hq n*wave (2*n) x
  have hpos (n : ℕ) : f n = (q*wave 2 x)^n := by
    simp only [f,geometricPeriodOneData_apply,geometricPeriodOneCoefficients_nat,
      wave_even_nat_pow,mul_pow]
  have hneg (n : ℕ) : f (-(n+1)) = 0 := by
    simp only [f,geometricPeriodOneData_apply,geometricPeriodOneCoefficients_negSucc,zero_mul]
  have hp : Summable (fun n : ℕ => f n) := by
    simp only [hpos]
    exact (hasSum_geometric_of_norm_lt_one hr).summable
  have hn : Summable (fun n : ℕ => f (-(n+1))) := by simp only [hneg,summable_zero]
  rw [periodOneSynthesis_eq_tsum]
  change (∑' n : ℤ, f n) = _
  rw [tsum_of_nat_of_neg_add_one hp hn]
  simp only [hpos,hneg,tsum_zero,add_zero]
  exact tsum_geometric_of_norm_lt_one hr

/-- The actual unit-interval Fourier integrals recover every one-sided geometric coefficient. -/
theorem periodOneCoefficient_geometric (q : ℂ) (hq : ‖q‖ < 1) (n : ℤ) :
    periodOneCoefficient (fun x => (1-q*wave 2 x)⁻¹) n = geometricPeriodOneCoefficients q n := by
  have he : (fun x => (1-q*wave 2 x)⁻¹) = periodOneSynthesis (geometricPeriodOneData q hq) :=
    funext fun x => (periodOneSynthesis_geometric q hq x).symm
  rw [he,periodOneCoefficient_synthesis,geometricPeriodOneData_apply]

end NLS.Fourier
