import NLS.SequenceSpaces.RealCoeff
import NLS.SequenceSpaces.ReciprocalSeries
import Mathlib.Analysis.PSeries

/-!
# Explicit witnesses for sharp squared-sequence exponents

The real sequence `|n|^(-1/(2r))` belongs to ℓᵖ when `2r<p`,
but its squares do not belong to ℓʳ. This remains true after every
nonzero real scaling, also for quasi-normed target exponents.
-/

noncomputable section
open scoped ENNReal
namespace NLS

def squaredExponentWitness (r : ℝ) (n : ℤ) : ℝ := |(n : ℝ)| ^ (-(2*r)⁻¹)

theorem squaredExponentWitness_nonneg (r : ℝ) (n : ℤ) : 0 ≤ squaredExponentWitness r n :=
  Real.rpow_nonneg (abs_nonneg _) _

theorem memℓp_squaredExponentWitness {p : ℝ≥0∞} {r : ℝ}
    (hr : 0 < r) (hrp : 2*r < p.toReal) : Memℓp (squaredExponentWitness r) p := by
  have hp : 0 < p.toReal := by linarith
  have hq : 1 < p.toReal/(2*r) := (one_lt_div (by positivity)).mpr hrp
  rw [memℓp_gen_iff hp]
  have hs := ReciprocalSeries.summable_int_shifted_rpow (α := 0) (q := p.toReal/(2*r))
    (by norm_num) hq
  convert hs using 1
  funext n
  rw [Real.norm_of_nonneg (squaredExponentWitness_nonneg r n),squaredExponentWitness,
    ← Real.rpow_mul (abs_nonneg _)]
  have he : -(2*r)⁻¹*p.toReal = -(p.toReal/(2*r)) := by ring
  rw [he]
  by_cases hn : n = 0
  · subst n
    simp only [Int.cast_zero,abs_zero]
    exact Real.zero_rpow (by linarith)
  · simp only [if_neg hn,zero_add]

/-- A real source-coordinate sequence with the prescribed sharp square exponent. -/
def squaredExponentCoeff {p : ℝ≥0∞} {r : ℝ} (hr : 0 < r) (hrp : 2*r < p.toReal) :
    RealCoeff p := ⟨squaredExponentWitness r,memℓp_squaredExponentWitness hr hrp⟩

@[simp] theorem squaredExponentCoeff_apply {p : ℝ≥0∞} {r : ℝ}
    (hr : 0 < r) (hrp : 2*r < p.toReal) (n : ℤ) :
    squaredExponentCoeff hr hrp n = squaredExponentWitness r n := rfl

theorem norm_squaredExponentWitness_sq_rpow {r : ℝ} (hr : 0 < r) (n : ℤ) :
    ‖(squaredExponentWitness r n : ℂ)^2‖ ^ r = |(n : ℝ)| ^ (-1 : ℝ) := by
  rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (squaredExponentWitness_nonneg r n),
    ← Real.rpow_natCast,← Real.rpow_mul (squaredExponentWitness_nonneg r n),
    squaredExponentWitness,← Real.rpow_mul (abs_nonneg _)]
  congr 1
  norm_num only [Nat.cast_ofNat]
  field_simp

theorem not_memℓp_squaredExponentWitness_sq {r : ℝ≥0∞} (hr : 0 < r.toReal) :
    ¬ Memℓp (fun n : ℤ => (squaredExponentWitness r.toReal n : ℂ)^2) r := by
  intro h
  have hs := (h.summable hr).comp_injective (i := fun n : ℕ => (n : ℤ))
    (by intro a b hab; dsimp only at hab; exact_mod_cast hab)
  have he (n : ℕ) : ‖(squaredExponentWitness r.toReal (n : ℤ) : ℂ)^2‖ ^ r.toReal =
      (n : ℝ)^(-1 : ℝ) := by
    rw [norm_squaredExponentWitness_sq_rpow hr,Int.cast_natCast,
      abs_of_nonneg (Nat.cast_nonneg n)]
  have hnat : Summable (fun n : ℕ => (n : ℝ)^(-1 : ℝ)) :=
    hs.congr (fun n => he n)
  have := Real.summable_nat_rpow.mp hnat
  linarith

theorem not_memℓp_smul_squaredExponentWitness_sq {r : ℝ≥0∞} (hr : 0 < r.toReal)
    (t : ℝ) (ht : t ≠ 0) :
    ¬ Memℓp (fun n : ℤ => ((t*squaredExponentWitness r.toReal n : ℝ) : ℂ)^2) r := by
  intro h
  apply not_memℓp_squaredExponentWitness_sq hr
  have hs := h.const_smul (((t : ℂ)^2)⁻¹)
  convert hs using 1
  funext n
  simp only [Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,mul_pow]
  rw [← mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ht)),one_mul]

end NLS
