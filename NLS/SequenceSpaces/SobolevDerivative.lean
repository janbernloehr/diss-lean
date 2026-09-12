import NLS.SequenceSpaces.WeightedMultiplier
import NLS.ZakharovShabat.Domain

/-!
# Embeddings and differentiation on the full Sobolev coefficient scale

The regularity is any real number and the exponent may be infinity. The
derivative loses exactly one unit of regularity; its graph recovers that unit.
-/

noncomputable section
open scoped ENNReal
namespace NLS

namespace Weight

theorem sobolev_mono {s t : ℝ} (h : t ≤ s) (n : ℤ) : sobolev t n ≤ sobolev s n :=
  Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (abs_nonneg _)) h

theorem sobolev_add (s t : ℝ) (n : ℤ) :
    sobolev (s + t) n = sobolev s n * sobolev t n :=
  Real.rpow_add (by positivity) _ _

theorem sobolev_derivative_bound (s : ℝ) (n : ℤ) :
    sobolev s n * ‖Complex.I * (Real.pi : ℂ) * n‖ ≤ Real.pi * sobolev (s + 1) n := by
  rw [sobolev_add]
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, one_mul, Complex.norm_intCast,
    sobolev_apply, Real.rpow_one]
  have hw : 0 ≤ (1 + |(n : ℝ)|) ^ s := (Real.rpow_pos_of_pos (by positivity) s).le
  nlinarith [mul_nonneg Real.pi_pos.le hw]

end Weight
namespace WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Decreasing real regularity preserves the raw Fourier sequence. -/
def sobolevInclusion {s t : ℝ} (h : t ≤ s) :
    WeightedCoeff (Weight.sobolev s) p →L[ℂ] WeightedCoeff (Weight.sobolev t) p :=
  inclusionCLM _ _ (Weight.sobolev_mono h)

@[simp] theorem sobolevInclusion_apply {s t : ℝ} (h : t ≤ s)
    (a : WeightedCoeff (Weight.sobolev s) p) (n : ℤ) :
    (sobolevInclusion h a).val n = a.val n := inclusionCLM_apply _ _ _ a n

theorem norm_sobolevInclusion_le {s t : ℝ} (h : t ≤ s)
    (a : WeightedCoeff (Weight.sobolev s) p) : ‖sobolevInclusion h a‖ ≤ ‖a‖ :=
  norm_inclusionCLM_le _ _ _ a

theorem sobolevInclusion_injective {s t : ℝ} (h : t ≤ s) :
    Function.Injective (sobolevInclusion (p := p) h) := inclusionCLM_injective _ _ _

@[simp] theorem sobolevInclusion_trans {s t u : ℝ} (hst : t ≤ s) (htu : u ≤ t)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    sobolevInclusion htu (sobolevInclusion hst a) = sobolevInclusion (htu.trans hst) a := by
  apply Subtype.ext
  funext n
  simp only [sobolevInclusion_apply]

/-- Period-two differentiation from regularity `s+1` to regularity `s`. -/
def sobolevDerivative (s : ℝ) :
    WeightedCoeff (Weight.sobolev (s + 1)) p →L[ℂ] WeightedCoeff (Weight.sobolev s) p :=
  weightedMultiplierCLM _ _ (fun n => Complex.I * (Real.pi : ℂ) * n)
    Real.pi Real.pi_pos.le (Weight.sobolev_derivative_bound s)

@[simp] theorem sobolevDerivative_apply (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev (s + 1)) p) (n : ℤ) :
    (sobolevDerivative s a).val n = Complex.I * (Real.pi : ℂ) * n * a.val n := rfl

theorem norm_sobolevDerivative_le (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev (s + 1)) p) :
    ‖sobolevDerivative s a‖ ≤ Real.pi * ‖a‖ :=
  norm_weightedMultiplier_le _ _ _ _ Real.pi_pos.le (Weight.sobolev_derivative_bound s) a

omit [Fact (1 ≤ p)] in
/-- A sequence and its derivative in regularity `s` recover regularity `s+1`. -/
theorem memlp_sobolev_succ_of_derivative (s : ℝ) {a : ℤ → ℂ}
    (ha : Memℓp (fun n => (Weight.sobolev s n : ℂ) * a n) p)
    (hd : Memℓp (fun n => (Weight.sobolev s n : ℂ) *
      (Complex.I * (Real.pi : ℂ) * n * a n)) p) :
    Memℓp (fun n => (Weight.sobolev (s + 1) n : ℂ) * a n) p := by
  have hd' : Memℓp (fun n => Complex.I * (Real.pi : ℂ) * n *
      ((Weight.sobolev s n : ℂ) * a n)) p := by
    convert hd using 1
    funext n
    ring
  convert ZakharovShabat.memlp_sobolev_weight_of_derivative ha hd' using 1
  funext n
  rw [Weight.sobolev_add, Complex.ofReal_mul]
  ring

end WeightedCoeff
end NLS
