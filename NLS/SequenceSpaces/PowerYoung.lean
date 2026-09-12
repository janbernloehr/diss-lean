import NLS.SequenceSpaces.PowerCoefficients
import NLS.SequenceSpaces.YoungConvolution

/-!
# Young's inequality for powered magnitudes

Scaling all exponents by a positive real number gives a convolution-root
estimate, including original sequence exponents below one.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- The exponent conditions for applying Young after taking the `t`-th power. -/
structure PowerYoungRelation (p q r t : ℝ) : Prop where
  t_pos : 0 < t
  t_le_p : t ≤ p
  t_le_q : t ≤ q
  t_le_r : t ≤ r
  relation : 1 / t + 1 / r = 1 / p + 1 / q

namespace PowerYoungRelation
variable {p q r t : ℝ} (h : PowerYoungRelation p q r t)
include h

theorem p_pos : 0 < p := h.t_pos.trans_le h.t_le_p
theorem q_pos : 0 < q := h.t_pos.trans_le h.t_le_q
theorem r_pos : 0 < r := h.t_pos.trans_le h.t_le_r

theorem one_le_p : 1 ≤ ENNReal.ofReal (p / t) :=
  ENNReal.one_le_ofReal.mpr ((le_div_iff₀ h.t_pos).mpr (by simpa using h.t_le_p))
theorem one_le_q : 1 ≤ ENNReal.ofReal (q / t) :=
  ENNReal.one_le_ofReal.mpr ((le_div_iff₀ h.t_pos).mpr (by simpa using h.t_le_q))
theorem one_le_r : 1 ≤ ENNReal.ofReal (r / t) :=
  ENNReal.one_le_ofReal.mpr ((le_div_iff₀ h.t_pos).mpr (by simpa using h.t_le_r))

theorem youngRelation : YoungRelation (ENNReal.ofReal (p / t))
    (ENNReal.ofReal (q / t)) (ENNReal.ofReal (r / t)) := by
  have hp := div_pos h.p_pos h.t_pos
  have hq := div_pos h.q_pos h.t_pos
  have hr := div_pos h.r_pos h.t_pos
  unfold YoungRelation
  apply (ENNReal.toReal_eq_toReal_iff' (by simpa using hr)
    (by simpa using And.intro hp hq)).mp
  rw [ENNReal.toReal_add (a := 1) (b := (ENNReal.ofReal (r / t))⁻¹)
    (by simp) (by simpa using hr),
    ENNReal.toReal_add (a := (ENNReal.ofReal (p / t))⁻¹) (b := (ENNReal.ofReal (q / t))⁻¹)
      (by simpa using hp) (by simpa using hq)]
  simp only [ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le,
    ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal hr.le]
  have he := congrArg (fun x : ℝ => t * x) h.relation
  field_simp [h.t_pos.ne', h.p_pos.ne', h.q_pos.ne', h.r_pos.ne'] at he ⊢
  nlinarith

end PowerYoungRelation
namespace Coeff

/-- Every powered scalar convolution in the root construction is summable. -/
theorem summable_powerConvolution {p q r t : ℝ} (h : PowerYoungRelation p q r t)
    (a : Coeff (ENNReal.ofReal p)) (b : Coeff (ENNReal.ofReal q)) (n : ℤ) :
    Summable (fun k : ℤ => ‖a (n - k) * b k‖ ^ t) := by
  let : Fact (1 ≤ ENNReal.ofReal (p / t)) := ⟨h.one_le_p⟩
  let : Fact (1 ≤ ENNReal.ofReal (q / t)) := ⟨h.one_le_q⟩
  have hy := summable_norm_youngConvolution_terms h.youngRelation
    (normPower h.p_pos h.t_pos a) (normPower h.q_pos h.t_pos b) n
  simpa only [normPower_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] using hy

/-- Powered convolution followed by its positive root has the exact Young bound. -/
theorem exists_powerConvolution {p q r t : ℝ} (h : PowerYoungRelation p q r t)
    (a : Coeff (ENNReal.ofReal p)) (b : Coeff (ENNReal.ofReal q)) :
    ∃ d : Coeff (ENNReal.ofReal r),
      (∀ n, d n = ((∑' k : ℤ, ‖a (n - k) * b k‖ ^ t) ^ (1 / t) : ℝ)) ∧
      ‖d‖ ≤ ‖a‖ * ‖b‖ := by
  let : Fact (1 ≤ ENNReal.ofReal (p / t)) := ⟨h.one_le_p⟩
  let : Fact (1 ≤ ENNReal.ofReal (q / t)) := ⟨h.one_le_q⟩
  let : Fact (1 ≤ ENNReal.ofReal (r / t)) := ⟨h.one_le_r⟩
  let w := youngConvolution h.youngRelation (normPower h.p_pos h.t_pos a)
    (normPower h.q_pos h.t_pos b)
  have hw (n : ℤ) : w n = ((∑' k : ℤ, ‖a (n - k) * b k‖ ^ t) : ℝ) := by
    simp only [w, youngConvolution_apply, normPower_apply, norm_mul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Complex.ofReal_tsum, Complex.ofReal_mul]
  have he : (r / t) / (1 / t) = r := by field_simp [h.t_pos.ne']
  suffices hz : ∃ d : Coeff (ENNReal.ofReal ((r / t) / (1 / t))),
      (∀ n, d n = ((∑' k : ℤ, ‖a (n - k) * b k‖ ^ t) ^ (1 / t) : ℝ)) ∧
      ‖d‖ ≤ ‖a‖ * ‖b‖ by
    convert! hz using 1 <;> rw [he]
  refine ⟨normPower (div_pos h.r_pos h.t_pos) (one_div_pos.mpr h.t_pos) w, ?_, ?_⟩
  · intro n
    rw [normPower_apply, hw, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg (fun _ => by positivity))]
  · rw [norm_normPower]
    have hn : ‖w‖ ≤ (‖a‖ * ‖b‖) ^ t := by
      have hy := norm_youngConvolution_le h.youngRelation
        (normPower h.p_pos h.t_pos a) (normPower h.q_pos h.t_pos b)
      simpa only [norm_normPower, Real.mul_rpow (lp.norm_nonneg' a) (lp.norm_nonneg' b)] using hy
    calc
      ‖w‖ ^ (1 / t) ≤ ((‖a‖ * ‖b‖) ^ t) ^ (1 / t) :=
        Real.rpow_le_rpow (norm_nonneg _) hn (one_div_pos.mpr h.t_pos).le
      _ = ‖a‖ * ‖b‖ := by
        rw [one_div, Real.rpow_rpow_inv (mul_nonneg (lp.norm_nonneg' a) (lp.norm_nonneg' b)) h.t_pos.ne']

end Coeff
end NLS
