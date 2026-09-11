import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Inversion from a small square

For a bounded operator `K`, the condition `‖K²‖ < 1` suffices to invert `1 - K`,
even when `‖K‖ ≥ 1`. This is the algebraic step used after Lemma 3.4.
-/

noncomputable section

namespace NLS.SquaredNeumann

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The geometric inverse of `1 - K²`. -/
def evenCorrection (K : E →L[ℂ] E) (h : ‖K ^ 2‖ < 1) : E →L[ℂ] E :=
  ↑(Units.oneSub (K ^ 2) h)⁻¹

theorem evenCorrection_hasSum (K : E →L[ℂ] E) (h : ‖K ^ 2‖ < 1) :
    HasSum (fun n : ℕ => (K ^ 2) ^ n) (evenCorrection K h) :=
  (summable_geometric_of_norm_lt_one h).hasSum

theorem evenCorrection_mul (K : E →L[ℂ] E) (h : ‖K ^ 2‖ < 1) :
    evenCorrection K h * (1 - K ^ 2) = 1 :=
  geom_series_mul_neg (K ^ 2) h

theorem mul_evenCorrection (K : E →L[ℂ] E) (h : ‖K ^ 2‖ < 1) :
    (1 - K ^ 2) * evenCorrection K h = 1 :=
  mul_neg_geom_series (K ^ 2) h

/-- The squared Neumann inverse `(1 + K) (1 - K²)⁻¹`. -/
def correction (K : E →L[ℂ] E) (h : ‖K ^ 2‖ < 1) : E →L[ℂ] E :=
  (1 + K) * evenCorrection K h

theorem mul_correction (K : E →L[ℂ] E) (h : ‖K ^ 2‖ < 1) :
    (1 - K) * correction K h = 1 := by
  rw [correction, ← mul_assoc]
  have he : (1 - K) * (1 + K) = 1 - K ^ 2 := by noncomm_ring
  rw [he, mul_evenCorrection]

theorem correction_eq_evenCorrection_mul (K : E →L[ℂ] E) (h : ‖K ^ 2‖ < 1) :
    correction K h = evenCorrection K h * (1 + K) := by
  have he : (1 + K) * (1 - K) = 1 - K ^ 2 := by noncomm_ring
  have hl : (evenCorrection K h * (1 + K)) * (1 - K) = 1 := by
    rw [mul_assoc, he, evenCorrection_mul]
  calc
    correction K h = 1 * correction K h := (one_mul _).symm
    _ = ((evenCorrection K h * (1 + K)) * (1 - K)) * correction K h := by rw [hl]
    _ = evenCorrection K h * (1 + K) := by rw [mul_assoc, mul_correction, mul_one]

theorem correction_mul (K : E →L[ℂ] E) (h : ‖K ^ 2‖ < 1) :
    correction K h * (1 - K) = 1 := by
  rw [correction_eq_evenCorrection_mul, mul_assoc]
  have he : (1 + K) * (1 - K) = 1 - K ^ 2 := by noncomm_ring
  rw [he, evenCorrection_mul]

theorem correction_left (K : E →L[ℂ] E) (h : ‖K ^ 2‖ < 1) (a : E) :
    correction K h (a - K a) = a :=
  congrArg (fun T : E →L[ℂ] E => T a) (correction_mul K h)

theorem correction_right (K : E →L[ℂ] E) (h : ‖K ^ 2‖ < 1) (a : E) :
    correction K h a - K (correction K h a) = a :=
  congrArg (fun T : E →L[ℂ] E => T a) (mul_correction K h)

theorem norm_evenCorrection_le (K : E →L[ℂ] E) (h : ‖K ^ 2‖ < 1) :
    ‖evenCorrection K h‖ ≤ (1 - ‖K ^ 2‖)⁻¹ := by
  have hg := tsum_geometric_le_of_norm_lt_one (K ^ 2) h
  have hid : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  change ‖evenCorrection K h‖ ≤ _ at hg
  linarith

theorem norm_correction_le (K : E →L[ℂ] E) (h : ‖K ^ 2‖ < 1) :
    ‖correction K h‖ ≤ (1 + ‖K‖) * (1 - ‖K ^ 2‖)⁻¹ := by
  have hid : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact (norm_mul_le _ _).trans (mul_le_mul
    ((norm_add_le _ _).trans (add_le_add hid le_rfl))
    (norm_evenCorrection_le K h) (norm_nonneg _) (by positivity))

/-- When the square vanishes, inversion terminates after its linear term. -/
theorem correction_eq_one_add_of_sq_eq_zero (K : E →L[ℂ] E) (h : ‖K ^ 2‖ < 1)
    (hK : K ^ 2 = 0) : correction K h = 1 + K := by
  have he := evenCorrection_mul K h
  rw [hK, sub_zero, mul_one] at he
  rw [correction, he, mul_one]

end NLS.SquaredNeumann
