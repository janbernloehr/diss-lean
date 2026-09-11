import NLS.SequenceSpaces.Weighted
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Weighted coefficients embedded in `l1`

Hölder's inequality gives an embedding whenever the inverse weight belongs to
the conjugate sequence space. The formulation includes the `p=1`, `q=∞`
endpoint and keeps the dependence on the weight explicit.
-/

open scoped ENNReal
noncomputable section

namespace NLS.WeightedCoeff

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

private theorem complex_mul_norm_le : ‖ContinuousLinearMap.mul ℂ ℂ‖ ≤ (1 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using ContinuousLinearMap.opNorm_mul_apply_le ℂ ℂ x

/-- Pointwise multiplication into `l1` for conjugate exponents. -/
def holderProduct : Coeff p →L[ℂ] Coeff q →L[ℂ] Coeff 1 :=
  lp.holderL (p := p) (q := q) 1 (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
    (K := 1) (fun _ => complex_mul_norm_le)

theorem norm_holderProduct_le : ‖holderProduct (p := p) (q := q)‖ ≤ 1 :=
  lp.norm_holderL_le 1 (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
    (K := 1) (fun _ => complex_mul_norm_le)

/-- The reciprocal weight bundled in its conjugate sequence space. -/
def inverseWeight (w : Weight) (hw : Memℓp (fun n => (w n : ℂ)⁻¹) q) : Coeff q :=
  ⟨fun n => (w n : ℂ)⁻¹, hw⟩

/-- Forgetting the weight as a continuous map into absolutely summable coefficients. -/
def toL1CLM (w : Weight) (hw : Memℓp (fun n => (w n : ℂ)⁻¹) q) :
    WeightedCoeff w p →L[ℂ] Coeff 1 :=
  ((holderProduct (p := p) (q := q)).flip (inverseWeight w hw)).comp
    (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem toL1CLM_apply (w : Weight) (hw : Memℓp (fun n => (w n : ℂ)⁻¹) q)
    (a : WeightedCoeff w p) (n : ℤ) : toL1CLM w hw a n = a.val n := by
  change (w n : ℂ) * a.val n * (w n : ℂ)⁻¹ = a.val n
  simp [mul_comm, w.complex_ne_zero]

/-- Quantitative weighted Hölder embedding. -/
theorem norm_toL1CLM_le (w : Weight) (hw : Memℓp (fun n => (w n : ℂ)⁻¹) q)
    (a : WeightedCoeff w p) : ‖toL1CLM w hw a‖ ≤ ‖inverseWeight w hw‖ * ‖a‖ := by
  change ‖holderProduct (weightEquiv w p a) (inverseWeight w hw)‖ ≤ _
  calc
    _ ≤ ‖holderProduct (p := p) (q := q)‖ * ‖weightEquiv w p a‖ * ‖inverseWeight w hw‖ :=
      (holderProduct (p := p) (q := q)).le_opNorm₂ _ _
    _ ≤ 1 * ‖weightEquiv w p a‖ * ‖inverseWeight w hw‖ := by
      gcongr
      exact norm_holderProduct_le
    _ = ‖inverseWeight w hw‖ * ‖a‖ := by
      rw [one_mul, ← norm_eq, mul_comm]

/-- The weighted-to-`l1` map does not identify distinct coefficients. -/
theorem toL1CLM_injective (w : Weight) (hw : Memℓp (fun n => (w n : ℂ)⁻¹) q) :
    Function.Injective (toL1CLM (p := p) w hw) := by
  intro a b hab
  apply Subtype.ext
  funext n
  simpa only [toL1CLM_apply] using congrArg (fun x : Coeff 1 => x n) hab

end NLS.WeightedCoeff
