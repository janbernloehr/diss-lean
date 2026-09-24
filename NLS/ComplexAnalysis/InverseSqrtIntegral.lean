import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Integrability under a square-root endpoint bound

A measurable complex function on `(0, ε)` whose product with `√y`
is bounded is integrable at zero. This is the local model for the
critical-root quotient at a noncollapsed gap endpoint.
-/

noncomputable section
open Set MeasureTheory
namespace NLS.ComplexAnalysis

/-- The inverse-square-root endpoint growth allowed by a simple
spectral branch point is locally integrable. -/
theorem integrableOn_Ioo_of_norm_mul_sqrt_le
    {f : ℝ → ℂ} {ε M : ℝ} (hε : 0 < ε)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioo 0 ε)))
    (hbound : ∀ y ∈ Ioo (0:ℝ) ε,
      ‖f y * (Real.sqrt y : ℂ)‖ ≤ M) :
    IntegrableOn f (Ioo (0:ℝ) ε) := by
  have hpow : IntegrableOn (fun y : ℝ => M * y ^ (-1/2 : ℝ))
      (Ioo (0:ℝ) ε) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hε).2
      (by norm_num : -1 < (-1/2 : ℝ))).const_mul M
  refine Integrable.mono' hpow hfm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have hypos : 0 < y := hy.1
  have hsqrt : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hweight : Real.sqrt y * y ^ (-1/2 : ℝ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hypos]
    norm_num
  have hbound' : ‖f y‖ * Real.sqrt y ≤ M := by
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsqrt.le] using hbound y hy
  have hM : 0 ≤ M :=
    (mul_nonneg (norm_nonneg _) hsqrt.le).trans hbound'
  have hnorm : ‖f y‖ ≤ M * y ^ (-1/2 : ℝ) := by
    calc
      ‖f y‖ = (‖f y‖ * Real.sqrt y) * y ^ (-1/2 : ℝ) := by
        rw [mul_assoc, hweight, mul_one]
      _ ≤ M * y ^ (-1/2 : ℝ) :=
        mul_le_mul_of_nonneg_right hbound' (Real.rpow_nonneg hypos.le _)
  simpa [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg hM (Real.rpow_nonneg hypos.le _))] using hnorm

/-- A positive scaling of the square-root weight does not change
integrability at the endpoint. -/
theorem integrableOn_Ioo_of_norm_mul_sqrt_mul_le
    {f : ℝ → ℂ} {d ε M : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioo 0 ε)))
    (hbound : ∀ y ∈ Ioo (0:ℝ) ε,
      ‖f y * (Real.sqrt (d*y) : ℂ)‖ ≤ M) :
    IntegrableOn f (Ioo (0:ℝ) ε) := by
  apply integrableOn_Ioo_of_norm_mul_sqrt_le hε hfm
  intro y hy
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hsq : Real.sqrt (d*y) = Real.sqrt d * Real.sqrt y :=
    Real.sqrt_mul hd.le _
  have hb := hbound y hy
  rw [hsq] at hb
  have hnorm : ‖f y * (Real.sqrt y : ℂ)‖ * Real.sqrt d ≤ M := by
    calc
      _ = ‖f y * ((Real.sqrt d * Real.sqrt y : ℝ) : ℂ)‖ := by
        simp [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_comm, mul_left_comm]
      _ ≤ M := hb
  exact (le_div_iff₀ hsd).2 hnorm

end NLS.ComplexAnalysis
