import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # A globally square-integrable function cannot have a growing exponential tail -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Complex
namespace NLS.FunctionalAnalysis

/-- A constant norm lower bound on a set of infinite measure must vanish for an L2 function. -/
theorem eq_zero_of_memLp_of_norm_le_on_infinite_set (y : ℝ → ℂ)
    (hy : MemLp y 2 volume) (c : ℂ) (S : Set ℝ) (hS : MeasurableSet S)
    (hvol : volume S = ⊤) (hb : ∀ t ∈ S, ‖c‖ ≤ ‖y t‖) : c = 0 := by
  have hi : Integrable (fun t => ‖y t‖^2) volume :=
    hy.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hc : IntegrableOn (fun _ : ℝ => ‖c‖^2) S volume := by
    apply hi.integrableOn.mono' aestronglyMeasurable_const
    rw [ae_restrict_iff' hS]
    exact Filter.Eventually.of_forall (fun t ht => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (‖c‖))] using
        pow_le_pow_left₀ (norm_nonneg c) (hb t ht) 2)
  have hz : ‖c‖^2 = 0 := by
    simpa [integrableOn_const_iff,hvol] using hc
  exact norm_eq_zero.mp ((sq_eq_zero_iff).mp hz)

/-- On the right half-line, a mode with nonnegative real exponent has zero coefficient. -/
theorem scalarL2_right_exponential_coefficient_eq_zero (α c : ℂ) (R : ℝ)
    (hα : 0 ≤ α.re) (y : ℝ → ℂ) (hy : MemLp y 2 volume)
    (he : ∀ t ∈ Ici R, y t = Complex.exp (α*((t-R : ℝ) : ℂ))*c) : c = 0 := by
  apply eq_zero_of_memLp_of_norm_le_on_infinite_set y hy c (Ici R)
    measurableSet_Ici Real.volume_Ici
  intro t ht
  rw [he t ht,norm_mul,Complex.norm_exp]
  have hexp : 1 ≤ Real.exp (α*((t-R : ℝ) : ℂ)).re := by
    apply Real.one_le_exp_iff.mpr
    simpa using mul_nonneg hα (sub_nonneg.mpr ht)
  simpa using mul_le_mul_of_nonneg_right hexp (norm_nonneg c)

/-- On the left half-line, a mode with nonpositive real exponent has zero coefficient. -/
theorem scalarL2_left_exponential_coefficient_eq_zero (α c : ℂ) (R : ℝ)
    (hα : α.re ≤ 0) (y : ℝ → ℂ) (hy : MemLp y 2 volume)
    (he : ∀ t ∈ Iic R, y t = Complex.exp (α*((t-R : ℝ) : ℂ))*c) : c = 0 := by
  apply eq_zero_of_memLp_of_norm_le_on_infinite_set y hy c (Iic R)
    measurableSet_Iic Real.volume_Iic
  intro t ht
  rw [he t ht,norm_mul,Complex.norm_exp]
  have hexp : 1 ≤ Real.exp (α*((t-R : ℝ) : ℂ)).re := by
    apply Real.one_le_exp_iff.mpr
    simpa using mul_nonneg_of_nonpos_of_nonpos hα (sub_nonpos.mpr ht)
  simpa using mul_le_mul_of_nonneg_right hexp (norm_nonneg c)

end NLS.FunctionalAnalysis
