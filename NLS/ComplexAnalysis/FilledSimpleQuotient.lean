import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic.FieldSimp

/-! # Filling a quotient at simple zeros of its denominator

The derivative ratio gives the removable value when both functions vanish
and the denominator has a simple zero.
-/
noncomputable section
open Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- The ordinary quotient, with its derivative ratio at denominator zeros. -/
def filledSimpleQuotient (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if g z = 0 then deriv f z / deriv g z else f z / g z

theorem filledSimpleQuotient_eq_div {f g : ℂ → ℂ} {z : ℂ} (hg : g z ≠ 0) :
    filledSimpleQuotient f g z = f z / g z := by
  simp only [filledSimpleQuotient, if_neg hg]

/-- Analyticity at a common zero whose denominator derivative is nonzero. -/
theorem analyticAt_filledSimpleQuotient_of_simple_zero
    {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hf0 : f z = 0) (hg0 : g z = 0) (hg1 : deriv g z ≠ 0) :
    AnalyticAt ℂ (filledSimpleQuotient f g) z := by
  obtain ⟨pf, hpf⟩ := hf
  obtain ⟨pg, hpg⟩ := hg
  have hdf : AnalyticAt ℂ (dslope f z) z :=
    ⟨_, hpf.has_fpower_series_dslope_fslope⟩
  have hdg : AnalyticAt ℂ (dslope g z) z :=
    ⟨_, hpg.has_fpower_series_dslope_fslope⟩
  have hdz : dslope g z z ≠ 0 := by simpa only [dslope_same] using hg1
  apply (hdf.div hdg hdz).congr
  filter_upwards [hdg.continuousAt.eventually_ne hdz] with w hw
  change dslope f z w / dslope g z w = filledSimpleQuotient f g w
  by_cases hwz : w = z
  · subst w
    simp only [filledSimpleQuotient, hg0, if_pos, dslope_same]
  · have hgw : g w ≠ 0 := by
      have he := sub_smul_dslope_of_zero hg0 w
      rw [smul_eq_mul] at he
      rw [← he]
      exact mul_ne_zero (sub_ne_zero.mpr hwz) hw
    rw [filledSimpleQuotient_eq_div hgw]
    simp only [dslope_of_ne _ hwz, slope, hf0, hg0, vsub_eq_sub, sub_zero, smul_eq_mul]
    field_simp

/-- Filling preserves analyticity wherever denominator zeros are simple and
are also numerator zeros. -/
theorem analyticAt_filledSimpleQuotient
    {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hzero : g z = 0 → f z = 0 ∧ deriv g z ≠ 0) :
    AnalyticAt ℂ (filledSimpleQuotient f g) z := by
  by_cases hz : g z = 0
  · exact analyticAt_filledSimpleQuotient_of_simple_zero hf hg (hzero hz).1 hz (hzero hz).2
  · apply (hf.div hg hz).congr
    filter_upwards [hg.continuousAt.eventually_ne hz] with w hw
    exact (filledSimpleQuotient_eq_div hw).symm

/-- Filling the quotient preserves the exact factor identity. -/
theorem filledSimpleQuotient_mul (f g : ℂ → ℂ) (z : ℂ)
    (hzero : g z = 0 → f z = 0) : filledSimpleQuotient f g z*g z = f z := by
  by_cases hg : g z = 0
  · rw [hg,hzero hg,mul_zero]
  · rw [filledSimpleQuotient_eq_div hg]
    exact div_mul_cancel₀ (f z) hg

/-- At a common simple zero the filled quotient is nonzero. -/
theorem filledSimpleQuotient_ne_zero_of_simple_zeros (f g : ℂ → ℂ) (z : ℂ)
    (hg : g z = 0) (hdf : deriv f z ≠ 0) (hdg : deriv g z ≠ 0) :
    filledSimpleQuotient f g z ≠ 0 := by
  simp only [filledSimpleQuotient,hg,ite_true]
  exact div_ne_zero hdf hdg

end NLS.ComplexAnalysis
