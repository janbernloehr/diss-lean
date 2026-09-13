import NLS.ComplexAnalysis.AnalyticScalarJetOrder
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Algebra of convergent scalar Taylor coefficients

The derivative product rule identifies multiplication of convergent Taylor
coefficients with ordinary formal convolution. Addition and subtraction
already act coefficientwise.
-/

noncomputable section
open Complex PowerSeries
namespace NLS.ComplexAnalysis

/-- The ordinary Taylor coefficient times its factorial is the spectral derivative. -/
theorem factorial_mul_coeff_scalarFormalTaylor {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {z : ℂ} (hf : HasFPowerSeriesAt f p z) (n : ℕ) :
    (n.factorial : ℂ)*PowerSeries.coeff n (scalarFormalTaylor p) = iteratedDeriv n f z := by
  obtain ⟨r,hr⟩ := hf
  rw [coeff_scalarFormalTaylor,iteratedDeriv_eq_iteratedFDeriv]
  simpa only [nsmul_eq_mul] using hr.factorial_smul (1 : ℂ) n

/-- Formal extraction respects addition of scalar multilinear series. -/
@[simp] theorem scalarFormalTaylor_add (p q : FormalMultilinearSeries ℂ ℂ ℂ) :
    scalarFormalTaylor (p+q) = scalarFormalTaylor p+scalarFormalTaylor q := by
  ext n
  simp [scalarFormalTaylor]

/-- Formal extraction respects subtraction of scalar multilinear series. -/
@[simp] theorem scalarFormalTaylor_sub (p q : FormalMultilinearSeries ℂ ℂ ℂ) :
    scalarFormalTaylor (p-q) = scalarFormalTaylor p-scalarFormalTaylor q := by
  ext n
  simp [scalarFormalTaylor]

/-- Taylor coefficients of a product are the formal convolution of the two factor series. -/
theorem scalarFormalTaylor_mul {f g : ℂ → ℂ}
    {p q s : FormalMultilinearSeries ℂ ℂ ℂ} {z : ℂ}
    (hf : HasFPowerSeriesAt f p z) (hg : HasFPowerSeriesAt g q z)
    (hfg : HasFPowerSeriesAt (fun w => f w*g w) s z) :
    scalarFormalTaylor s = scalarFormalTaylor p*scalarFormalTaylor q := by
  ext n
  apply mul_left_cancel₀ (show (n.factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero n)
  rw [factorial_mul_coeff_scalarFormalTaylor hfg,
    iteratedDeriv_fun_mul hf.analyticAt.contDiffAt hg.analyticAt.contDiffAt,
    PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← factorial_mul_coeff_scalarFormalTaylor hf i,
    ← factorial_mul_coeff_scalarFormalTaylor hg (n-i)]
  have hc : (n.choose i : ℂ)*(i.factorial : ℂ)*((n-i).factorial : ℂ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  calc
    _ = ((n.choose i : ℂ)*(i.factorial : ℂ)*((n-i).factorial : ℂ))*
        (PowerSeries.coeff i (scalarFormalTaylor p)*PowerSeries.coeff (n-i) (scalarFormalTaylor q)) := by ring
    _ = _ := by rw [hc]

end NLS.ComplexAnalysis
