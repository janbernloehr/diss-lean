import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Analytic orders of finite spectral polynomials

Orders are computed in the extended naturals before passing to natural
multiplicities. This retains the distinction between finite order and
identical vanishing.
-/

noncomputable section
namespace NLS.ComplexAnalysis

/-- A nonzero constant normalization does not change analytic order. -/
theorem analyticOrderAt_div_const (f : ℂ → ℂ) (z c : ℂ) (hc : c ≠ 0) (hf : AnalyticAt ℂ f z) :
    analyticOrderAt (fun t => f t/c) z = analyticOrderAt f z := by
  have hconst : analyticOrderAt (fun _ : ℂ => c⁻¹) z = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (inv_ne_zero hc))
  change analyticOrderAt (f * fun _ => c⁻¹) z = _
  rw [analyticOrderAt_mul hf analyticAt_const, hconst, add_zero]

/-- A finite product's extended analytic order is the sum of its factor orders. -/
theorem analyticOrderAt_finsetProd {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) z) :
    analyticOrderAt (fun t => ∏ i ∈ s, f i t) z = ∑ i ∈ s, analyticOrderAt (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [analyticOrderAt_eq_zero]
  | @insert i s hi ih =>
    have hprod : AnalyticAt ℂ (fun t => ∏ j ∈ s, f j t) z :=
      s.analyticAt_fun_prod (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    rw [show (fun t => ∏ j ∈ insert i s, f j t) = f i * (fun t => ∏ j ∈ s, f j t) from
      funext (fun t => Finset.prod_insert hi)]
    rw [analyticOrderAt_mul (hf i (Finset.mem_insert_self _ _)) hprod, ih
      (fun j hj => hf j (Finset.mem_insert_of_mem hj)), Finset.sum_insert hi]

/-- A linear root factor has order one precisely at its root. -/
theorem analyticOrderAt_const_sub (a z : ℂ) :
    analyticOrderAt (fun t => a-t) z = if a = z then 1 else 0 := by
  classical
  rw [show (fun t => a-t) = -(fun t => t-a) from funext (fun _ => by simp)]
  rw [analyticOrderAt_neg]
  by_cases h : a = z
  · subst a
    simp
  · simp [h, analyticOrderAt_id_sub_const_of_ne (Ne.symm h)]

/-- A finite polynomial with explicit root multiplicities has exactly those analytic orders. -/
theorem analyticOrderAt_rootPolynomial (s : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) :
    analyticOrderAt (fun t => ∏ a ∈ s, (a-t)^(m a)) z =
      if z ∈ s then (m z : ℕ∞) else 0 := by
  classical
  rw [analyticOrderAt_finsetProd s _ z (fun _ _ => by fun_prop)]
  have he (a : ℂ) : analyticOrderAt (fun t => (a-t)^(m a)) z = if a = z then (m a : ℕ∞) else 0 := by
    rw [show (fun t => (a-t)^(m a)) = (fun t => a-t)^(m a) by rfl,
      analyticOrderAt_pow (by fun_prop), analyticOrderAt_const_sub]
    split_ifs <;> simp
  simp_rw [he]
  simp

end NLS.ComplexAnalysis
