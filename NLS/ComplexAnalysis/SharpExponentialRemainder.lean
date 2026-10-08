import NLS.ComplexAnalysis.QuadraticProductError
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Exponential remainders with the exact quadratic coefficient -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis

/-- The quadratic real exponential remainder retains the Taylor factor one half. -/
theorem exp_sub_one_sub_le_half_sq_mul_exp {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x-1-x ≤ x^2/2*Real.exp x := by
  let f : ℝ → ℝ := fun t => Real.exp (-t)*(1+t)-1+t^2/2
  have hd (t : ℝ) : HasDerivAt f (t*(1-Real.exp (-t))) t := by
    have h := (((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg).mul
      ((hasDerivAt_id t).const_add 1)).sub_const 1 |>.add ((hasDerivAt_id t).pow 2 |>.div_const 2)
    convert h using 1 <;> first | rfl | (dsimp; ring)
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht : t ∈ Ici (0:ℝ))
    have he : Real.exp (-t) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr ht0)
    exact mul_nonneg ht0 (sub_nonneg.mpr he)
  have hf : 0 ≤ f x := by simpa [f] using hm (by simp) hx hx
  have h := mul_nonneg hf (Real.exp_pos x).le
  have he : Real.exp (-x)*Real.exp x = 1 := by rw [← Real.exp_add]; simp
  dsimp [f] at h
  nlinarith

/-- The complex quadratic remainder has the same sharp factorial coefficient. -/
theorem norm_exp_sub_one_sub_le_half_sq_mul_exp (z : ℂ) :
    ‖Complex.exp z-1-z‖ ≤ ‖z‖^2/2*Real.exp ‖z‖ := by
  have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 2
  have he : (∑ m ∈ Finset.range 2, z^m/(m.factorial:ℂ)) = 1+z := by
    simp [Finset.sum_range_succ]
  have hr : (∑ m ∈ Finset.range 2, ‖z‖^m/(m.factorial:ℝ)) = 1+‖z‖ := by
    simp [Finset.sum_range_succ]
  rw [he, hr] at h
  simpa only [sub_add_eq_sub_sub] using h.trans (by
    simpa only [sub_add_eq_sub_sub] using exp_sub_one_sub_le_half_sq_mul_exp (norm_nonneg z))

/-- A global first-order exponential bound, without a smallness assumption. -/
theorem norm_exp_sub_one_le_norm_mul_exp (z : ℂ) :
    ‖Complex.exp z-1‖ ≤ ‖z‖*Real.exp ‖z‖ := by
  simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp z 1

/-- The weaker real exponential estimate in Remark D.2. -/
theorem exp_sub_one_le_mul_exp {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x-1 ≤ x*Real.exp x := by
  have h := norm_exp_sub_one_le_norm_mul_exp (x:ℂ)
  rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] at h
  exact (le_abs_self _).trans h

end NLS.ComplexAnalysis
