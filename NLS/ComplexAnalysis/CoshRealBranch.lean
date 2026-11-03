import NLS.ComplexAnalysis.ContinuousLogarithmUnique

/-! # A continuous cosh branch anchored on the nonnegative real axis

Equal hyperbolic cosines and nonnegative real parts give the same
exponential. Connectedness and one common value then fix its logarithm.
No unproved principal-logarithm or imaginary-period choice is supplied.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.ComplexAnalysis

theorem exp_eq_of_cosh_eq_real_nonneg (w : ℂ) (t : ℝ)
    (hw : 0 ≤ w.re) (ht : 0 ≤ t) (hc : cosh w = cosh (t : ℂ)) :
    exp w = exp (t : ℂ) := by
  have hs := congrArg (fun z : ℂ => 2*z) hc
  rw [two_cosh,two_cosh] at hs
  have hwprod : exp w*exp (-w) = 1 := by rw [← exp_add,add_neg_cancel,exp_zero]
  have htprod : exp (t : ℂ)*exp (-(t : ℂ)) = 1 := by rw [← exp_add,add_neg_cancel,exp_zero]
  have hprod : (exp w-exp (t : ℂ))*(exp w-exp (-(t : ℂ))) = 0 := by
    linear_combination exp w*hs-hwprod+htprod
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · have he := sub_eq_zero.mp h
    have hn := congrArg norm he
    rw [norm_exp,norm_exp,neg_re,ofReal_re] at hn
    have hre : w.re = -t := Real.exp_injective hn
    have ht0 : t = 0 := by linarith
    simpa only [ht0,ofReal_zero,neg_zero] using he

theorem continuous_cosh_real_branch_eqOn
    {X : Type*} [TopologicalSpace X] (F : X → ℂ) (G : X → ℝ) (S : Set X)
    (hS : IsPreconnected S) (hF : ContinuousOn F S) (hG : ContinuousOn G S)
    (hFr : ∀ x ∈ S, 0 ≤ (F x).re) (hGr : ∀ x ∈ S, 0 ≤ G x)
    (hcosh : ∀ x ∈ S, cosh (F x) = cosh (G x : ℂ))
    (a : X) (ha : a ∈ S) (he : F a = (G a : ℂ)) :
    EqOn F (fun x => (G x : ℂ)) S := by
  apply continuousLogarithms_eqOn F (fun x => (G x : ℂ)) S hS hF
    (continuous_ofReal.comp_continuousOn hG) ?_ a ha he
  intro x hx
  exact exp_eq_of_cosh_eq_real_nonneg (F x) (G x) (hFr x hx) (hGr x hx) (hcosh x hx)

end NLS.ComplexAnalysis
