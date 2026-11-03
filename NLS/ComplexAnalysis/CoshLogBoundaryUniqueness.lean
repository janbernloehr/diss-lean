import NLS.ComplexAnalysis.ContinuousLogarithmUnique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Physical cosh sheets and boundary-normalized logarithm uniqueness

Positive real parts select the same exponential over a common cosh value.
A common finite boundary limit then fixes the full logarithm period on a
connected domain, without choosing a principal logarithm.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis

theorem exp_eq_of_cosh_eq_of_re_pos (z w : ℂ) (hz : 0 < z.re) (hw : 0 < w.re)
    (hc : cosh z = cosh w) : exp z = exp w := by
  have hs : sinh z^2 = sinh w^2 := by
    have h₁ := cosh_sq_sub_sinh_sq z
    have h₂ := cosh_sq_sub_sinh_sq w
    rw [hc] at h₁
    linear_combination h₂-h₁
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with he | he
  · rw [← cosh_add_sinh z,← cosh_add_sinh w,hc,he]
  · have hexp : exp z = exp (-w) := by
      rw [← cosh_add_sinh z,← cosh_add_sinh (-w),cosh_neg,sinh_neg,hc,he]
    have hn := congrArg norm hexp
    rw [norm_exp,norm_exp,neg_re] at hn
    have hre := Real.exp_injective hn
    linarith

theorem continuousLogarithms_eqOn_of_common_boundary_limit
    {X : Type*} [TopologicalSpace X] (F G : X → ℂ) (S : Set X)
    (hS : IsPreconnected S) (hF : ContinuousOn F S) (hG : ContinuousOn G S)
    (hexp : ∀ x ∈ S, exp (F x) = exp (G x))
    (a : X) (ha : a ∈ S) (c : X) (L : ℂ) [NeBot (𝓝[S] c)]
    (hFlim : Tendsto F (𝓝[S] c) (𝓝 L)) (hGlim : Tendsto G (𝓝[S] c) (𝓝 L)) :
    EqOn F G S := by
  let K := F a-G a
  let H : X → ℂ := fun x => G x+K
  have heK : exp K = 1 := by
    rw [exp_sub,hexp a ha,div_self (exp_ne_zero _)]
  have heq : EqOn F H S := continuousLogarithms_eqOn F H S hS hF (hG.add_const K)
    (by intro x hx; simpa only [H,exp_add,heK,mul_one] using hexp x hx)
    a ha (by dsimp only [H,K]; ring)
  have hlimH : Tendsto H (𝓝[S] c) (𝓝 L) := by
    apply hFlim.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact heq hx
  have heL : L+K = L := tendsto_nhds_unique (hGlim.add_const K) hlimH
  have hK : K = 0 := by
    apply add_left_cancel (a := L)
    simpa only [add_zero] using heL
  intro x hx
  simpa only [H,hK,add_zero] using heq hx

end NLS.ComplexAnalysis
