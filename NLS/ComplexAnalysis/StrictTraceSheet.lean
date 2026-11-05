import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith

/-! # Strict half-plane normalization of a nonconstant trace primitive

A nonnegative real part of an analytic primitive is strictly positive
when its hyperbolic cosine is a nonconstant entire trace. Maximum modulus
excludes contact with the imaginary axis without assuming a spectral sign.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem re_pos_of_nonneg_of_nonconstant_cosh_trace
    (f g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g univ)
    (htrace : ∀ z ∈ U, 2*cosh (f z) = g z)
    (hnonconstant : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c)
    (hnonneg : ∀ z ∈ U, 0 ≤ (f z).re) (z : ℂ) (hz : z ∈ U) :
    0 < (f z).re := by
  by_contra hpos
  have hz0 : (f z).re = 0 := le_antisymm (not_lt.mp hpos) (hnonneg z hz)
  let E : ℂ → ℂ := fun w => exp (-f w)
  have hE : AnalyticAt ℂ E z := (hf z hz).neg.cexp
  have hmax : IsLocalMax (norm ∘ E) z := by
    change ∀ᶠ w in 𝓝 z, ‖E w‖ ≤ ‖E z‖
    filter_upwards [hU.mem_nhds hz] with w hw
    simp only [E, norm_exp, neg_re, hz0, neg_zero, Real.exp_zero]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hnonneg w hw))
  have he := Complex.eventually_eq_of_isLocalMax_norm
    (hE.eventually_analyticAt.mono (fun _ hw => hw.differentiableAt)) hmax
  have hnear : g =ᶠ[𝓝 z] (fun _ => g z) := by
    filter_upwards [he,hU.mem_nhds hz] with w hw hwU
    have hplus : exp (f w) = exp (f z) := by
      have hinv := congrArg (fun v : ℂ => v⁻¹) hw
      simpa only [E,exp_neg,inv_inv] using hinv
    rw [← htrace w hwU, ← htrace z hz]
    simp only [cosh,hplus]
    change 2*((exp (f z)+E w)/2) = 2*((exp (f z)+E z)/2)
    rw [hw]
  apply hnonconstant
  refine ⟨g z,fun w => ?_⟩
  exact hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    isPreconnected_univ (mem_univ z) hnear (mem_univ w)

end NLS.ComplexAnalysis
