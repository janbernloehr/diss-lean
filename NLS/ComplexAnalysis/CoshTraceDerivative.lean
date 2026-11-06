import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.LinearCombination

/-! # The derivative of a parity-normalized trace primitive -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem hasDerivAt_of_cosh_trace (F D : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hF : AnalyticOnNhd ℂ F U) (hD : AnalyticOnNhd ℂ D U) (s : ℂ) (hs : s^2 = 1)
    (he : ∀ z ∈ U, 2*cosh (F z) = s*D z)
    (z : ℂ) (hz : z ∈ U) (hne : 2*s*sinh (F z) ≠ 0) :
    HasDerivAt F (deriv D z/(2*s*sinh (F z))) z := by
  have hleft := ((Complex.hasDerivAt_cosh (F z)).comp z
    (hF z hz).differentiableAt.hasDerivAt).const_mul 2
  have hright := (hD z hz).differentiableAt.hasDerivAt.const_mul s
  have hnear : (fun w => 2*cosh (F w)) =ᶠ[𝓝 z] (fun w => s*D w) :=
    Filter.eventually_of_mem (hU.mem_nhds hz) (fun w hw => he w hw)
  have hd := (hleft.congr_of_eventuallyEq hnear.symm).unique hright
  apply (hF z hz).differentiableAt.hasDerivAt.congr_deriv
  apply (eq_div_iff hne).mpr
  linear_combination s*hd+deriv D z*hs

end NLS.ComplexAnalysis
