import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-! # The analytic-order doubling under the square map at zero. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
theorem analyticOrderNatAt_comp_sq_zero (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    analyticOrderNatAt (fun z : ℂ => f (z^2)) 0 = 2*analyticOrderNatAt f 0 := by
  have hf' : AnalyticAt ℂ f ((0 : ℂ)^2) := by simpa using hf
  have he := hf'.analyticOrderAt_comp (analyticAt_id.pow 2 : AnalyticAt ℂ (fun z : ℂ => z^2) 0)
  have hp : analyticOrderAt ((id : ℂ → ℂ)^2) 0 = 2 := by
    rw [analyticOrderAt_pow (show AnalyticAt ℂ (id : ℂ → ℂ) 0 from analyticAt_id) 2,analyticOrderAt_id]
    norm_num
  simp only [Function.comp_def,Pi.pow_apply,id_eq,zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero] at he
  change analyticOrderAt (fun z : ℂ => f (z^2)) 0 = analyticOrderAt f 0*analyticOrderAt ((id : ℂ → ℂ)^2) 0 at he
  rw [hp] at he
  have hn := congrArg ENat.toNat he
  simpa only [analyticOrderNatAt,ENat.toNat_mul,ENat.toNat_ofNat,mul_comm] using hn

end NLS.ComplexAnalysis
