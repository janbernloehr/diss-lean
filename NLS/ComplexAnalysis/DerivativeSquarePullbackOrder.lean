import NLS.ComplexAnalysis.AnalyticSquarePullback

/-! # Exact zero order of a derivative pulled back through the square energy map. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ComplexAnalysis

theorem analyticOrderNatAt_linear_mul_comp_sq_zero (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (hfin : analyticOrderAt f 0 ≠ ⊤) :
    analyticOrderNatAt (fun z : ℂ => 2*z*f (z^2)) 0 = 1+2*analyticOrderNatAt f 0 := by
  have hsq : AnalyticAt ℂ (fun z : ℂ => z^2) 0 := analyticAt_id.pow 2
  have hf' : AnalyticAt ℂ f ((0 : ℂ)^2) := by simpa using hf
  have hcomp := hf'.comp (f := fun z : ℂ => z^2) hsq
  have hp : analyticOrderAt ((id : ℂ → ℂ)^2) 0 = 2 := by
    rw [analyticOrderAt_pow (show AnalyticAt ℂ (id : ℂ → ℂ) 0 from analyticAt_id) 2,analyticOrderAt_id]
    norm_num
  have hc := hf'.analyticOrderAt_comp hsq
  simp only [Function.comp_def,zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero] at hc
  change analyticOrderAt (fun z : ℂ => f (z^2)) 0 = analyticOrderAt f 0*analyticOrderAt ((id : ℂ → ℂ)^2) 0 at hc
  have hcf : analyticOrderAt (fun z : ℂ => f (z^2)) 0 ≠ ⊤ := by
    rw [hc,hp]
    obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hm,show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) from rfl,← ENat.natCast_mul]
    exact ENat.natCast_ne_top _
  have hl : analyticOrderAt (fun z : ℂ => 2*z) 0 = 1 := by
    apply (analyticAt_const.mul analyticAt_id).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    · simp
    · norm_num [deriv_const_mul_field]
  have h := analyticOrderNatAt_mul (analyticAt_const.mul analyticAt_id : AnalyticAt ℂ (fun z : ℂ => 2*z) 0)
    hcomp (by change analyticOrderAt (fun z : ℂ => 2*z) 0 ≠ ⊤; rw [hl]; norm_num) hcf
  change analyticOrderNatAt (fun z : ℂ => 2*z*f (z^2)) 0 =
    analyticOrderNatAt (fun z : ℂ => 2*z) 0+analyticOrderNatAt (fun z : ℂ => f (z^2)) 0 at h
  have hlNat : analyticOrderNatAt (fun z : ℂ => 2*z) 0 = 1 := by
    simp only [analyticOrderNatAt,hl,ENat.toNat_one]
  rw [h,hlNat,analyticOrderNatAt_comp_sq_zero f hf]


end NLS.ComplexAnalysis
