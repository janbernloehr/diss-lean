import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic

/-! # The cubic norm remainder after an analytic quadratic Taylor polynomial -/
noncomputable section
set_option autoImplicit false
open Filter Topology Asymptotics
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analytic_quadratic_remainder (f : E → ℂ) (hf : AnalyticAt ℂ f 0) :
    (fun a => f a-f 0-fderiv ℂ f 0 a-(1/2 : ℂ)*fderiv ℂ (fderiv ℂ f) 0 a a)
      =O[𝓝 0] (fun a => ‖a‖^3) := by
  obtain ⟨p,r,hp⟩ := hf
  have hrem := hp.hasFPowerSeriesAt.isBigO_sub_partialSum_pow 3
  have hpoly (a : E) : p.partialSum 3 a=
      f 0+fderiv ℂ f 0 a+(1/2 : ℂ)*fderiv ℂ (fderiv ℂ f) 0 a a := by
    have h0 := hp.factorial_smul a 0
    have h1 := hp.factorial_smul a 1
    have h2 := hp.factorial_smul a 2
    simp only [Nat.factorial_zero,one_smul,iteratedFDeriv_zero_apply] at h0
    simp only [Nat.factorial_one,one_smul,iteratedFDeriv_one_apply] at h1
    norm_num [Nat.factorial,iteratedFDeriv_two_apply,nsmul_eq_mul] at h2
    have h2' : p 2 (fun _ => a)=(1/2 : ℂ)*fderiv ℂ (fderiv ℂ f) 0 a a := by
      linear_combination (1/2 : ℂ)*h2
    simp only [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,
      Finset.sum_range_zero,zero_add,h0,h1,h2']
  apply hrem.congr_left
  intro a
  rw [zero_add,hpoly]
  ring

end NLS.ComplexAnalysis
