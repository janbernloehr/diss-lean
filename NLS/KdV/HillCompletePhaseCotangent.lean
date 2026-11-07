import NLS.KdV.HillCompletePhaseSquare
import NLS.ComplexAnalysis.ExponentialLogDifferential

/-! The actual full Abelian angle differential is a single-valued
analytic native cotangent on the original open selected-gap locus.
Every actual local phase chart has precisely this full differential. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

def hillHminusCompletePhaseCotangent (n : ℕ+) (q : PeriodOneHminusOne) :
    PeriodOneHminusOne →L[ℂ] ℂ :=
  (2*I*hillHminusCompletePhaseSquare n q)⁻¹ • fderiv ℂ (hillHminusCompletePhaseSquare n) q

theorem analyticOnNhd_hillHminusCompletePhaseCotangent (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCompletePhaseCotangent n) (hillHminusCompletePhaseDomain n) := by
  have hP := analyticOnNhd_hillHminusCompletePhaseSquare n
  intro q hq
  exact ((analyticAt_const.mul (hP q hq)).inv
    (mul_ne_zero (by simp) (hillHminusCompletePhaseSquare_ne_zero n q hq))).smul (hP.fderiv q hq)

namespace HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

theorem eventually_completePhaseCotangent_eq_fderiv (C : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    hillHminusCompletePhaseCotangent n =ᶠ[𝓝 q] fderiv ℂ C.completePhase := by
  have he := C.eventually_completePhaseSquare_eq_exp q hq hr
  filter_upwards [eventually_eventually_nhds.mpr he,C.source_open.mem_nhds hq,
    isOpen_hillHminusOffIndexAnalyticDomain.mem_nhds (real_mem_hillHminusOffIndexAnalyticDomain q hr)] with p hp hC hOff
  exact logarithmic_fderiv_of_exp_germ (hillHminusCompletePhaseSquare n) C.completePhase p (2*I)
    (by simp) (C.analytic_completePhase p ⟨hC,hOff⟩) hp

theorem completePhaseCotangent_eq_fderiv_of_real (C : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    hillHminusCompletePhaseCotangent n q=fderiv ℂ C.completePhase q :=
  (C.eventually_completePhaseCotangent_eq_fderiv q hq hr).eq_of_nhds

end HillPhysicalOnIndexPhaseChart
end NLS.KdV
