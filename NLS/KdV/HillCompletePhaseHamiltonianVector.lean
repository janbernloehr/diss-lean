import NLS.KdV.HillCompletePhaseReality
import NLS.KdV.HillCompletePhaseActionKronecker
import NLS.Poisson.GardnerRealForm

/-! The actual complete phase Hamiltonian vector is real, has mean
zero, and gives unit selected action velocity with the actual sign. -/
noncomputable section
open Set Complex Filter Topology NLS.Poisson
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

theorem completePhase_HamiltonianVector_real (A : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ A.source) (hr : IsRealPeriodOneHminusOne q) :
    IsRealPeriodOneHminusOne (gardnerHamiltonianVector A.completePhase q) := by
  apply gardnerHamiltonianVector_real_of_eventually_real A.completePhase q hr
    (A.analytic_completePhase q ⟨hq,real_mem_hillHminusOffIndexAnalyticDomain q hr⟩)
  filter_upwards [A.source_open.mem_nhds hq] with a ha har
  exact A.completePhase_im_eq_zero_of_real a ha har

theorem completePhase_HamiltonianVector_zero_mode (A : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) : (gardnerHamiltonianVector A.completePhase q).val 0=0 := by
  rw [gardnerHamiltonianVector_apply]
  simp

theorem completePhase_HamiltonianVector_action_velocity (A : HillPhysicalOnIndexPhaseChart P n)
    (k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ A.source) (hr : IsRealPeriodOneHminusOne q) :
    (fderiv ℂ (hillHminusCanonicalAction k) q) (gardnerHamiltonianVector A.completePhase q)=
      if k=n then (1:ℂ) else 0 := by
  rw [fderiv_apply_gardnerHamiltonianVector]
  exact A.action_completePhase_Gardner_of_real k q hq hr

end NLS.KdV.HillPhysicalOnIndexPhaseChart
