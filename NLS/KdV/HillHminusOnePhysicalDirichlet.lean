import NLS.KdV.HillHminusOneDirichlet
import NLS.KdV.HillHminusOneWeakEquation
import NLS.MKdV.L2QuasiHillEnergyAgreement

/-! # The entire H^-1 Dirichlet characteristic is the actual normalized IVP

The shared analytic characteristic equals the terminal position of the
actual rough solution with initial position zero and quasi-derivative
one, in every shifted-Miura chart and at every complex energy.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

theorem HillHminusMiuraChart.hillHminusDirichlet_eq_physicalPosition
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (lambda : ℂ) :
    hillHminusDirichlet q lambda = extend (C.physicalPosition q lambda (0,1)) 1 := by
  rw [hillHminusDirichlet_eq_chart C q hq]
  change quasiHillL2Dirichlet (C.lift q) (lambda+C.energyShift) = _
  rw [quasiHillL2Dirichlet_eq_physical]
  exact (extend_coe (C.physicalPosition q lambda (0,1))
    ⟨1,by constructor <;> norm_num⟩).symm

end NLS.KdV
