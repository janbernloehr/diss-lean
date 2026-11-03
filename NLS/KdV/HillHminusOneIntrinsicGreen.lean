import NLS.KdV.HillHminusOneIntrinsicWeakForm
import NLS.KdV.HillHminusOneWeakEquation

/-! # Intrinsic Green identity on every admissible H1 test pair -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

theorem HillHminusMiuraChart.intrinsic_green_identity
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (lambda : ℂ) (v : ℂ × ℂ) (φ : Curve ℂ)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend (C.physicalPosition q lambda v) 1*extend φ 1 =
      extend (C.physicalPosition q lambda v) 0*extend φ 0) :
    hillHminusWeakForm q (C.physicalPosition q lambda v) φ =
      extend (C.physicalMomentum q lambda v) 1*extend φ 1-
        extend (C.physicalMomentum q lambda v) 0*extend φ 0+
        lambda*(∫ s in (0 : ℝ)..1, extend (C.physicalPosition q lambda v) s*extend φ s) := by
  have hy := C.physicalSolution_scalar_H1 q lambda v
  rw [hillHminusWeakForm_eq_chart C q hq _ φ hy.1 hφ hy.2.1 hφ₂ hend]
  exact C.physicalSolution_weak_green_identity q lambda v φ hφ hφ₂

end NLS.KdV
