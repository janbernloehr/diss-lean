import NLS.KdV.HillHminusOnePhysicalQuasi
import NLS.MKdV.L2QuasiHillWeakEquation
import NLS.MKdV.L2QuasiHillScalarNontrivial

/-! # Actual scalar weak Hill equations in every H^-1 Miura chart

Position and quasi-derivative have H1 interval regularity. Their factored
Miura form has the literal energy lambda after the chart's constant shift
is subtracted. Reciprocal Floquet endpoints cancel the exact Green
boundary term. No endpoint value of the rough profile is used.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV.HillHminusMiuraChart

def physicalPosition (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (lambda : ℂ) (v : ℂ × ℂ) : Curve ℂ :=
  l2QuasiHillPosition (C.physicalProfile q) (lambda+C.energyShift) v

def physicalMomentum (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (lambda : ℂ) (v : ℂ × ℂ) : Curve ℂ :=
  l2QuasiHillMomentum (C.physicalProfile q) (lambda+C.energyShift) v

theorem physicalSolution_scalar_H1 (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (lambda : ℂ) (v : ℂ × ℂ) :
    AbsolutelyContinuousOnInterval (extend (C.physicalPosition q lambda v)) 0 1 ∧
      MemLp (deriv (extend (C.physicalPosition q lambda v))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      AbsolutelyContinuousOnInterval (extend (C.physicalMomentum q lambda v)) 0 1 ∧
      MemLp (deriv (extend (C.physicalMomentum q lambda v))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  ⟨absolutelyContinuous_l2QuasiHillPosition _ _ _,memLp_deriv_l2QuasiHillPosition _ _ _,
    absolutelyContinuous_l2QuasiHillMomentum _ _ _,memLp_deriv_l2QuasiHillMomentum _ _ _⟩

theorem physicalPosition_ne_zero (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (lambda : ℂ) (v : ℂ × ℂ) (hv : v ≠ 0) : C.physicalPosition q lambda v ≠ 0 :=
  l2QuasiHillPosition_ne_zero _ _ _ hv

theorem physicalSolution_weak_green_identity (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (lambda : ℂ) (v : ℂ × ℂ) (φ : Curve ℂ)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    shiftedMiuraWeakForm (C.physicalProfile q) C.energyShift (C.physicalPosition q lambda v) φ =
      extend (C.physicalMomentum q lambda v) 1*extend φ 1-
        extend (C.physicalMomentum q lambda v) 0*extend φ 0+
        lambda*(∫ s in (0 : ℝ)..1, extend (C.physicalPosition q lambda v) s*extend φ s) := by
  simpa only [physicalPosition,physicalMomentum,add_sub_cancel_right] using
    l2QuasiHill_weak_green_identity (C.physicalProfile q) (lambda+C.energyShift) C.energyShift v φ hφ hφ₂

theorem physicalSolution_weak_equation_zero_endpoints (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (lambda : ℂ) (v : ℂ × ℂ) (φ : Curve ℂ)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₀ : extend φ 0 = 0) (hφ₁ : extend φ 1 = 0) :
    shiftedMiuraWeakForm (C.physicalProfile q) C.energyShift (C.physicalPosition q lambda v) φ =
      lambda*(∫ s in (0 : ℝ)..1, extend (C.physicalPosition q lambda v) s*extend φ s) := by
  rw [C.physicalSolution_weak_green_identity q lambda v φ hφ hφ₂,hφ₀,hφ₁]
  ring

/-- A state multiplier sigma pairs with the reciprocal test multiplier
rho. Periodic and antiperiodic states and tests are included. -/
theorem physicalSolution_weak_equation_floquet (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (lambda σ ρ : ℂ) (hσρ : σ*ρ = 1) (v : ℂ × ℂ)
    (hv : C.physicalSolution q lambda v ⟨1,by constructor <;> norm_num⟩ = σ • v)
    (φ : Curve ℂ) (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφend : extend φ 1 = ρ*extend φ 0) :
    shiftedMiuraWeakForm (C.physicalProfile q) C.energyShift (C.physicalPosition q lambda v) φ =
      lambda*(∫ s in (0 : ℝ)..1, extend (C.physicalPosition q lambda v) s*extend φ s) := by
  have hw : extend (C.physicalMomentum q lambda v) 1 = σ*extend (C.physicalMomentum q lambda v) 0 := by
    change (extend (C.physicalSolution q lambda v) ((⟨1,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) : ℝ)).2 = _
    rw [extend_coe]
    change (C.physicalSolution q lambda v ⟨1,by constructor <;> norm_num⟩).2 =
      σ*extend (l2QuasiHillMomentum (C.physicalProfile q) (lambda+C.energyShift) v) 0
    rw [l2QuasiHillMomentum_initial]
    simpa only [Prod.smul_snd,smul_eq_mul] using congrArg Prod.snd hv
  rw [C.physicalSolution_weak_green_identity q lambda v φ hφ hφ₂,hw,hφend]
  linear_combination extend (C.physicalMomentum q lambda v) 0*extend φ 0*hσρ

end NLS.KdV.HillHminusMiuraChart
