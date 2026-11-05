import NLS.KdV.HillHminusOneIntrinsicGreen
import NLS.MKdV.L2QuasiHillWeakReconstruction
import NLS.FunctionalAnalysis.IntervalEndpointTests

/-! # Every Miura chart gives the same normalized Dirichlet position

The scalar curve, not only its terminal value or zero set, is intrinsic
at every complex H^-1 potential and energy. Weak local reconstruction
in another chart and an H1 test with endpoints one and zero recover the
same normalized initial state. At a Dirichlet zero the terminal
quasi-derivative is chart independent as well.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory hiding extend
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV NLS.FunctionalAnalysis
namespace NLS.KdV

theorem HillHminusMiuraChart.dirichlet_position_eq_on_overlap
    (C D : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hC : q ∈ C.domain) (hD : q ∈ D.domain)
    (lambda : ℂ) : C.physicalPosition q lambda (0,1) = D.physicalPosition q lambda (0,1) := by
  let y := C.physicalPosition q lambda (0,1)
  have hy := C.physicalSolution_scalar_H1 q lambda (0,1)
  have hy₀ : extend y 0 = 0 := l2QuasiHillPosition_initial _ _ _
  obtain ⟨v,he⟩ := exists_initial_state_of_weak_Hill_equation (D.physicalProfile q) D.energyShift lambda y
    hy.1 hy.2.1 (by
      intro φ hφ hφ₂ hφ₀ hφ₁
      rw [← hillHminusWeakForm_eq_chart D q hD y φ hy.1 hφ hy.2.1 hφ₂
        (by rw [hφ₀,hφ₁,mul_zero,mul_zero])]
      have hg := C.intrinsic_green_identity q hC lambda (0,1) φ hφ hφ₂
        (by rw [hφ₀,hφ₁,mul_zero,mul_zero])
      simpa only [hφ₀,hφ₁,mul_zero,sub_self,zero_add] using hg)
  change y = D.physicalPosition q lambda v at he
  have hv₀ : v.1 = 0 := by
    have h := congrArg (fun f : Curve ℂ => extend f 0) he
    rw [hy₀] at h
    change 0 = extend (l2QuasiHillPosition _ _ v) 0 at h
    rw [l2QuasiHillPosition_initial] at h
    exact h.symm
  let φ := unitIntervalAffineCurve 1 0
  have hφ := unitIntervalAffineCurve_H1 1 0
  have hφe := unitIntervalAffineCurve_endpoints 1 0
  have hyend : extend y 1*extend φ 1 = extend y 0*extend φ 0 := by rw [hφe.2,hy₀,mul_zero,zero_mul]
  have hgC := C.intrinsic_green_identity q hC lambda (0,1) φ hφ.1 hφ.2 hyend
  rw [hφe.1,hφe.2,mul_zero,mul_one,
    show extend (C.physicalMomentum q lambda (0,1)) 0 = 1 from l2QuasiHillMomentum_initial _ _ _,zero_sub] at hgC
  have hDend : extend (D.physicalPosition q lambda v) 1*extend φ 1 =
      extend (D.physicalPosition q lambda v) 0*extend φ 0 := by rw [← he]; exact hyend
  have hgD := D.intrinsic_green_identity q hD lambda v φ hφ.1 hφ.2 hDend
  rw [hφe.1,hφe.2,mul_zero,mul_one,
    show extend (D.physicalMomentum q lambda v) 0 = v.2 from l2QuasiHillMomentum_initial _ _ _,zero_sub,← he] at hgD
  have hv₁ : v.2 = 1 := by linear_combination hgD-hgC
  rw [show v = (0,1) from Prod.ext hv₀ hv₁] at he
  exact he

theorem HillHminusMiuraChart.dirichlet_momentum_eq_on_overlap_at_zero
    (C D : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hC : q ∈ C.domain) (hD : q ∈ D.domain)
    (lambda : ℂ) (hz : extend (C.physicalPosition q lambda (0,1)) 1 = 0) :
    extend (C.physicalMomentum q lambda (0,1)) 1 = extend (D.physicalMomentum q lambda (0,1)) 1 := by
  have he := C.dirichlet_position_eq_on_overlap D q hC hD lambda
  let φ := unitIntervalAffineCurve 0 1
  have hφ := unitIntervalAffineCurve_H1 0 1
  have hφe := unitIntervalAffineCurve_endpoints 0 1
  have hend : extend (C.physicalPosition q lambda (0,1)) 1*extend φ 1 =
      extend (C.physicalPosition q lambda (0,1)) 0*extend φ 0 := by rw [hz,hφe.1,zero_mul,mul_zero]
  have hendD : extend (D.physicalPosition q lambda (0,1)) 1*extend φ 1 =
      extend (D.physicalPosition q lambda (0,1)) 0*extend φ 0 := by rw [← he]; exact hend
  have hgC := C.intrinsic_green_identity q hC lambda (0,1) φ hφ.1 hφ.2 hend
  have hgD := D.intrinsic_green_identity q hD lambda (0,1) φ hφ.1 hφ.2 hendD
  rw [hφe.1,hφe.2,mul_zero,mul_one,sub_zero] at hgC hgD
  rw [← he] at hgD
  linear_combination hgD-hgC

end NLS.KdV
