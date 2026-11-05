import NLS.KdV.HillHminusOneDirichletDifferential
import NLS.MKdV.L2QuasiHillFreeSolution
import NLS.FunctionalAnalysis.IntervalEndpointTests

/-! # The exact intrinsic free normalized Dirichlet column

Weak reconstruction at zero potential and an endpoint test fix both
initial constants. Thus the entire intrinsic scalar curve agrees with
the free sine column, with its exact factor 1/z, at every nonzero
complex frequency. No chosen Miura chart is assumed to vanish at zero.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV NLS.FunctionalAnalysis
namespace NLS.KdV

theorem hillHminusWeakForm_zero_eq_shifted_zero (y φ : Curve ℂ)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend y 1*extend φ 1 = extend y 0*extend φ 0) :
    hillHminusWeakForm 0 y φ = shiftedMiuraWeakForm 0 0 y φ := by
  have he := hillHminusWeakForm_eq_physicalL2 (0 : Coeff 2) y φ hy hφ hy₂ hφ₂ hend
  rw [shiftedMiuraWeakForm_zero_profile]
  simpa only [map_zero,physicalL2HillWeakForm,add_zero] using he

theorem hillHminusDirichletColumn_zero_eq_rough (lambda : ℂ) :
    hillHminusDirichletColumn 0 lambda = l2QuasiHillPosition 0 lambda (0,1) := by
  let y := hillHminusDirichletColumn 0 lambda
  have hy := hillHminusDirichletColumn_H1 0 lambda
  have hy₀ : extend y 0 = 0 := hillHminusDirichletColumn_initial _ _
  obtain ⟨v,he⟩ := exists_initial_state_of_weak_Hill_equation 0 0 lambda y hy.1 hy.2 (by
    intro φ hφ hφ₂ hφ₀ hφ₁
    rw [← hillHminusWeakForm_zero_eq_shifted_zero y φ hy.1 hφ hy.2 hφ₂
      (by rw [hφ₀,hφ₁,mul_zero,mul_zero])]
    exact hillHminusDirichletColumn_weak 0 lambda φ hφ hφ₂ hφ₀ hφ₁)
  rw [add_zero] at he
  have hv₀ : v.1 = 0 := by
    have h := congrArg (fun f : Curve ℂ => extend f 0) he
    rw [hy₀,l2QuasiHillPosition_initial] at h
    exact h.symm
  let φ := unitIntervalAffineCurve 1 0
  have hφ := unitIntervalAffineCurve_H1 1 0
  have hφe := unitIntervalAffineCurve_endpoints 1 0
  have hend : extend y 1*extend φ 1 = extend y 0*extend φ 0 := by
    rw [hφe.2,hy₀,mul_zero,zero_mul]
  let C := hillHminusMiuraChartAt 0
  have hC : (0 : PeriodOneHminusOne) ∈ C.domain := mem_hillHminusMiuraChartAt 0
  have hgC := C.intrinsic_green_identity 0 hC lambda (0,1) φ hφ.1 hφ.2 hend
  rw [hφe.1,hφe.2,mul_zero,mul_one,
    show extend (C.physicalMomentum 0 lambda (0,1)) 0 = 1 from l2QuasiHillMomentum_initial _ _ _,zero_sub] at hgC
  have hgD := l2QuasiHill_weak_green_identity 0 lambda 0 v φ hφ.1 hφ.2
  rw [hφe.1,hφe.2,mul_zero,mul_one,l2QuasiHillMomentum_initial,zero_sub,sub_zero,← he] at hgD
  change hillHminusWeakForm 0 y φ = -1+lambda*(∫ s in (0 : ℝ)..1, extend y s*extend φ s) at hgC
  rw [hillHminusWeakForm_zero_eq_shifted_zero y φ hy.1 hφ.1 hy.2 hφ.2 hend] at hgC
  have hv₁ : v.2 = 1 := by linear_combination hgD-hgC
  rw [show v = (0,1) from Prod.ext hv₀ hv₁] at he
  exact he

theorem hillHminusDirichletColumn_zero_sq (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    hillHminusDirichletColumn 0 (z^2) t = sin (z*t.val)/z := by
  rw [hillHminusDirichletColumn_zero_eq_rough,l2QuasiHillPosition_zero_profile_sq z hz]

theorem hillHminusDirichletColumn_zero_free (n : ℕ+) (t : Icc (0 : ℝ) 1) :
    hillHminusDirichletColumn 0 (freeHillValue (n : ℕ)) t =
      sin ((n : ℂ)*(Real.pi : ℂ)*t.val)/((n : ℂ)*(Real.pi : ℂ)) := by
  have he : (freeHillValue (n : ℕ) : ℂ) = ((n : ℂ)*(Real.pi : ℂ))^2 := by
    unfold freeHillValue
    push_cast
    ring
  rw [he]
  apply hillHminusDirichletColumn_zero_sq
  exact mul_ne_zero (by exact_mod_cast n.ne_zero) (by exact_mod_cast Real.pi_ne_zero)

end NLS.KdV
