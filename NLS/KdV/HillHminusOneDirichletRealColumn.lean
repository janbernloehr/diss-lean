import NLS.KdV.HillHminusOneDirichletSimplicity
import NLS.KdV.HillHminusOneIntrinsicGreen
import NLS.FunctionalAnalysis.IntervalEndpointTests

/-! # Reality of the actual normalized Dirichlet column

Weak conjugation and local reconstruction produce an actual state for
the conjugate position. A real H1 endpoint test fixes its initial
quasi-derivative to one. Thus the normalized position is real on the
whole interval at every real original energy and real H^-1 potential,
even when the chosen Miura lift and shift are complex. At a Dirichlet
root the terminal quasi-derivative is real as well.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory hiding extend
open scoped ComplexConjugate
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV NLS.FunctionalAnalysis
namespace NLS.KdV

theorem intrinsic_local_weak_conj (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (x : ℝ) (y : Curve ℂ) (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hw : ∀ φ : Curve ℂ, AbsolutelyContinuousOnInterval (extend φ) 0 1 →
      MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
      extend φ 0 = 0 → extend φ 1 = 0 →
      hillHminusWeakForm q y φ = x*(∫ s in (0 : ℝ)..1, extend y s*extend φ s)) :
    ∀ φ : Curve ℂ, AbsolutelyContinuousOnInterval (extend φ) 0 1 →
      MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
      extend φ 0 = 0 → extend φ 1 = 0 →
      hillHminusWeakForm q (star y) φ = x*(∫ s in (0 : ℝ)..1, extend (star y) s*extend φ s) := by
  intro φ hφ hφ₂ hφ₀ hφ₁
  have hφs := absolutelyContinuous_curve_star φ hφ
  have hφs₂ := memLp_deriv_curve_star φ hφ₂
  have he := congrArg (starRingEnd ℂ) (hw (star φ) hφs hφs₂
    (by change conj (extend φ 0) = 0; rw [hφ₀,map_zero])
    (by change conj (extend φ 1) = 0; rw [hφ₁,map_zero]))
  have hc := hillHminusWeakForm_conj q hr y (star φ) hy hφs hy₂ hφs₂
    (by change extend y 1*conj (extend φ 1) = extend y 0*conj (extend φ 0)
        rw [hφ₀,hφ₁,map_zero,mul_zero,mul_zero])
  rw [star_star] at hc
  rw [hc,map_mul,conj_ofReal,← intervalIntegral.intervalIntegral_conj] at he
  convert he using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  change conj (NLS.LinearVolterra.extend y s)*NLS.LinearVolterra.extend φ s =
    conj (NLS.LinearVolterra.extend y s*conj (NLS.LinearVolterra.extend φ s))
  rw [map_mul,conj_conj]

theorem HillHminusMiuraChart.physicalPosition_dirichlet_star_real
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (hr : IsRealPeriodOneHminusOne q) (x : ℝ) :
    star (C.physicalPosition q x (0,1)) = C.physicalPosition q x (0,1) := by
  let y := C.physicalPosition q x (0,1)
  have hy := C.physicalSolution_scalar_H1 q x (0,1)
  have hy₀ : extend y 0 = 0 := l2QuasiHillPosition_initial _ _ _
  have hys := absolutelyContinuous_curve_star y hy.1
  have hys₂ := memLp_deriv_curve_star y hy.2.1
  have hlocal := intrinsic_local_weak_conj q hr x y hy.1 hy.2.1 (by
    intro φ hφ hφ₂ hφ₀ hφ₁
    have hg := C.intrinsic_green_identity q hq x (0,1) φ hφ hφ₂
      (by rw [hφ₀,hφ₁,mul_zero,mul_zero])
    simpa only [hφ₀,hφ₁,mul_zero,sub_self,zero_add] using hg)
  obtain ⟨v,he⟩ := exists_initial_state_of_weak_Hill_equation (C.physicalProfile q) C.energyShift x
    (star y) hys hys₂ (by
      intro φ hφ hφ₂ hφ₀ hφ₁
      rw [← hillHminusWeakForm_eq_chart C q hq (star y) φ hys hφ hys₂ hφ₂
        (by rw [hφ₀,hφ₁,mul_zero,mul_zero])]
      exact hlocal φ hφ hφ₂ hφ₀ hφ₁)
  have hv₀ : v.1 = 0 := by
    have h := congrArg (fun f : Curve ℂ => extend f 0) he
    change conj (extend y 0) = extend (l2QuasiHillPosition _ _ v) 0 at h
    rw [hy₀,map_zero,l2QuasiHillPosition_initial] at h
    exact h.symm
  let φ := unitIntervalAffineCurve 1 0
  have hφ := unitIntervalAffineCurve_H1 1 0
  have hφe := unitIntervalAffineCurve_endpoints 1 0
  have hφs : star φ = φ := unitIntervalAffineCurve_star_real 1 0
  have hend : extend y 1*extend φ 1 = extend y 0*extend φ 0 := by rw [hφe.2,hy₀,mul_zero,zero_mul]
  have hg : hillHminusWeakForm q y φ = -1+x*(∫ s in (0 : ℝ)..1, extend y s*extend φ s) := by
    have h := C.intrinsic_green_identity q hq x (0,1) φ hφ.1 hφ.2 hend
    rw [hφe.1,hφe.2,mul_zero,mul_one] at h
    simpa only [HillHminusMiuraChart.physicalMomentum,l2QuasiHillMomentum_initial,zero_sub] using h
  have hmass : conj (∫ s in (0 : ℝ)..1, extend y s*extend φ s) =
      ∫ s in (0 : ℝ)..1, extend (star y) s*extend φ s := by
    rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro s _
    have hp := congrArg (fun f : Curve ℂ => extend f s) hφs
    change conj (extend φ s) = extend φ s at hp
    change conj (NLS.LinearVolterra.extend y s*NLS.LinearVolterra.extend φ s) =
      conj (NLS.LinearVolterra.extend y s)*NLS.LinearVolterra.extend φ s
    rw [map_mul,hp]
  have hc := congrArg (starRingEnd ℂ) hg
  rw [hillHminusWeakForm_conj q hr y φ hy.1 hφ.1 hy.2.1 hφ.2 hend,hφs,
    map_add,map_neg,map_one,map_mul,conj_ofReal,hmass] at hc
  have hvend : extend (C.physicalPosition q x v) 1*extend φ 1 =
      extend (C.physicalPosition q x v) 0*extend φ 0 := by
    rw [hφe.2,mul_zero]
    change 0 = extend (l2QuasiHillPosition _ _ v) 0*extend φ 0
    rw [l2QuasiHillPosition_initial,hv₀,zero_mul]
  have hvG := C.intrinsic_green_identity q hq x v φ hφ.1 hφ.2 hvend
  rw [hφe.1,hφe.2,mul_zero,mul_one,zero_sub] at hvG
  rw [show extend (C.physicalMomentum q x v) 0 = v.2 from l2QuasiHillMomentum_initial _ _ _] at hvG
  change hillHminusWeakForm q (C.physicalPosition q x v) φ =
    -v.2+x*(∫ s in (0 : ℝ)..1, extend (C.physicalPosition q x v) s*extend φ s) at hvG
  change star y = C.physicalPosition q x v at he
  rw [← he] at hvG
  have hv₁ : v.2 = 1 := by linear_combination hvG-hc
  rw [show v = (0,1) from Prod.ext hv₀ hv₁] at he
  exact he

theorem hillHminusDirichlet_real (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (x : ℝ) :
    (hillHminusDirichlet q x).im = 0 := by
  let C := hillHminusMiuraChartAt q
  have hq : q ∈ C.domain := mem_hillHminusMiuraChartAt q
  have he := congrArg (fun f : Curve ℂ => extend f 1) (C.physicalPosition_dirichlet_star_real q hq hr x)
  change conj (extend (C.physicalPosition q x (0,1)) 1) = extend (C.physicalPosition q x (0,1)) 1 at he
  rw [← C.hillHminusDirichlet_eq_physicalPosition q hq x] at he
  have hi := congrArg Complex.im he
  simp only [conj_im] at hi
  linarith

end NLS.KdV
