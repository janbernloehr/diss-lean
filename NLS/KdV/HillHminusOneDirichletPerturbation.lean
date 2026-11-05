import NLS.KdV.HillHminusOneIntrinsicDirichletColumn
import NLS.KdV.HillHminusOneWeakPotentialFunctional
import NLS.KdV.HillHminusOneIntrinsicGreen

/-! # The intrinsic two-potential Dirichlet perturbation identity

For actual normalized Dirichlet columns at arbitrary complex roots,
the energy difference times their unconjugated overlap equals the
original H^-1 potential difference paired with their product. All
boundary terms vanish intrinsically; no common Miura chart is needed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

theorem hillHminusWeakForm_comm (q : PeriodOneHminusOne) (y φ : Curve ℂ) :
    hillHminusWeakForm q y φ = hillHminusWeakForm q φ y :=
  shiftedMiuraWeakForm_comm _ _ _ _

theorem hillHminusWeakPotential_sub (q r : PeriodOneHminusOne) (y φ : Curve ℂ)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend y 1*extend φ 1 = extend y 0*extend φ 0) :
    hillHminusWeakPotential (q-r) y φ = hillHminusWeakForm q y φ-hillHminusWeakForm r y φ := by
  have h := (hillHminusWeakPotentialCLM y φ hy hφ hy₂ hφ₂ hend).map_sub q r
  simp only [hillHminusWeakPotentialCLM_apply,hillHminusWeakPotential] at h
  unfold hillHminusWeakPotential
  linear_combination h

theorem hillHminusDirichletColumn_weak (q : PeriodOneHminusOne) (lambda : ℂ)
    (φ : Curve ℂ)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₀ : extend φ 0 = 0) (hφ₁ : extend φ 1 = 0) :
    hillHminusWeakForm q (hillHminusDirichletColumn q lambda) φ =
      lambda*(∫ s in (0 : ℝ)..1, extend (hillHminusDirichletColumn q lambda) s*extend φ s) := by
  let C := hillHminusMiuraChartAt q
  have hq : q ∈ C.domain := mem_hillHminusMiuraChartAt q
  have hend : extend (C.physicalPosition q lambda (0,1)) 1*extend φ 1 =
      extend (C.physicalPosition q lambda (0,1)) 0*extend φ 0 := by rw [hφ₀,hφ₁,mul_zero,mul_zero]
  have h := C.intrinsic_green_identity q hq lambda (0,1) φ hφ hφ₂ hend
  rw [hφ₀,hφ₁,mul_zero,mul_zero,sub_self,zero_add] at h
  exact h

theorem hillHminusDirichlet_two_potential_identity
    (q p : PeriodOneHminusOne) (lambda mu : ℂ)
    (hq : hillHminusDirichlet q lambda = 0) (hp : hillHminusDirichlet p mu = 0) :
    (mu-lambda)*(∫ s in (0 : ℝ)..1,
      extend (hillHminusDirichletColumn q lambda) s*extend (hillHminusDirichletColumn p mu) s) =
      hillHminusWeakPotential (p-q) (hillHminusDirichletColumn q lambda) (hillHminusDirichletColumn p mu) := by
  let y := hillHminusDirichletColumn q lambda
  let z := hillHminusDirichletColumn p mu
  have hy := hillHminusDirichletColumn_H1 q lambda
  have hz := hillHminusDirichletColumn_H1 p mu
  have hy₀ : extend y 0 = 0 := hillHminusDirichletColumn_initial _ _
  have hz₀ : extend z 0 = 0 := hillHminusDirichletColumn_initial _ _
  have hy₁ : extend y 1 = 0 := (hillHminusDirichletColumn_terminal _ _).trans hq
  have hz₁ : extend z 1 = 0 := (hillHminusDirichletColumn_terminal _ _).trans hp
  have hY := hillHminusDirichletColumn_weak q lambda z hz.1 hz.2 hz₀ hz₁
  have hZ := hillHminusDirichletColumn_weak p mu y hy.1 hy.2 hy₀ hy₁
  have hcomm : (∫ s in (0 : ℝ)..1, extend z s*extend y s) =
      ∫ s in (0 : ℝ)..1, extend y s*extend z s :=
    intervalIntegral.integral_congr (fun _ _ => mul_comm _ _)
  change hillHminusWeakForm p z y = _ at hZ
  rw [hillHminusWeakForm_comm p z y,hcomm] at hZ
  rw [hillHminusWeakPotential_sub p q y z hy.1 hz.1 hy.2 hz.2 (by rw [hy₀,hy₁,zero_mul,zero_mul])]
  change (mu-lambda)*(∫ s in (0 : ℝ)..1, extend y s*extend z s) = _
  rw [hY,hZ]
  ring

end NLS.KdV
