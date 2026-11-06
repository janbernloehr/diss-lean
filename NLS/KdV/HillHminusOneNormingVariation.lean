import NLS.KdV.HillHminusOneNormingPerturbation

/-! # The exact two-potential terminal norming identity

A cosine column at an arbitrary base potential replaces the free cosine
test. The identity is intrinsic in the perturbed potential and is valid
at every complex Dirichlet root, without any open-gap hypothesis.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

theorem HillHminusMiuraChart.dirichlet_norming_two_potential_identity
    (C D : HillHminusMiuraChart) (p q : PeriodOneHminusOne)
    (hp : p ∈ C.domain) (hq : q ∈ D.domain) (mu lambda : ℂ)
    (hzero : hillHminusDirichlet p mu = 0) :
    extend (D.physicalPosition q lambda (1,0)) 1*
        extend (C.physicalMomentum p mu (0,1)) 1-1 =
      (lambda-mu)*(∫ s in (0 : ℝ)..1,
        extend (hillHminusDirichletColumn p mu) s*extend (D.physicalPosition q lambda (1,0)) s)+
      hillHminusWeakPotential (p-q) (hillHminusDirichletColumn p mu) (D.physicalPosition q lambda (1,0)) := by
  let y := hillHminusDirichletColumn p mu
  let φ := D.physicalPosition q lambda (1,0)
  have hy := hillHminusDirichletColumn_H1 p mu
  have hφ := D.physicalSolution_scalar_H1 q lambda (1,0)
  have hy₀ : extend y 0 = 0 := hillHminusDirichletColumn_initial _ _
  have hy₁ : extend y 1 = 0 := (hillHminusDirichletColumn_terminal _ _).trans hzero
  have hφ₀ : extend φ 0 = 1 := l2QuasiHillPosition_initial _ _ _
  have hend : extend y 1*extend φ 1 = extend y 0*extend φ 0 := by rw [hy₀,hy₁,zero_mul,zero_mul]
  have hC := C.intrinsic_green_identity p hp mu (0,1) φ hφ.1 hφ.2.1 (by
    rw [← hillHminusDirichletColumn_eq_chart C p hp mu]
    exact hend)
  rw [← hillHminusDirichletColumn_eq_chart C p hp mu,hφ₀,
    show extend (C.physicalMomentum p mu (0,1)) 0 = 1 from l2QuasiHillMomentum_initial _ _ _,mul_one] at hC
  have hD := D.intrinsic_green_identity q hq lambda (1,0) y hy.1 hy.2 (by
    change extend φ 1*extend y 1 = extend φ 0*extend y 0
    rw [hy₀,hy₁,mul_zero,mul_zero])
  change hillHminusWeakForm q φ y = _ at hD
  rw [hy₀,hy₁,mul_zero,mul_zero,sub_self,zero_add] at hD
  have hcomm : (∫ s in (0 : ℝ)..1, extend φ s*extend y s) =
      ∫ s in (0 : ℝ)..1, extend y s*extend φ s :=
    intervalIntegral.integral_congr (fun _ _ => mul_comm _ _)
  rw [hillHminusWeakForm_comm q φ y,hcomm] at hD
  have hpot := hillHminusWeakPotential_sub p q y φ hy.1 hφ.1 hy.2 hφ.2.1 hend
  change hillHminusWeakForm p y φ = _ at hC
  rw [hC,hD] at hpot
  change _ = (lambda-mu)*(∫ s in (0 : ℝ)..1, extend y s*extend φ s)+hillHminusWeakPotential (p-q) y φ
  linear_combination -hpot

theorem HillHminusMiuraChart.dirichlet_cosine_terminal_reciprocal
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (lambda : ℂ) (hzero : hillHminusDirichlet q lambda = 0) :
    extend (C.physicalPosition q lambda (1,0)) 1*
      extend (C.physicalMomentum q lambda (0,1)) 1 = 1 := by
  have h := C.dirichlet_norming_two_potential_identity C q q hq hq lambda lambda hzero
  have hy := hillHminusDirichletColumn_H1 q lambda
  have hφ := C.physicalSolution_scalar_H1 q lambda (1,0)
  have hend : extend (hillHminusDirichletColumn q lambda) 1*extend (C.physicalPosition q lambda (1,0)) 1 =
      extend (hillHminusDirichletColumn q lambda) 0*extend (C.physicalPosition q lambda (1,0)) 0 := by
    simp only [hillHminusDirichletColumn_terminal,hzero,hillHminusDirichletColumn_initial,zero_mul]
  have hpot := hillHminusWeakPotential_sub q q _ _ hy.1 hφ.1 hy.2 hφ.2.1 hend
  simp only [sub_self] at hpot
  simp only [sub_self,zero_mul,hpot,add_zero] at h
  exact sub_eq_zero.mp h

end NLS.KdV
