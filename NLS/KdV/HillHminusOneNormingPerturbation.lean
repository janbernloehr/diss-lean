import NLS.KdV.HillHminusOneFreeNormingPairing

/-! # Exact terminal norming perturbation against the free cosine test

At any actual complex Dirichlet root the signed terminal momentum is
related to the original H^-1 potential pairing and an energy-overlap
term. The initial quasi-momentum is exactly one in every Miura chart.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

def chartDirichletTerminalBranch (C : HillHminusMiuraChart) (a : PeriodOneHminusOne → ℂ)
    (p : PeriodOneHminusOne) : ℂ := extend (C.physicalMomentum p (a p) (0,1)) 1

theorem analyticAt_chartDirichletTerminalBranch (C : HillHminusMiuraChart)
    (a : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (ha : AnalyticAt ℂ a q) : AnalyticAt ℂ (chartDirichletTerminalBranch C a) q := by
  have hW := (C.analyticOnNhd_physicalMomentum (0,1) (a q,q) ⟨mem_univ _,hq⟩).comp
    (f := fun p : PeriodOneHminusOne => (a p,p)) (ha.prod analyticAt_id)
  have he := ((ContinuousMap.evalCLM ℂ (⟨1,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)).analyticAt _).comp hW
  apply he.congr
  exact Filter.Eventually.of_forall (fun p =>
    (extend_coe (C.physicalMomentum p (a p) (0,1)) ⟨1,by constructor <;> norm_num⟩).symm)

theorem HillHminusMiuraChart.dirichlet_norming_free_test_identity (C : HillHminusMiuraChart)
    (p : PeriodOneHminusOne) (hp : p ∈ C.domain) (n : ℕ+) (lambda : ℂ)
    (hzero : hillHminusDirichlet p lambda = 0) :
    (-1 : ℂ)^(n : ℕ)*extend (C.physicalMomentum p lambda (0,1)) 1-1 =
      ((freeHillValue (n : ℕ) : ℂ)-lambda)*(∫ s in (0 : ℝ)..1,
        extend (hillHminusDirichletColumn p lambda) s*extend (freeDirichletCosineTest n) s)+
      hillHminusWeakPotential p (hillHminusDirichletColumn p lambda) (freeDirichletCosineTest n) := by
  let y := hillHminusDirichletColumn p lambda
  let φ := freeDirichletCosineTest n
  have hy := hillHminusDirichletColumn_H1 p lambda
  have hφ := freeDirichletCosineTest_H1 n
  have hφe := freeDirichletCosineTest_endpoints n
  have hy₀ : extend y 0 = 0 := hillHminusDirichletColumn_initial _ _
  have hy₁ : extend y 1 = 0 := (hillHminusDirichletColumn_terminal _ _).trans hzero
  have hend : extend y 1*extend φ 1 = extend y 0*extend φ 0 := by rw [hy₀,hy₁,zero_mul,zero_mul]
  have hC := C.intrinsic_green_identity p hp lambda (0,1) φ hφ.1 hφ.2 (by
    rw [← hillHminusDirichletColumn_eq_chart C p hp lambda]
    exact hend)
  rw [← hillHminusDirichletColumn_eq_chart C p hp lambda,hφe.1,hφe.2,
    show extend (C.physicalMomentum p lambda (0,1)) 0 = 1 from l2QuasiHillMomentum_initial _ _ _,mul_one] at hC
  have hF := l2QuasiHill_weak_green_identity 0 (freeHillValue (n : ℕ)) 0 (1,0) y hy.1 hy.2
  change shiftedMiuraWeakForm 0 0 φ y = _ at hF
  rw [hy₀,hy₁,mul_zero,mul_zero,sub_self,zero_add,sub_zero] at hF
  change shiftedMiuraWeakForm 0 0 φ y = (freeHillValue (n : ℕ) : ℂ)*
    (∫ s in (0 : ℝ)..1, extend φ s*extend y s) at hF
  have hcomm : (∫ s in (0 : ℝ)..1, extend φ s*extend y s) =
      ∫ s in (0 : ℝ)..1, extend y s*extend φ s :=
    intervalIntegral.integral_congr (fun _ _ => mul_comm _ _)
  rw [shiftedMiuraWeakForm_comm 0 0 φ y,hcomm,
    ← hillHminusWeakForm_zero_eq_shifted_zero y φ hy.1 hφ.1 hy.2 hφ.2 hend] at hF
  have hpot := hillHminusWeakPotential_sub p 0 y φ hy.1 hφ.1 hy.2 hφ.2 hend
  rw [sub_zero] at hpot
  change hillHminusWeakForm p y φ = _ at hC
  rw [hC,hF] at hpot
  change _ = ((freeHillValue (n : ℕ) : ℂ)-lambda)*
    (∫ s in (0 : ℝ)..1, extend y s*extend φ s)+hillHminusWeakPotential p y φ
  linear_combination -hpot

end NLS.KdV
