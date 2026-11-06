import NLS.KdV.HillHminusOneNormingVariation
import NLS.KdV.HillHminusOneDirichletDifferential

/-! # The exact norming differential at every complex Dirichlet branch

The potential variation is paired with the fixed sine-cosine product at
the base potential. The energy variation contributes the exact overlap
correction. Full H1 graph analyticity differentiates the original H^-1
pairing; all directions are allowed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV NLS.Fourier
namespace NLS.KdV

theorem chartDirichletTerminalBranch_relative_differential
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hC : q ∈ C.domain)
    (a : PeriodOneHminusOne → ℂ) (ha : AnalyticAt ℂ a q)
    (hzero : hillHminusDirichlet q (a q) = 0)
    (hroot : ∀ᶠ p in 𝓝 q, hillHminusDirichlet p (a p) = 0)
    (h : PeriodOneHminusOne) :
    extend (C.physicalPosition q (a q) (1,0)) 1*
        fderiv ℂ (chartDirichletTerminalBranch C a) q h =
      hillHminusWeakPotential h (hillHminusDirichletColumn q (a q)) (C.physicalPosition q (a q) (1,0))-
        fderiv ℂ a q h*(∫ s in (0 : ℝ)..1,
          extend (hillHminusDirichletColumn q (a q)) s*extend (C.physicalPosition q (a q) (1,0)) s) := by
  let Z : PeriodOneHminusOne → Curve ℂ × IntervalL2 := fun p =>
    (hillHminusDirichletColumn p (a p),hillHminusDirichletDerivativeColumn p (a p))
  have hZ : AnalyticAt ℂ Z q :=
    (analyticOnNhd_hillHminusDirichletH1Graph_joint _ (mem_univ _)).comp
      (f := fun p : PeriodOneHminusOne => (a p,p)) (ha.prod analyticAt_id)
  let φ := C.physicalPosition q (a q) (1,0)
  have hφ := C.physicalSolution_scalar_H1 q (a q) (1,0)
  let dφ : IntervalL2 := hφ.2.1.toLp (deriv (extend φ))
  let M : PeriodOneHminusOne → ℂ := fun p => unitIntervalMean ((Z p).1*φ)
  have hM : AnalyticAt ℂ M q := (unitIntervalMean (E := ℂ)).analyticAt _ |>.comp
    ((analyticAt_fst.comp (f := Z) hZ).mul analyticAt_const)
  let T : PeriodOneHminusOne → IntervalL2 := fun p => intervalH1MassProduct 0 (Z p) (φ,dφ)
  have hT : AnalyticAt ℂ T q :=
    (analyticOnNhd_intervalH1MassProduct_joint 0 _ (mem_univ _)).comp
      (f := fun p : PeriodOneHminusOne => (Z p,(φ,dφ))) (hZ.prod analyticAt_const)
  let P : PeriodOneHminusOne → ℂ := fun p => intervalL2Bilinear (hillHminusMassProfile 0 (p-q)) (T p)
  have heq : (fun p => extend φ 1*chartDirichletTerminalBranch C a p-1) =ᶠ[𝓝 q]
      (fun p => (a q-a p)*M p+P p) := by
    filter_upwards [hroot,C.domain_open.mem_nhds hC] with p hp hpC
    have hy := hillHminusDirichletColumn_H1 p (a p)
    have hend : extend (Z p).1 1*extend φ 1 = extend (Z p).1 0*extend φ 0 := by
      dsimp only [Z]
      simp only [hillHminusDirichletColumn_terminal,hp,hillHminusDirichletColumn_initial,zero_mul]
    have ht := intervalH1MassProduct_eq 0 (Z p).1 φ (Z p).2 dφ hy.1 hφ.1 hy.2 hφ.2.1
      (hillHminusDirichletDerivativeColumn_representative p (a p)) hφ.2.1.coeFn_toLp
    have hi := C.dirichlet_norming_two_potential_identity C p q hpC hC (a p) (a q) hp
    rw [hillHminusWeakPotential_eq_mass 0 (p-q) _ _ hy.1 hφ.1 hy.2 hφ.2.1 hend,
      hillHminusMassPotential,← ht] at hi
    exact hi
  have hU : HasFDerivAt (fun p : PeriodOneHminusOne => hillHminusMassProfile 0 (p-q))
      (hillHminusMassProfile 0) q := by
    have hh := (hillHminusMassProfile 0).hasFDerivAt.comp q ((hasFDerivAt_id q).sub_const q)
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using! hh
  have hP := intervalL2Bilinear.hasFDerivAt_of_bilinear hU hT.differentiableAt.hasFDerivAt
  have hE := (hasFDerivAt_const (a q) q).sub ha.differentiableAt.hasFDerivAt
  have hR := (hE.mul hM.differentiableAt.hasFDerivAt).add hP
  have hL := (((analyticAt_chartDirichletTerminalBranch C a q hC ha).differentiableAt.hasFDerivAt).const_mul
    (extend φ 1)).sub_const 1
  have hd := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h)
    ((hL.congr_of_eventuallyEq heq.symm).unique hR)
  simp only [Pi.sub_apply,sub_self,map_zero,ContinuousLinearMap.precompL_apply,
    add_apply,sub_apply,smul_apply,smul_eq_mul,zero_mul,zero_add,zero_apply] at hd
  have hy := hillHminusDirichletColumn_H1 q (a q)
  have ht := intervalH1MassProduct_eq 0 (Z q).1 φ (Z q).2 dφ hy.1 hφ.1 hy.2 hφ.2.1
    (hillHminusDirichletDerivativeColumn_representative q (a q)) hφ.2.1.coeFn_toLp
  have hend : extend (Z q).1 1*extend φ 1 = extend (Z q).1 0*extend φ 0 := by
    dsimp only [Z]
    simp only [hillHminusDirichletColumn_terminal,hzero,hillHminusDirichletColumn_initial,zero_mul]
  have hpot := hillHminusWeakPotential_eq_mass 0 h (Z q).1 φ hy.1 hφ.1 hy.2 hφ.2.1 hend
  rw [hillHminusMassPotential,← ht] at hpot
  change hillHminusWeakPotential h (Z q).1 φ = intervalL2Bilinear (hillHminusMassProfile 0 h) (T q) at hpot
  change extend φ 1*fderiv ℂ (chartDirichletTerminalBranch C a) q h =
    hillHminusWeakPotential h (Z q).1 φ-fderiv ℂ a q h*M q
  rw [hpot]
  linear_combination hd

end NLS.KdV
