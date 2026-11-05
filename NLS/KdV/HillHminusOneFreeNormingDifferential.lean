import NLS.KdV.HillHminusOneNormingPerturbation

/-! # Exact original H^-1 derivative of the signed terminal Dirichlet multiplier

The energy-overlap term has zero differential at the free point.
The full H1 graph and resolvent pairing give the remaining derivative,
with the original signed Fourier convention and no finite-mode restriction.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV NLS.Fourier
namespace NLS.KdV

theorem chartDirichletTerminalBranch_signed_fderiv_zero
    (C : HillHminusMiuraChart) (hC : (0 : PeriodOneHminusOne) ∈ C.domain)
    (a : PeriodOneHminusOne → ℂ) (ha : AnalyticAt ℂ a 0) (n : ℕ+)
    (ha0 : a 0 = (freeHillValue (n : ℕ) : ℂ))
    (hroot : ∀ᶠ p in 𝓝 (0 : PeriodOneHminusOne), hillHminusDirichlet p (a p) = 0)
    (h : PeriodOneHminusOne) :
    fderiv ℂ (fun p => (-1 : ℂ)^(n : ℕ)*chartDirichletTerminalBranch C a p) 0 h =
      (h.val (-(n : ℤ))-h.val (n : ℤ))/(4*I*((n : ℂ)*(Real.pi : ℂ))) := by
  let β : PeriodOneHminusOne → ℂ := fun p => (-1 : ℂ)^(n : ℕ)*chartDirichletTerminalBranch C a p
  have hβ : AnalyticAt ℂ β 0 := analyticAt_const.mul (analyticAt_chartDirichletTerminalBranch C a 0 hC ha)
  let Z : PeriodOneHminusOne → Curve ℂ × IntervalL2 := fun p =>
    (hillHminusDirichletColumn p (a p),hillHminusDirichletDerivativeColumn p (a p))
  have hZ : AnalyticAt ℂ Z 0 :=
    (analyticOnNhd_hillHminusDirichletH1Graph_joint _ (mem_univ _)).comp
      (f := fun p : PeriodOneHminusOne => (a p,p)) (ha.prod analyticAt_id)
  let φ := freeDirichletCosineTest n
  have hφ := freeDirichletCosineTest_H1 n
  let dφ : IntervalL2 := hφ.2.toLp (deriv (extend φ))
  let M : PeriodOneHminusOne → ℂ := fun p => unitIntervalMean ((Z p).1*φ)
  have hM : AnalyticAt ℂ M 0 := (unitIntervalMean (E := ℂ)).analyticAt _ |>.comp
    ((analyticAt_fst.comp (f := Z) hZ).mul analyticAt_const)
  have hM0 : M 0 = 0 := by
    change (∫ s in (0 : ℝ)..1, extend (hillHminusDirichletColumn 0 (a 0)) s*extend φ s) = 0
    rw [ha0]
    exact freeDirichlet_sine_cosine_overlap_zero n
  let T : PeriodOneHminusOne → IntervalL2 := fun p => intervalH1MassProduct 0 (Z p) (φ,dφ)
  have hT : AnalyticAt ℂ T 0 :=
    (analyticOnNhd_intervalH1MassProduct_joint 0 _ (mem_univ _)).comp
      (f := fun p : PeriodOneHminusOne => (Z p,(φ,dφ))) (hZ.prod analyticAt_const)
  let P : PeriodOneHminusOne → ℂ := fun p => intervalL2Bilinear (hillHminusMassProfile 0 p) (T p)
  have heq : (fun p => β p-1) =ᶠ[𝓝 (0 : PeriodOneHminusOne)]
      (fun p => ((freeHillValue (n : ℕ) : ℂ)-a p)*M p+P p) := by
    filter_upwards [hroot,C.domain_open.mem_nhds hC] with p hp hpC
    have hy := hillHminusDirichletColumn_H1 p (a p)
    have hend : extend (Z p).1 1*extend φ 1 = extend (Z p).1 0*extend φ 0 := by
      dsimp only [Z]
      simp only [hillHminusDirichletColumn_terminal,hp,hillHminusDirichletColumn_initial,zero_mul]
    have ht := intervalH1MassProduct_eq 0 (Z p).1 φ (Z p).2 dφ hy.1 hφ.1 hy.2 hφ.2
      (hillHminusDirichletDerivativeColumn_representative p (a p)) hφ.2.coeFn_toLp
    have hi := C.dirichlet_norming_free_test_identity p hpC n (a p) hp
    rw [hillHminusWeakPotential_eq_mass 0 p _ _ hy.1 hφ.1 hy.2 hφ.2 hend,
      hillHminusMassPotential,← ht] at hi
    exact hi
  have hP := intervalL2Bilinear.hasFDerivAt_of_bilinear (hillHminusMassProfile 0).hasFDerivAt
    hT.differentiableAt.hasFDerivAt
  have hE := (hasFDerivAt_const (freeHillValue (n : ℕ) : ℂ) (0 : PeriodOneHminusOne)).sub
    ha.differentiableAt.hasFDerivAt
  have hR := (hE.mul hM.differentiableAt.hasFDerivAt).add hP
  have hL := hβ.differentiableAt.hasFDerivAt.sub_const 1
  have hd := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h)
    ((hL.congr_of_eventuallyEq heq.symm).unique hR)
  simp only [Pi.sub_apply,ha0,sub_self,hM0,map_zero,ContinuousLinearMap.precompL_apply,
    add_apply,smul_apply,smul_eq_mul,zero_mul,zero_add,add_zero,zero_apply] at hd
  have hy := hillHminusDirichletColumn_H1 0 (a 0)
  have ht := intervalH1MassProduct_eq 0 (Z 0).1 φ (Z 0).2 dφ hy.1 hφ.1 hy.2 hφ.2
    (hillHminusDirichletDerivativeColumn_representative 0 (a 0)) hφ.2.coeFn_toLp
  have hend : extend (Z 0).1 1*extend φ 1 = extend (Z 0).1 0*extend φ 0 := by
    dsimp only [Z]
    rw [ha0]
    simp only [hillHminusDirichletColumn_terminal,hillHminusDirichlet_free_nat_root (n : ℕ) n.property,
      hillHminusDirichletColumn_initial,zero_mul]
  have hpot := hillHminusWeakPotential_eq_mass 0 h (Z 0).1 φ hy.1 hφ.1 hy.2 hφ.2 hend
  rw [hillHminusMassPotential,← ht] at hpot
  have hout : fderiv ℂ β 0 h = hillHminusWeakPotential h (Z 0).1 φ := hd.trans hpot.symm
  rw [show (Z 0).1 = hillHminusDirichletColumn 0 (freeHillValue (n : ℕ)) from by dsimp only [Z]; rw [ha0],
    hillHminusWeakPotential_free_norming_product] at hout
  exact hout

end NLS.KdV
