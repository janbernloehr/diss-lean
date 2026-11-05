import NLS.KdV.HillHminusOneDirichletH1Analytic
import NLS.KdV.HillHminusOneDirichletPerturbation
import NLS.KdV.HillHminusOneMassPotentialPairing
import NLS.Fourier.IntervalH1ProductGraph
import NLS.KdV.HillHminusOneDirichletGapLabels
import NLS.FunctionalAnalysis.UnitIntervalMean

/-! # The actual H^-1 differential of every Dirichlet energy branch

Differentiating the intrinsic two-potential identity in the full H1
graph yields the exact Hellmann--Feynman pairing with the squared
normalized column. The derivative is in the original complex H^-1
Banach norm, and all actual positive labels, including closed gaps,
have this same locally analytic formula.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV NLS.Fourier
namespace NLS.KdV

theorem hillHminusDirichlet_branch_differential
    (q : PeriodOneHminusOne) (a : PeriodOneHminusOne → ℂ) (ha : AnalyticAt ℂ a q)
    (hzero : hillHminusDirichlet q (a q) = 0)
    (hroot : ∀ᶠ p in 𝓝 q, hillHminusDirichlet p (a p) = 0) (h : PeriodOneHminusOne) :
    fderiv ℂ a q h*(∫ s in (0 : ℝ)..1,
      extend (hillHminusDirichletColumn q (a q)) s*extend (hillHminusDirichletColumn q (a q)) s) =
      hillHminusWeakPotential h (hillHminusDirichletColumn q (a q)) (hillHminusDirichletColumn q (a q)) := by
  let Z : PeriodOneHminusOne → Curve ℂ × IntervalL2 := fun p =>
    (hillHminusDirichletColumn p (a p),hillHminusDirichletDerivativeColumn p (a p))
  have hZ : AnalyticAt ℂ Z q :=
    (analyticOnNhd_hillHminusDirichletH1Graph_joint _ (mem_univ _)).comp
      (f := fun p : PeriodOneHminusOne => (a p,p)) (ha.prod analyticAt_id)
  let y := (Z q).1
  let M : PeriodOneHminusOne → ℂ := fun p => unitIntervalMean (y*(Z p).1)
  have hM : AnalyticAt ℂ M q := (unitIntervalMean (E := ℂ)).analyticAt _ |>.comp
    (analyticAt_const.mul (analyticAt_fst.comp (f := Z) hZ))
  let T : PeriodOneHminusOne → IntervalL2 := fun p => intervalH1MassProduct 0 (Z q) (Z p)
  have hT : AnalyticAt ℂ T q :=
    (analyticOnNhd_intervalH1MassProduct_joint 0 _ (mem_univ _)).comp
      (f := fun p : PeriodOneHminusOne => (Z q,Z p)) (analyticAt_const.prod hZ)
  let B : PeriodOneHminusOne → ℂ := fun p =>
    intervalL2Bilinear (hillHminusMassProfile 0 (p-q)) (T p)
  have heq : (fun p => (a p-a q)*M p) =ᶠ[𝓝 q] B := by
    filter_upwards [hroot] with p hp
    have hy := hillHminusDirichletColumn_H1 q (a q)
    have hz := hillHminusDirichletColumn_H1 p (a p)
    have hend : extend (hillHminusDirichletColumn q (a q)) 1*extend (hillHminusDirichletColumn p (a p)) 1 =
        extend (hillHminusDirichletColumn q (a q)) 0*extend (hillHminusDirichletColumn p (a p)) 0 := by
      simp only [hillHminusDirichletColumn_terminal,hzero,hillHminusDirichletColumn_initial,zero_mul]
    have ht := intervalH1MassProduct_eq 0 (Z q).1 (Z p).1 (Z q).2 (Z p).2
      hy.1 hz.1 hy.2 hz.2 (hillHminusDirichletDerivativeColumn_representative q (a q))
      (hillHminusDirichletDerivativeColumn_representative p (a p))
    have hi := hillHminusDirichlet_two_potential_identity q p (a q) (a p) hzero hp
    rw [hillHminusWeakPotential_eq_mass 0 (p-q) _ _ hy.1 hz.1 hy.2 hz.2 hend,hillHminusMassPotential,← ht] at hi
    exact hi
  have hU : HasFDerivAt (fun p : PeriodOneHminusOne => hillHminusMassProfile 0 (p-q))
      (hillHminusMassProfile 0) q := by
    have hh := (hillHminusMassProfile 0).hasFDerivAt.comp q ((hasFDerivAt_id q).sub_const q)
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using! hh
  have hB := intervalL2Bilinear.hasFDerivAt_of_bilinear hU hT.differentiableAt.hasFDerivAt
  have hL := (ha.differentiableAt.hasFDerivAt.sub_const (a q)).mul hM.differentiableAt.hasFDerivAt
  have hd := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h)
    ((hL.congr_of_eventuallyEq heq.symm).unique hB)
  have ht := intervalH1MassProduct_eq 0 (Z q).1 (Z q).1 (Z q).2 (Z q).2
    (hillHminusDirichletColumn_H1 q (a q)).1 (hillHminusDirichletColumn_H1 q (a q)).1
    (hillHminusDirichletColumn_H1 q (a q)).2 (hillHminusDirichletColumn_H1 q (a q)).2
    (hillHminusDirichletDerivativeColumn_representative q (a q))
    (hillHminusDirichletDerivativeColumn_representative q (a q))
  have hend : extend y 1*extend y 1 = extend y 0*extend y 0 := by
    dsimp only [y,Z]
    simp only [hillHminusDirichletColumn_terminal,hzero,hillHminusDirichletColumn_initial,zero_mul]
  have hpot := hillHminusWeakPotential_eq_mass 0 h y y
    (hillHminusDirichletColumn_H1 q (a q)).1 (hillHminusDirichletColumn_H1 q (a q)).1
    (hillHminusDirichletColumn_H1 q (a q)).2 (hillHminusDirichletColumn_H1 q (a q)).2 hend
  rw [hillHminusMassPotential,← ht] at hpot
  simp only [sub_self,map_zero,ContinuousLinearMap.precompL_apply,
    add_apply,smul_apply,smul_eq_mul,zero_add,zero_mul,zero_apply] at hd
  change hillHminusWeakPotential h y y = intervalL2Bilinear (hillHminusMassProfile 0 h) (T q) at hpot
  have hout : fderiv ℂ a q h*M q = hillHminusWeakPotential h y y := by
    calc
      _ = M q*fderiv ℂ a q h := mul_comm _ _
      _ = intervalL2Bilinear (hillHminusMassProfile 0 h) (T q) := hd
      _ = hillHminusWeakPotential h y y := hpot.symm
  exact hout

theorem hillHminusDirichletColumn_square_integral_ne_zero
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (lambda : ℂ)
    (hz : hillHminusDirichlet q lambda = 0) :
    (∫ s in (0 : ℝ)..1, extend (hillHminusDirichletColumn q lambda) s*
      extend (hillHminusDirichletColumn q lambda) s) ≠ 0 :=
  (hillHminusMiuraChartAt q).dirichlet_column_square_integral_ne_zero q
    (mem_hillHminusMiuraChartAt q) hr lambda hz

theorem hillHminusDirichlet_branch_fderiv
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (a : PeriodOneHminusOne → ℂ) (ha : AnalyticAt ℂ a q)
    (hzero : hillHminusDirichlet q (a q) = 0)
    (hroot : ∀ᶠ p in 𝓝 q, hillHminusDirichlet p (a p) = 0) (h : PeriodOneHminusOne) :
    fderiv ℂ a q h =
      hillHminusWeakPotential h (hillHminusDirichletColumn q (a q)) (hillHminusDirichletColumn q (a q))/
        (∫ s in (0 : ℝ)..1, extend (hillHminusDirichletColumn q (a q)) s*
          extend (hillHminusDirichletColumn q (a q)) s) := by
  apply (eq_div_iff (hillHminusDirichletColumn_square_integral_ne_zero q hr (a q) hzero)).mpr
  exact hillHminusDirichlet_branch_differential q a ha hzero hroot h

theorem exists_hillHminusDirichletEnergy_analytic_extension_with_fderiv
    (q : PeriodOneRealHminusOne) (n : ℕ+) :
    ∃ a : PeriodOneHminusOne → ℂ, AnalyticAt ℂ a q.val ∧
      a q.val = (hillHminusDirichletEnergy q.val q.property n : ℂ) ∧
      (∀ᶠ p in 𝓝 q.val, hillHminusDirichlet p (a p) = 0) ∧
      (∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q,
        a p.val = (hillHminusDirichletEnergy p.val p.property n : ℂ)) ∧
      ∀ h : PeriodOneHminusOne, fderiv ℂ a q.val h =
        hillHminusWeakPotential h
          (hillHminusDirichletColumn q.val (hillHminusDirichletEnergy q.val q.property n))
          (hillHminusDirichletColumn q.val (hillHminusDirichletEnergy q.val q.property n))/
        (∫ s in (0 : ℝ)..1,
          extend (hillHminusDirichletColumn q.val (hillHminusDirichletEnergy q.val q.property n)) s*
          extend (hillHminusDirichletColumn q.val (hillHminusDirichletEnergy q.val q.property n)) s) := by
  obtain ⟨a,ha,haq,hroot,hmatch⟩ := exists_hillHminusDirichletEnergy_analytic_extension q n
  refine ⟨a,ha,haq,hroot,hmatch,?_⟩
  intro h
  have hz : hillHminusDirichlet q.val (a q.val) = 0 := by
    rw [haq]
    exact hillHminusDirichletEnergy_zero q.val q.property n
  simpa only [haq] using hillHminusDirichlet_branch_fderiv q.val q.property a ha hz hroot h

end NLS.KdV
