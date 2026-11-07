import NLS.KdV.HillProductEquationAnalytic
import NLS.KdV.HminusOneHillProductJointColumns

/-! Actual derivatives of the ASSEMBLED Banach period map. Its lp-data
Jacobian is a bounded operator and is jointly analytic; its matrix
columns are the literal verified native contour columns. Invertibility
at general nonzero sources is not inferred from this identification. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem fderiv_equation_apply (P : HillProductEquationPatch) (n m : ℕ+)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) (ht : t ∈ P.inputDomain)
    (h : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) :
    (fderiv ℂ (P.equation n) t h) m = fderiv ℂ (P.row n m) t h := by
  let ev := lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m
  have hc := ev.hasFDerivAt.comp t (P.analytic_equation n t ht).differentiableAt.hasFDerivAt
  have he : (fun s => P.equation n s m) =ᶠ[𝓝 t] P.row n m := by
    filter_upwards [P.inputDomain_open.mem_nhds ht] with s hs
    exact P.equation_apply n m s hs
  have hf := hc.fderiv
  change fderiv ℂ (fun s => P.equation n s m) t = ev.comp (fderiv ℂ (P.equation n) t) at hf
  rw [he.fderiv_eq] at hf
  exact (congrArg (fun L : (lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) →L[ℂ] ℂ => L h) hf).symm

def sequenceJacobian (P : HillProductEquationPatch) (n : ℕ+)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) :
    lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2 :=
  (fderiv ℂ (P.equation n) t).comp (ContinuousLinearMap.inl ℂ (lp (fun _ : ℕ+ => ℂ) 2) PeriodOneHminusOne)

theorem analytic_sequenceJacobian (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.sequenceJacobian n) P.inputDomain := by
  let C : ((lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) →L[ℂ]
      (lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) :=
    (ContinuousLinearMap.compL ℂ (lp (fun _ : ℕ+ => ℂ) 2)
      (lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) (lp (fun _ : ℕ+ => ℂ) 2)).flip
      (ContinuousLinearMap.inl ℂ (lp (fun _ : ℕ+ => ℂ) 2) PeriodOneHminusOne)
  exact C.comp_analyticOnNhd (P.analytic_equation n).fderiv

theorem sequenceJacobian_coordinate (P : HillProductEquationPatch) (n m r : ℕ+)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (q : PeriodOneHminusOne) (ht : (d,q) ∈ P.inputDomain)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))
    (ha : D.center = P.centers ((m:ℕ):ℤ)) (hR : D.radius = P.radii ((m:ℕ):ℤ)) :
    P.sequenceJacobian n (d,q) (lp.single 2 r 1) m =
      if m = n then (if n = r then 1 else 0) else
        hillPeriodEquationWeight n m*hillEnergyProductPeriodColumn n r
          (P.parent.parent.miuraBall.actionBall.shift:ℂ) (P.sourcePsi q) D d := by
  change (fderiv ℂ (P.equation n) (d,q) (lp.single 2 r 1,0)) m = _
  rw [P.fderiv_equation_apply n m (d,q) ht]
  exact P.parent.fderiv_productEquationRow_coordinate n m r _ _ P.source P.subset
    (P.periods_analytic n ((m:ℕ):ℤ)) d q ht.2 D ha hR

end NLS.KdV.HillProductEquationPatch
