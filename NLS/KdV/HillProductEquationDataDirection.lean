import NLS.KdV.HillProductEquationDerivative
import NLS.KdV.HillProductEquationRealDiagonal
import NLS.KdV.HillProductDataPeriodDerivative

/-! Every full l2 direction of the ACTUAL bounded Hill Jacobian has
the literal period-variation formula, including the exact midpoint row. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem sequenceJacobian_data_direction (P : HillProductEquationPatch) (n m : ℕ+)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (q : PeriodOneHminusOne) (ht : (d,q) ∈ P.inputDomain)
    (hr : IsRealPeriodOneHminusOne q)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))
    (ha : D.center = P.centers ((m:ℕ):ℤ)) (hR : D.radius = P.radii ((m:ℕ):ℤ))
    (h : lp (fun _ : ℕ+ => ℂ) 2) :
    P.sequenceJacobian n (d,q) h m = if m = n then h n else
      hillPeriodEquationWeight n m*((2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),
        (2*z*hillEnergyProductDataVariation n d h (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)))/
          sourceCanonicalRoot (by norm_num) (by norm_num) (P.sourcePsi q) z)) := by
  change (fderiv ℂ (P.equation n) (d,q) (h,0)) m = _
  rw [P.fderiv_equation_apply n m (d,q) ht]
  have hrow : HasFDerivAt (P.row n m) (fderiv ℂ (P.row n m) (d,q)) (d,q) :=
    (P.analytic_row n m (d,q) ⟨mem_univ _,ht.2⟩).differentiableAt.hasFDerivAt
  have hi : HasFDerivAt (fun b : lp (fun _ : ℕ+ => ℂ) 2 => (b,q))
      (ContinuousLinearMap.inl ℂ (lp (fun _ : ℕ+ => ℂ) 2) PeriodOneHminusOne) d :=
    hasFDerivAt_prodMk_left d q
  have hc : HasFDerivAt (fun b : lp (fun _ : ℕ+ => ℂ) 2 => P.row n m (b,q))
      ((fderiv ℂ (P.row n m) (d,q)).comp (ContinuousLinearMap.inl ℂ (lp (fun _ : ℕ+ => ℂ) 2) PeriodOneHminusOne)) d := by
    exact hrow.comp d hi
  have hh : fderiv ℂ (P.row n m) (d,q) (h,0) =
      fderiv ℂ (fun b => P.row n m (b,q)) d h := by
    exact (congrArg (fun L : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] ℂ => L h) hc.fderiv).symm
  rw [hh]
  by_cases hmn : m = n
  · rw [if_pos hmn]
    have he : (fun b => P.row n m (b,q)) = fun b =>
        b n-(P.parent.parent.miuraBall.energyMidpoint n q-((Real.pi:ℂ)*(n:ℕ))^2)/(n:ℕ) := by
      funext b
      rw [P.row_eq_native]
      simp only [HillHminusPsiBall.productEquationRow,if_pos hmn]
    rw [he]
    exact congrArg (fun L : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] ℂ => L h)
      (((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).hasFDerivAt.sub_const
        ((P.parent.parent.miuraBall.energyMidpoint n q-((Real.pi:ℂ)*(n:ℕ))^2)/(n:ℕ))).fderiv)
  · rw [if_neg hmn]
    have he : (fun b => P.row n m (b,q)) = fun b => hillPeriodEquationWeight n m*
        hillEnergyProductFixedPeriod n (P.parent.parent.miuraBall.actionBall.shift:ℂ) (P.sourcePsi q) D b := by
      funext b
      rw [P.row_eq_native]
      simp only [HillHminusPsiBall.productEquationRow,if_neg hmn]
      rw [← ha,← hR,P.parent.productPeriod_eq_fixed n ((m:ℕ):ℤ) q D]
      rfl
    rw [he]
    let B := P.parent.parent.miuraBall.actionBall
    have hb := (P.parent.subset (P.subset ht.2)).1
    let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hb hr⟩
    have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) := (hillMiuraRealSource u).property
    have hf := ((analyticOnNhd_hillEnergyProductFixedPeriod n (B.shift:ℂ) (P.sourcePsi q) hreal D d
      (mem_univ _)).differentiableAt.hasFDerivAt).const_mul (hillPeriodEquationWeight n m)
    rw [hf.fderiv]
    change hillPeriodEquationWeight n m*(fderiv ℂ (hillEnergyProductFixedPeriod n (B.shift:ℂ) (P.sourcePsi q) D) d h) = _
    rw [fderiv_hillEnergyProductFixedPeriod_data n (B.shift:ℂ) (P.sourcePsi q) hreal D d h]

theorem sequenceJacobian_kernel_omitted_zero (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (h : lp (fun _ : ℕ+ => ℂ) 2)
    (hk : P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) h = 0) : h n = 0 := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((n:ℕ):ℤ)
    (P.centers ((n:ℕ):ℤ)) (P.radii ((n:ℕ):ℤ)) (P.radii_pos ((n:ℕ):ℤ)) (P.discs_eq ((n:ℕ):ℤ))
  have he := P.sequenceJacobian_data_direction n n _ q (P.actual_real_graph_mem q hq hr n) hr D rfl rfl h
  rw [if_pos rfl,hk] at he
  exact he.symm

theorem sequenceJacobian_kernel_retained_period_zero (P : HillProductEquationPatch) (n m : ℕ+)
    (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (h : lp (fun _ : ℕ+ => ℂ) 2)
    (hk : P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) h = 0)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))
    (ha : D.center = P.centers ((m:ℕ):ℤ)) (hR : D.radius = P.radii ((m:ℕ):ℤ)) :
    (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),
      (2*z*hillEnergyProductDataVariation n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩) h
        (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)))/
          sourceCanonicalRoot (by norm_num) (by norm_num) (P.sourcePsi q) z) = 0 := by
  have he := P.sequenceJacobian_data_direction n m _ q (P.actual_real_graph_mem q hq hr n) hr D ha hR h
  rw [if_neg hmn,hk] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (hillPeriodEquationWeight_ne_zero n m hmn)

end NLS.KdV.HillProductEquationPatch
