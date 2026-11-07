import NLS.KdV.HminusOneHillProductEquationRows

/-! ACTUAL full Frechet columns of the native complex Hill equation
rows, with source directions held at zero. The columns are the literal
filled product-derivative contour integrals. No real-source restriction
or zero-factor division is used. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hasDerivAt_hillZeroCoordinateShift (r : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    HasDerivAt (hillZeroCoordinateShift r d) (lp.single 2 r 1 : lp (fun _ : ℕ+ => ℂ) 2) z := by
  simpa only [hillZeroCoordinateShift,zero_add,one_smul] using!
    (hasDerivAt_const z d).add ((hasDerivAt_id z).smul_const
      (lp.single 2 r 1 : lp (fun _ : ℕ+ => ℂ) 2))

namespace HillHminusPsiBall

theorem fderiv_productPeriod_coordinate (B : HillHminusPsiBall) (n r : ℕ+) (a : ℝ) (R : ℝ)
    (U : Set PeriodOneHminusOne)
    (hP : AnalyticOnNhd ℂ (B.productPeriod n a R) (univ ×ˢ U))
    (d : lp (fun _ : ℕ+ => ℂ) 2) (q : PeriodOneHminusOne) (hq : q ∈ U) (k : ℤ)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) k)
    (ha : D.center = a) (hR : D.radius = R) :
    fderiv ℂ (B.productPeriod n a R) (d,q) (lp.single 2 r 1,0) =
      hillEnergyProductPeriodColumn n r (B.parent.miuraBall.actionBall.shift:ℂ)
        (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) D d := by
  let L : ℂ → lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne :=
    fun w => (hillZeroCoordinateShift r d w,q)
  have hL : HasDerivAt L (lp.single 2 r 1,0) 0 :=
    (hasDerivAt_hillZeroCoordinateShift r d 0).prodMk (hasDerivAt_const 0 q)
  have hF : HasFDerivAt (B.productPeriod n a R) (fderiv ℂ (B.productPeriod n a R) (d,q)) (L 0) := by
    simpa only [L,hillZeroCoordinateShift,zero_smul,add_zero] using
      (hP (d,q) ⟨mem_univ _,hq⟩).differentiableAt.hasFDerivAt
  have hc := hF.comp_hasDerivAt 0 hL
  have he : B.productPeriod n a R ∘ L = fun w =>
      hillEnergyProductFixedPeriod n (B.parent.miuraBall.actionBall.shift:ℂ)
        (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) D (hillZeroCoordinateShift r d w) := by
    funext w
    rw [← ha,← hR]
    rfl
  rw [he] at hc
  exact hc.unique (hasDerivAt_hillEnergyProductFixedPeriod_coordinate n r _ _ D d 0)

theorem fderiv_productEquationRow_coordinate (B : HillHminusPsiBall) (n m r : ℕ+) (a : ℝ) (R : ℝ)
    (U : Set PeriodOneHminusOne) (hUB : U ⊆ B.source)
    (hP : AnalyticOnNhd ℂ (B.productPeriod n a R) (univ ×ˢ U))
    (d : lp (fun _ : ℕ+ => ℂ) 2) (q : PeriodOneHminusOne) (hq : q ∈ U)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ))
    (ha : D.center = a) (hR : D.radius = R) :
    fderiv ℂ (B.productEquationRow n m a R) (d,q) (lp.single 2 r 1,0) =
      if m = n then (if n = r then 1 else 0) else
        hillPeriodEquationWeight n m*hillEnergyProductPeriodColumn n r
          (B.parent.miuraBall.actionBall.shift:ℂ)
          (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) D d := by
  by_cases hmn : m = n
  · rw [if_pos hmn]
    let L : ℂ → lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne :=
      fun w => (hillZeroCoordinateShift r d w,q)
    have hL : HasDerivAt L (lp.single 2 r 1,0) 0 :=
      (hasDerivAt_hillZeroCoordinateShift r d 0).prodMk (hasDerivAt_const 0 q)
    have hF : HasFDerivAt (B.productEquationRow n m a R)
        (fderiv ℂ (B.productEquationRow n m a R) (d,q)) (L 0) := by
      simpa only [L,hillZeroCoordinateShift,zero_smul,add_zero] using
        (B.analytic_productEquationRow n m a R U hUB hP (d,q) ⟨mem_univ _,hq⟩).differentiableAt.hasFDerivAt
    have hc := hF.comp_hasDerivAt 0 hL
    have he : B.productEquationRow n m a R ∘ L = fun w =>
        hillZeroCoordinateShift r d w n-
          (B.parent.miuraBall.energyMidpoint n q-((Real.pi:ℂ)*(n:ℕ))^2)/(n:ℕ) := by
      funext w
      simp only [Function.comp_def,L,productEquationRow,if_pos hmn]
    rw [he] at hc
    have hv := (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_hillZeroCoordinateShift r d 0)
    have hconst := hv.sub_const ((B.parent.miuraBall.energyMidpoint n q-((Real.pi:ℂ)*(n:ℕ))^2)/(n:ℕ))
    have hh := hc.unique hconst
    change fderiv ℂ (B.productEquationRow n m a R) (d,q) (lp.single 2 r 1,0) =
      (lp.single 2 r 1 : lp (fun _ : ℕ+ => ℂ) 2) n at hh
    simpa only [lp.single_apply,Pi.single_apply] using hh
  · rw [if_neg hmn]
    have he : B.productEquationRow n m a R = fun t => hillPeriodEquationWeight n m*B.productPeriod n a R t := by
      funext t
      simp only [productEquationRow,if_neg hmn]
    have hd := (hP (d,q) ⟨mem_univ _,hq⟩).differentiableAt.hasFDerivAt.const_mul (hillPeriodEquationWeight n m)
    rw [← he] at hd
    rw [hd.fderiv]
    change hillPeriodEquationWeight n m*(fderiv ℂ (B.productPeriod n a R) (d,q) (lp.single 2 r 1,0)) = _
    rw [B.fderiv_productPeriod_coordinate n r a R U hP d q hq ((m:ℕ):ℤ) D ha hR]

theorem analytic_productEquationRow_column (B : HillHminusPsiBall) (n m r : ℕ+) (a : ℝ) (R : ℝ)
    (U : Set PeriodOneHminusOne)
    (hrow : AnalyticOnNhd ℂ (B.productEquationRow n m a R) (univ ×ˢ U)) :
    AnalyticOnNhd ℂ (fun t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne =>
      fderiv ℂ (B.productEquationRow n m a R) t (lp.single 2 r 1,0)) (univ ×ˢ U) := by
  let ev : ((lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (lp.single 2 r 1,0)
  intro t ht
  exact (ev.analyticAt _).comp (hrow.fderiv t ht)

end HillHminusPsiBall
end NLS.KdV
