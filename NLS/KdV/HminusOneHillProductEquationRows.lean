import NLS.KdV.HminusOneJointHillProductPeriods
import NLS.KdV.HillFreePeriodJacobian

/-! The ACTUAL original weighted Hill period equation rows jointly
in independent inverse-index l2 zeros and native complex H-minus-one
sources. The omitted row uses the ORIGINAL gap midpoint. One source
neighborhood supports ALL n,m and the actual real zero sequences solve
ALL rows there. No lp-valued joint-source assembly is inferred. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV
namespace HillHminusPsiBall

def productEquationRow (B : HillHminusPsiBall) (n m : ℕ+) (a : ℝ) (R : ℝ)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) : ℂ :=
  if m = n then t.1 n-(B.parent.miuraBall.energyMidpoint n t.2-((Real.pi:ℂ)*(n:ℕ))^2)/(n:ℕ)
  else hillPeriodEquationWeight n m*B.productPeriod n a R t

theorem analytic_productEquationRow (B : HillHminusPsiBall) (n m : ℕ+) (a : ℝ) (R : ℝ)
    (U : Set PeriodOneHminusOne) (hUB : U ⊆ B.source)
    (hP : AnalyticOnNhd ℂ (B.productPeriod n a R) (univ ×ˢ U)) :
    AnalyticOnNhd ℂ (B.productEquationRow n m a R) (univ ×ˢ U) := by
  intro t ht
  unfold productEquationRow
  by_cases hmn : m = n
  · simp only [if_pos hmn]
    have he := ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).analyticAt t.1).comp
      (f := Prod.fst) analyticAt_fst
    have hm := (B.parent.miuraBall.analytic_energyMidpoint n t.2 (B.subset (hUB ht.2)).1).comp
      (f := Prod.snd) analyticAt_snd
    exact he.sub ((hm.sub analyticAt_const).div_const)
  · simp only [if_neg hmn]
    exact analyticAt_const.mul (hP t ht)

theorem productEquationRow_actual_real_zeros (B : HillHminusPsiBall) (n m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ)) :
    B.productEquationRow n m D.center D.radius (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) = 0 := by
  by_cases hmn : m = n
  · subst m
    simp only [productEquationRow]
    rw [B.parent.miuraBall.energyMidpoint_eq_real n q (B.subset hq).1 hr]
    change (((hillHminusCanonicalPsiRealZero n n q hr:ℂ)-((Real.pi:ℂ)*(n:ℕ))^2)/(n:ℕ))-
      (((hillHminusLabels q hr (2*(n:ℕ)-1):ℂ)+(hillHminusLabels q hr (2*(n:ℕ)):ℂ))/2-
        ((Real.pi:ℂ)*(n:ℕ))^2)/(n:ℕ) = 0
    rw [hillHminusCanonicalPsiRealZero,dif_pos rfl]
    push_cast
    ring
  · simp only [productEquationRow,if_neg hmn]
    rw [B.productPeriod_eq_fixed n ((m:ℕ):ℤ) q D,
      B.product_off_diagonal_period_zero n m hmn q hq hr D,mul_zero]

end HillHminusPsiBall

theorem exists_hminus_hill_product_equation_chart (q₀ : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q₀) :
    ∃ B : HillHminusPsiBall, B.center = q₀ ∧
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q₀ ∈ U ∧ U ⊆ B.source ∧
    ∃ a R : ℤ → ℝ, (∀ k : ℤ, 0 < R k) ∧
      (∀ q ∈ U, ∀ k : ℤ,
        ∃ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
          (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) k,
          D.center = a k ∧ D.radius = R k) ∧
      (∀ (n : ℕ+) (k : ℤ), AnalyticOnNhd ℂ (B.productPeriod n (a k) (R k)) (univ ×ˢ U)) ∧
      (∀ n m : ℕ+, AnalyticOnNhd ℂ
        (B.productEquationRow n m (a ((m:ℕ):ℤ)) (R ((m:ℕ):ℤ))) (univ ×ˢ U)) ∧
      ∀ q ∈ U, ∀ hreal : IsRealPeriodOneHminusOne q, ∀ n m : ℕ+,
        B.productEquationRow n m (a ((m:ℕ):ℤ)) (R ((m:ℕ):ℤ))
          (hillHminusPsiZeroDisplacement n ⟨q,hreal⟩,q) = 0 := by
  obtain ⟨B,hB,U,hU,hq,hUB,a,R,hR,hC,hP⟩ := exists_hminus_hill_product_joint_period_chart q₀ hr
  refine ⟨B,hB,U,hU,hq,hUB,a,R,hR,hC,hP,?_,?_⟩
  · intro n m
    exact B.analytic_productEquationRow n m _ _ U hUB (hP n ((m:ℕ):ℤ))
  · intro q hq hreal n m
    obtain ⟨D,ha,hR⟩ := hC q hq ((m:ℕ):ℤ)
    rw [← ha,← hR]
    exact B.productEquationRow_actual_real_zeros n m q (hUB hq) hreal D

end NLS.KdV
