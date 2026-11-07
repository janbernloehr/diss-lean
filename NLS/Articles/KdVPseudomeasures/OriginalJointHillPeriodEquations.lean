import NLS.Articles.KdVPseudomeasures.OriginalHillProductJacobian
import NLS.KdV.HminusOneHillProductJointColumns

/-! Near EVERY original physical real H-minus-one potential, ONE
complex native source neighborhood and genuine fixed circle family
support ALL original weighted Hill period rows. They are jointly
analytic in independent FULL inverse-index l2 zero data and source;
the actual original real zero sequences solve every row. This is a
scalar-row family, not yet an assembled source-joint lp-valued map. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem exists_original_joint_Hill_period_equations (q₀ : OriginalHminusOnePotential) :
    ∃ B : HillHminusPsiBall, B.center = originalPeriodOneCoefficients q₀ ∧
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ originalPeriodOneCoefficients q₀ ∈ U ∧ U ⊆ B.source ∧
    ∃ a R : ℤ → ℝ, (∀ k : ℤ, 0 < R k) ∧
      (∀ q ∈ U, ∀ k : ℤ,
        ∃ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
          (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) k,
          D.center = a k ∧ D.radius = R k) ∧
      (∀ n m : ℕ+, AnalyticOnNhd ℂ
        (B.productEquationRow n m (a ((m:ℕ):ℤ)) (R ((m:ℕ):ℤ))) (univ ×ˢ U)) ∧
      (∀ n m r : ℕ+, AnalyticOnNhd ℂ
        (fun t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne =>
          fderiv ℂ (B.productEquationRow n m (a ((m:ℕ):ℤ)) (R ((m:ℕ):ℤ))) t (lp.single 2 r 1,0))
        (univ ×ˢ U)) ∧
      ∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ U → ∀ n m : ℕ+,
        B.productEquationRow n m (a ((m:ℕ):ℤ)) (R ((m:ℕ):ℤ))
          (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q) = 0 := by
  obtain ⟨B,hB,U,hU,hq,hUB,a,R,hR,hC,_,hA,hZ⟩ := exists_hminus_hill_product_equation_chart
    (originalPeriodOneCoefficients q₀) (originalPeriodOneCoefficients_real q₀)
  refine ⟨B,hB,U,hU,hq,hUB,a,R,hR,hC,hA,?_,?_⟩
  · intro n m r
    exact B.analytic_productEquationRow_column n m r _ _ U (hA n m)
  · intro q hq n m
    exact hZ (originalPeriodOneCoefficients q) hq (originalPeriodOneCoefficients_real q) n m

end NLS.Articles.KdVPseudomeasures
