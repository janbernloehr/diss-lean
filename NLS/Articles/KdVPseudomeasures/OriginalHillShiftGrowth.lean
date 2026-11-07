import NLS.Articles.KdVPseudomeasures.OriginalHillNumeratorZeros
import NLS.KdV.HillPsiPeriodUniqueness

/-! Arbitrary-shift growth and the exact period-uniqueness reduction
for original Hill numerator charts. The translated growth hypotheses
are PROVED. Common periods across distinct physical shifts still need
to be transported; equality between arbitrary charts is not claimed. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_numerator_difference_arbitrary_shift_growth
    (A D : MiuraHillPsiFamily) (B C : HillHminusDirichletBall)
    (q : OriginalHminusOnePotential) (n : ℕ+) (c : ℂ) :
    AnalyticOnNhd ℂ (fun E : ℂ => B.psiNumerator A n (E,originalPeriodOneCoefficients q)) univ ∧
    AnalyticOnNhd ℂ (fun E : ℂ => C.psiNumerator D n (E,originalPeriodOneCoefficients q)) univ ∧
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
        ‖(2*z*(B.psiNumerator A n (z^2-c,originalPeriodOneCoefficients q)-
          C.psiNumerator D n (z^2-c,originalPeriodOneCoefficients q)))/(-2*sin z)‖ ≤ ε :=
  ⟨B.psiNumerator_energy_entire A _ n,C.psiNumerator_energy_entire D _ n,
    B.psiNumerator_difference_arbitrary_shift_sub_sine C A D _ n c⟩

/-- No equal-shift hypothesis is needed ONCE actual common periods are proved. -/
theorem original_Hill_numerators_eq_of_common_periods
    (A D : MiuraHillPsiFamily) (B C : HillHminusDirichletBall)
    (q : OriginalHminusOnePotential) (n : ℕ+)
    (hq : originalPeriodOneCoefficients q ∈ B.psiSource A ∩ C.psiSource D)
    (hperiod : ∀ m : ℕ+, ∃ T : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.miuraBall.actionBall.lift (originalPeriodOneCoefficients q))) ((m:ℕ):ℤ),
      (∮ z in C((T.center:ℂ),T.radius),
        (2*z*(B.psiNumerator A n (z^2-(B.miuraBall.actionBall.shift:ℂ),originalPeriodOneCoefficients q)-
          C.psiNumerator D n (z^2-(B.miuraBall.actionBall.shift:ℂ),originalPeriodOneCoefficients q)))/
            sourceCanonicalRoot (by norm_num) (by norm_num)
              (hillMiuraDiagonal (B.miuraBall.actionBall.lift (originalPeriodOneCoefficients q))) z) = 0) :
    (fun E : ℂ => B.psiNumerator A n (E,originalPeriodOneCoefficients q)) =
      (fun E : ℂ => C.psiNumerator D n (E,originalPeriodOneCoefficients q)) := by
  let u : PeriodOneRealL2 := ⟨B.miuraBall.actionBall.lift (originalPeriodOneCoefficients q),
    B.miuraBall.actionBall.lift_real _ hq.1.1 (originalPeriodOneCoefficients_real q)⟩
  exact B.psiNumerator_eq_of_positive_common_periods C A D _ u n (B.miuraBall.actionBall.shift:ℂ) hperiod

end NLS.Articles.KdVPseudomeasures
