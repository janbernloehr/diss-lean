import NLS.KdV.HillPsiArbitraryShiftGrowth
import NLS.ComplexAnalysis.QuadraticLiftUniqueness
import NLS.KdV.MiuraOddPositivePeriods

/-! Different-shift energy numerator uniqueness REDUCED to actual
common-circle periods. Entire analyticity and translated growth are
proved inputs. The common-period hypothesis is explicit: transport
between different chart cycles is not supplied by this theorem. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV
namespace HillHminusDirichletBall

theorem psiNumerator_eq_of_common_periods (B C : HillHminusDirichletBall) (A D : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (n : ℕ+) (c : ℂ)
    (hperiod : ∀ m : ℤ, ∃ T : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val) m,
      (∮ z in C((T.center:ℂ),T.radius),
        (2*z*(B.psiNumerator A n (z^2-c,q)-C.psiNumerator D n (z^2-c,q)))/
          sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) z) = 0) :
    (fun E : ℂ => B.psiNumerator A n (E,q)) = (fun E : ℂ => C.psiNumerator D n (E,q)) := by
  let F : ℂ → ℂ := fun z => 2*z*(B.psiNumerator A n (z^2-c,q)-C.psiNumerator D n (z^2-c,q))
  have hF : AnalyticOnNhd ℂ F univ := by
    have he : F = (fun z => 2*z*B.psiNumerator A n (z^2-c,q)-2*z*C.psiNumerator D n (z^2-c,q)) := by
      funext z
      dsimp only [F]
      ring
    rw [he]
    exact (B.psiNumerator_arbitrary_shift_pullback_entire A q n c).sub
      (C.psiNumerator_arbitrary_shift_pullback_entire D q n c)
  choose T hT using hperiod
  have hzero : F = 0 := by
    apply section7_entire_zero_of_periods (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property F hF
      (fun m => (T m).center) (fun m => (T m).radius)
    · intro m
      exact ⟨(T m).radius_pos,(T m).gap,(T m).closedBall_subset_omittedDomain,(T m).sphere_subset_rootDomain⟩
    · exact hT
    · exact B.psiNumerator_difference_arbitrary_shift_sub_sine C A D q n c
  apply eq_of_quadratic_differential_pullback_eq _ _
    (continuousOn_univ.mp (B.psiNumerator_energy_entire A q n).continuousOn)
    (continuousOn_univ.mp (C.psiNumerator_energy_entire D q n).continuousOn) c
  intro z
  have hz := congrFun hzero z
  change 2*z*(B.psiNumerator A n (z^2-c,q)-C.psiNumerator D n (z^2-c,q)) = 0 at hz
  linear_combination hz

theorem psiNumerator_eq_of_positive_common_periods (B C : HillHminusDirichletBall) (A D : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (n : ℕ+) (c : ℂ)
    (hperiod : ∀ m : ℕ+, ∃ T : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val) ((m:ℕ):ℤ),
      (∮ z in C((T.center:ℂ),T.radius),
        (2*z*(B.psiNumerator A n (z^2-c,q)-C.psiNumerator D n (z^2-c,q)))/
          sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) z) = 0) :
    (fun E : ℂ => B.psiNumerator A n (E,q)) = (fun E : ℂ => C.psiNumerator D n (E,q)) := by
  apply B.psiNumerator_eq_of_common_periods C A D q u n c
  apply exists_all_signed_zero_periods_of_positive A u _ _ hperiod
  intro z
  simp only [neg_sq,mul_neg,neg_mul]

end HillHminusDirichletBall
end NLS.KdV
