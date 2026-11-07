import NLS.KdV.HillProductFixedPeriods
import NLS.KdV.MiuraOddPositivePeriods
import NLS.ComplexAnalysis.QuadraticLiftUniqueness
import NLS.ZakharovShabat.Section7EntirePeriodUniqueness

/-! Literal periods of arbitrary entire Hill energy numerators and
uniqueness from all positive periods on the actual real Miura root. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillEnergyNumeratorPeriod (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k) (F : ℂ → ℂ) : ℂ :=
  (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius), (2*z*F (z^2-c))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z)

theorem circleIntegrable_hillEnergyNumerator (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F univ) :
    CircleIntegrable (fun z => (2*z*F (z^2-c))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z)
      (D.center:ℂ) D.radius := by
  apply ContinuousOn.circleIntegrable D.radius_pos.le
  intro z hz
  have hp := (hF (z^2-c) (mem_univ _)).comp (f := fun w : ℂ => w^2-c)
    ((analyticAt_id.pow 2).sub analyticAt_const)
  exact (((analyticAt_const.mul analyticAt_id).mul hp).div
    (sourceCanonicalRoot_analyticOnNhd (by norm_num) (by norm_num) ψ z (D.sphere_subset_rootDomain hz))
    (sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num) ψ z (D.sphere_subset_rootDomain hz))).continuousAt.continuousWithinAt

theorem hillEnergyNumeratorPeriod_sub (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (F G : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F univ) (hG : AnalyticOnNhd ℂ G univ) :
    hillEnergyNumeratorPeriod c ψ D (fun E => F E-G E) =
      hillEnergyNumeratorPeriod c ψ D F-hillEnergyNumeratorPeriod c ψ D G := by
  unfold hillEnergyNumeratorPeriod
  simp_rw [mul_sub,sub_div]
  rw [circleIntegral.integral_sub (circleIntegrable_hillEnergyNumerator c ψ D F hF)
    (circleIntegrable_hillEnergyNumerator c ψ D G hG)]
  ring

theorem hillEnergyNumeratorPeriod_const_mul (c : ℂ) (ψ : CoeffPair 2) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k) (A : ℂ) (F : ℂ → ℂ) :
    hillEnergyNumeratorPeriod c ψ D (fun E => A*F E) = A*hillEnergyNumeratorPeriod c ψ D F := by
  have he : (fun z => (2*z*(A*F (z^2-c)))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z) =
      (fun z => A*((2*z*F (z^2-c))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z)) := by funext z; ring
  unfold hillEnergyNumeratorPeriod
  rw [he,circleIntegral.integral_const_mul]
  ring

theorem hillEnergyNumerator_eq_zero_of_positive_periods (u : PeriodOneRealL2) (c : ℂ)
    (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ)
    (hperiod : ∀ m : ℕ+, ∃ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val) ((m:ℕ):ℤ), hillEnergyNumeratorPeriod c (hillMiuraDiagonal u.val) D P = 0)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k), ‖(2*z*P (z^2-c))/(-2*sin z)‖ ≤ ε) : P = 0 := by
  let F : ℂ → ℂ := fun z => 2*z*P (z^2-c)
  have hF : AnalyticOnNhd ℂ F univ := by
    intro z _
    exact (analyticAt_const.mul analyticAt_id).mul
      ((hP _ (mem_univ _)).comp (f := fun w : ℂ => w^2-c) ((analyticAt_id.pow 2).sub analyticAt_const))
  have hodd (z : ℂ) : F (-z) = -F z := by dsimp only [F]; rw [neg_sq]; ring
  have hpositive (m : ℕ+) : ∃ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val) ((m:ℕ):ℤ),
      (∮ z in C((D.center:ℂ),D.radius), F z/sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) z) = 0 := by
    obtain ⟨D,hD⟩ := hperiod m
    refine ⟨D,?_⟩
    exact (mul_eq_zero.mp hD).resolve_left (inv_ne_zero (by simp [Real.pi_ne_zero]))
  obtain ⟨A⟩ := nonempty_miuraHillPsiFamily
  choose D hD using exists_all_signed_zero_periods_of_positive A u F hodd hpositive
  have hzero : F = 0 := by
    apply section7_entire_zero_of_periods (by norm_num) (by norm_num) (hillMiuraDiagonal u.val)
      (hillMiuraRealSource u).property F hF (fun m => (D m).center) (fun m => (D m).radius)
    · intro m
      exact ⟨(D m).radius_pos,(D m).gap,(D m).closedBall_subset_omittedDomain,(D m).sphere_subset_rootDomain⟩
    · exact hD
    · exact hsmall
  apply eq_of_quadratic_differential_pullback_eq P (fun _ => 0)
    (continuousOn_univ.mp hP.continuousOn) continuous_const c
  intro z
  simpa only [F,Pi.zero_apply,mul_zero] using congrFun hzero z

end NLS.KdV
