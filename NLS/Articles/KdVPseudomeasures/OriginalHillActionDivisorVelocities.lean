import NLS.Articles.KdVPseudomeasures.OriginalHillAbelianActionVariation
import NLS.KdV.HillOffIndexActionVelocity

/-! Actual analytic action/divisor velocities at every original
physical potential, including zero physical sheets and closed gaps.
The off-index Abelian action contour formula has no sheet condition.
The complete angle/action Kronecker matrix remains a further step. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

theorem original_Hill_local_analytic_action_divisor_velocities
    (q : OriginalHminusOnePotential) (k : ℕ+) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ originalPeriodOneCoefficients q ∈ U ∧
      U ⊆ hillHminusPhysicalAbelianDomain ∧
      ∃ V : ℕ+ → PeriodOneHminusOne → ℂ,
        (∀ m : ℕ+, AnalyticOnNhd ℂ (V m) U) ∧
        (∀ m : ℕ+, ∀ p ∈ U, NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
          (hillHminusCanonicalAction k) p = hillHminusDirichletSheet m p*V m p) ∧
        ∀ n m : ℕ+, m ≠ n → ∀ p ∈ U,
          NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue n m)
            (hillHminusCanonicalAction k) p =
            hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m p,p)*V m p := by
  let q₀ := originalPeriodOneCoefficients q
  have hreal : IsRealPeriodOneHminusOne q₀ := originalPeriodOneCoefficients_real q
  obtain ⟨B,hq⟩ := exists_hillHminusMiuraActionBall q₀ hreal
  obtain ⟨a,R,_,r,hr,hsub,_,hvelocity⟩ := B.exists_local_offIndex_action_velocity k q₀ hq hreal
  refine ⟨ball q₀ r,isOpen_ball,mem_ball_self hr,(fun p hp => (hsub hp).2),
    (fun m => B.dirichletContourVelocity m a R),(fun m => (hvelocity m).1),
    (fun m => (hvelocity m).2.1),?_⟩
  intro n m hmn
  exact (hvelocity m).2.2 n hmn

theorem original_Hill_offIndex_Abelian_action_bracket_contour
    (q : OriginalHminusOnePotential) (n m k : ℕ+) (hmn : m ≠ n) :
    ∃ u : Coeff 2, ∃ c : ℂ,
      periodOneMiura u=originalPeriodOneCoefficients q+periodOneL2Inclusion (lp.single 2 0 c) ∧
      ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧
        CircleIntegrable (hillMiuraActionDirichletIntegrand m (originalPeriodOneCoefficients q) u c) a R ∧
        deriv (hillHminusDirichlet (originalPeriodOneCoefficients q))
          (hillHminusCanonicalDirichlet m (originalPeriodOneCoefficients q))*
          NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue n m)
            (hillHminusCanonicalAction k) (originalPeriodOneCoefficients q) =
          -hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m (originalPeriodOneCoefficients q),
            originalPeriodOneCoefficients q)*(Real.pi:ℂ)⁻¹*
            (∮ z in C(a,R), hillMiuraActionDirichletIntegrand m (originalPeriodOneCoefficients q) u c z) :=
  exists_hillHminus_offIndex_Abelian_action_bracket_contour n m k hmn _
    (originalPeriodOneCoefficients_real q)

end NLS.Articles.KdVPseudomeasures
