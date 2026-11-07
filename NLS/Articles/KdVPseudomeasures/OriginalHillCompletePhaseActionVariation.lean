import NLS.Articles.KdVPseudomeasures.OriginalHillActionDivisorVelocities
import NLS.KdV.HillOnIndexActionContour
import NLS.KdV.HillCompletePhaseActionSeries

/-! Actual original on-index phase/action contours and the complete
local Abelian phase variation. An open ORIGINAL selected gap is the
only gap hypothesis; zero-sheet endpoints are included. The full
normalized velocity sum has not yet been evaluated as a Kronecker value. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.LpSequence
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

theorem original_Hill_onIndex_phase_action_bracket_contour
    (q : OriginalHminusOnePotential) (n k : ℕ+)
    (hgap : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0) :
    ∃ P : HillProductEquationPatch, ∃ C : HillPhysicalOnIndexPhaseChart P n,
      C.center = originalPeriodOneCoefficients q ∧ originalPeriodOneCoefficients q ∈ C.source ∧
      ∃ u : Coeff 2, ∃ c : ℂ,
        periodOneMiura u=originalPeriodOneCoefficients q+periodOneL2Inclusion (lp.single 2 0 c) ∧
        ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧
          CircleIntegrable (hillMiuraActionDirichletIntegrand n (originalPeriodOneCoefficients q) u c) a R ∧
          deriv (hillHminusDirichlet (originalPeriodOneCoefficients q))
            (hillHminusCanonicalDirichlet n (originalPeriodOneCoefficients q))*
            NLS.Poisson.hminusGardnerBracket C.phase (hillHminusCanonicalAction k) (originalPeriodOneCoefficients q) =
            -hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n (originalPeriodOneCoefficients q),
              originalPeriodOneCoefficients q)*(Real.pi:ℂ)⁻¹*
              (∮ z in C(a,R), hillMiuraActionDirichletIntegrand n (originalPeriodOneCoefficients q) u c z) := by
  have hr := originalPeriodOneCoefficients_real q
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch (originalPeriodOneCoefficients q) hr
  obtain ⟨C,hcenter,hCq⟩ := exists_hillPhysicalOnIndexPhaseChart P n (originalPeriodOneCoefficients q)
    (P.real_mem_physicalDirichletSource _ hq hr) hr hgap
  exact ⟨P,C,hcenter,hCq,C.exists_phase_action_bracket_contour k _ hCq hr⟩

theorem original_Hill_complete_local_phase_action_velocity_series
    (q : OriginalHminusOnePotential) (n k : ℕ+)
    (hgap : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0) :
    ∃ P : HillProductEquationPatch, ∃ C : HillPhysicalOnIndexPhaseChart P n,
      C.center = originalPeriodOneCoefficients q ∧
      ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ originalPeriodOneCoefficients q ∈ U ∧
        U ⊆ C.source ∩ hillHminusOffIndexAnalyticDomain ∧ AnalyticOnNhd ℂ C.completePhase U ∧
        ∃ V : ℕ+ → PeriodOneHminusOne → ℂ,
          (∀ m : ℕ+, AnalyticOnNhd ℂ (V m) U) ∧
          (∀ m : ℕ+, ∀ p ∈ U, NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
            (hillHminusCanonicalAction k) p = hillHminusDirichletSheet m p*V m p) ∧
          ∀ p ∈ U, Tendsto (fun N : ℕ =>
            hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n p,p)*V n p+
              ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
                positiveScalarExtension (hillHminusOffIndexVelocityTerm n V p) j) atTop
              (𝓝 (NLS.Poisson.hminusGardnerBracket C.completePhase (hillHminusCanonicalAction k) p)) := by
  let q₀ := originalPeriodOneCoefficients q
  have hr : IsRealPeriodOneHminusOne q₀ := originalPeriodOneCoefficients_real q
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q₀ hr
  obtain ⟨C,hcenter,hCq⟩ := exists_hillPhysicalOnIndexPhaseChart P n q₀
    (P.real_mem_physicalDirichletSource q₀ hq hr) hr hgap
  obtain ⟨B,hqB⟩ := exists_hillHminusMiuraActionBall q₀ hr
  obtain ⟨a,R,_,r,hrpos,hsub,_,hvelocity,hphase⟩ := C.exists_local_action_velocity B k q₀ hCq hqB hr
  have hsource : ball q₀ r ⊆ C.source ∩ hillHminusOffIndexAnalyticDomain :=
    fun p hp => ⟨(hsub hp).1.1,(hsub hp).2⟩
  refine ⟨P,C,hcenter,ball q₀ r,isOpen_ball,mem_ball_self hrpos,hsource,
    C.analytic_completePhase.mono hsource,(fun m => B.dirichletContourVelocity m a R),
    (fun m => (hvelocity m).1),(fun m => (hvelocity m).2.1),?_⟩
  intro p hp
  exact C.tendsto_completePhase_action_series k p (hsource hp).1 (hsource hp).2
    (fun m => B.dirichletContourVelocity m a R) (hphase p hp)
    (fun m hmn => (hvelocity m).2.2 n hmn p hp)

end NLS.Articles.KdVPseudomeasures
