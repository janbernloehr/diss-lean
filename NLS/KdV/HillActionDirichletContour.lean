import NLS.KdV.HillCanonicalActionGradient
import NLS.KdV.HillFilledMixedGardner

/-! The actual action/Dirichlet bracket is a genuine contour integral
of the filled Dirichlet quotient. No gap or moving energy pole is
divided out. Every real H-minus-one source, including closed gaps,
has an actual Miura contour computing the formula. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

def hillMiuraActionDirichletIntegrand (n : ℕ+) (q : PeriodOneHminusOne) (u : Coeff 2) (c z : ℂ) : ℂ :=
  (z/sourceCanonicalRoot (by simp) (by norm_num) (hillMiuraDiagonal u) z)*
    hillHminusDirichletFilledQuotient n (z^2-c,q)

theorem analyticOnNhd_hillMiuraActionDirichletIntegrand
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) (u : Coeff 2) (c : ℂ) :
    AnalyticOnNhd ℂ (hillMiuraActionDirichletIntegrand n q u c)
      (sourceCanonicalRootDomain (by simp) (by norm_num) (hillMiuraDiagonal u)) := by
  intro z hz
  have hQ := (analyticOnNhd_hillHminusDirichletFilledQuotient n (z^2-c,q) ⟨mem_univ _,hq⟩).comp
    (f := fun w : ℂ => (w^2-c,q)) (((analyticAt_id.pow 2).sub analyticAt_const).prod analyticAt_const)
  exact (analyticAt_id.div
    (sourceCanonicalRoot_analyticOnNhd (by simp) (by norm_num) (hillMiuraDiagonal u) z hz)
    (sourceCanonicalRoot_ne_zero_off_gaps (by simp) (by norm_num) (hillMiuraDiagonal u) z hz)).mul hQ

theorem HillHminusMiuraActionBall.exists_action_Dirichlet_bracket_circle
    (B : HillHminusMiuraActionBall) (m n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ B.source) (hreal : IsRealPeriodOneHminusOne q) :
    ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧
      CircleIntegrable (hillMiuraActionDirichletIntegrand n q (B.lift q) (B.shift : ℂ)) a R ∧
      deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet n q)*
        NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalAction m) (hillHminusCanonicalDirichlet n) q=
        hillHminusDirichletSheet n q*(Real.pi : ℂ)⁻¹*
          (∮ z in C(a,R), hillMiuraActionDirichletIntegrand n q (B.lift q) (B.shift : ℂ) z) := by
  have hdir := real_mem_hillHminusCanonicalDirichletDomain q hreal
  obtain ⟨a,R,hR,hcircle,hpoint⟩ := B.exists_action_gradient_circle m q hq hreal
  have hci : CircleIntegrable (hillMiuraActionDirichletIntegrand n q (B.lift q) (B.shift : ℂ)) a R :=
    ((analyticOnNhd_hillMiuraActionDirichletIntegrand n q hdir _ _).continuousOn.mono hcircle).circleIntegrable hR.le
  have hb : NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalAction m) (hillHminusCanonicalDirichlet n) q=
      -(2*(Real.pi : ℂ)⁻¹)*(∮ z in C(a,R), z*
        NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p (z^2-(B.shift : ℂ)))
          (hillHminusCanonicalDirichlet n) q/
        sourceCanonicalRoot (by simp) (by norm_num) (hillMiuraDiagonal (B.lift q)) z) := by
    rw [← NLS.Poisson.fderiv_apply_gardnerHamiltonianVector,hpoint]
    congr 1
    apply circleIntegral.integral_congr hR.le
    intro z _
    dsimp only [hillHminusDiscriminantCotangent]
    rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  have hi : (2*deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet n q))*
      (∮ z in C(a,R), z*
        NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p (z^2-(B.shift : ℂ)))
          (hillHminusCanonicalDirichlet n) q/
        sourceCanonicalRoot (by simp) (by norm_num) (hillMiuraDiagonal (B.lift q)) z)=
      -hillHminusDirichletSheet n q*
        (∮ z in C(a,R), hillMiuraActionDirichletIntegrand n q (B.lift q) (B.shift : ℂ) z) := by
    rw [← circleIntegral.integral_const_mul,← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR.le
    intro z _
    dsimp only [hillMiuraActionDirichletIntegrand]
    linear_combination (z/sourceCanonicalRoot (by simp) (by norm_num) (hillMiuraDiagonal (B.lift q)) z)*
      hillHminus_filled_discriminant_Dirichlet_Gardner n q hdir (z^2-(B.shift : ℂ))
  refine ⟨a,R,hR,hci,?_⟩
  linear_combination deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet n q)*hb-(Real.pi : ℂ)⁻¹*hi

theorem exists_hillHminus_action_Dirichlet_bracket_contour
    (q : PeriodOneHminusOne) (hreal : IsRealPeriodOneHminusOne q) (m n : ℕ+) :
    ∃ u : Coeff 2, ∃ c : ℂ, periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c) ∧
      ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧
        CircleIntegrable (hillMiuraActionDirichletIntegrand n q u c) a R ∧
        deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet n q)*
          NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalAction m) (hillHminusCanonicalDirichlet n) q=
          hillHminusDirichletSheet n q*(Real.pi : ℂ)⁻¹*
            (∮ z in C(a,R), hillMiuraActionDirichletIntegrand n q u c z) := by
  obtain ⟨B,hB⟩ := exists_hillHminusMiuraActionBall q hreal
  obtain ⟨a,R,hR,hci,hformula⟩ := B.exists_action_Dirichlet_bracket_circle m n q hB hreal
  exact ⟨B.lift q,B.shift,B.image q hB,a,R,hR,hci,hformula⟩

end NLS.KdV
