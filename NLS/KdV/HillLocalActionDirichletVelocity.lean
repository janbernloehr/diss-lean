import NLS.KdV.HillFixedActionDirichletContour

/-! Actual analytic Dirichlet action velocities through zero sheets.
One fixed action circle and one native source ball precede every
Dirichlet index. The velocity factor divides only the proved nonzero
simple energy derivative, never a physical sheet or periodic gap. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV.HillHminusMiuraActionBall

def dirichletContourVelocity (B : HillHminusMiuraActionBall) (m : ℕ+) (a : ℂ) (R : ℝ)
    (q : PeriodOneHminusOne) : ℂ :=
  -(Real.pi:ℂ)⁻¹*(deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q))⁻¹*
    (∮ z in C(a,R), hillMiuraActionDirichletIntegrand m q (B.lift q) (B.shift:ℂ) z)

theorem analytic_dirichletContourVelocity (B : HillHminusMiuraActionBall)
    (W : Set (CoeffPair 2))
    (hDW : IsOpen (sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct (by norm_num) (by norm_num))
      (sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W))
    (U : Set PeriodOneHminusOne) (hU : IsOpen U) (hsub : U ⊆ hillHminusCanonicalDirichletDomain)
    (a : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : ∀ q ∈ U, ∀ z ∈ sphere a R, (z,q) ∈ B.rootJointDomain W) (m : ℕ+) :
    AnalyticOnNhd ℂ (B.dirichletContourVelocity m a R) U := by
  have hI : AnalyticOnNhd ℂ (fun q =>
      ∮ z in C(a,R), hillMiuraActionDirichletIntegrand m q (B.lift q) (B.shift:ℂ) z) U :=
    analyticOnNhd_circleIntegral_of_jointAnalytic _
      ((B.isOpen_rootJointDomain W hDW).inter (isOpen_univ.prod isOpen_hillHminusCanonicalDirichletDomain))
      (B.analytic_actionDirichletIntegrand_joint W hroot m) a R hR hU
      (fun q hq z hz => ⟨hcircle q hq z hz,mem_univ _,hsub hq⟩)
  have hd : AnalyticOnNhd ℂ (fun q =>
      deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q)) U := by
    have ha : AnalyticOnNhd ℂ (fun q => hillHminusDirichletFilledQuotient m
        (hillHminusCanonicalDirichlet m q,q)) U := by
      intro q hq
      exact (analyticOnNhd_hillHminusDirichletFilledQuotient m
        (hillHminusCanonicalDirichlet m q,q) ⟨mem_univ _,hsub hq⟩).comp
          (f := fun p : PeriodOneHminusOne => (hillHminusCanonicalDirichlet m p,p))
          ((analyticOnNhd_hillHminusCanonicalDirichlet m q (hsub hq)).prod analyticAt_id)
    simpa only [hillHminusDirichletFilledQuotient_at_root] using ha
  intro q hq
  exact (analyticAt_const.mul ((hd q hq).inv
    (deriv_hillHminusCanonicalDirichlet_ne_zero m q (hsub hq)))).mul (hI q hq)

theorem Dirichlet_action_velocity_of_cotangent_contour (B : HillHminusMiuraActionBall)
    (k m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain)
    (a : ℂ) (R : ℝ) (hR : 0 < R)
    (hcircle : sphere a R ⊆ sourceCanonicalRootDomain (by norm_num) (by norm_num) (B.diracSource q))
    (hgradient : fderiv ℂ (hillHminusCanonicalAction k) q = -(2*(Real.pi:ℂ)⁻¹) •
      (∮ z in C(a,R), hillMiuraActionCotangentIntegrand q (B.lift q) (B.shift:ℂ) z)) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m) (hillHminusCanonicalAction k) q =
      hillHminusDirichletSheet m q*B.dirichletContourVelocity m a R q := by
  let d := deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q)
  have hd : d ≠ 0 := deriv_hillHminusCanonicalDirichlet_ne_zero m q hq
  have hb := B.action_Dirichlet_bracket_of_cotangent_contour k m q hq a R hR hcircle hgradient
  rw [NLS.Poisson.hminusGardnerBracket_antisymm (hillHminusCanonicalAction k)
    (hillHminusCanonicalDirichlet m) q] at hb
  have hm : d*NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
      (hillHminusCanonicalAction k) q = -hillHminusDirichletSheet m q*(Real.pi:ℂ)⁻¹*
        (∮ z in C(a,R), hillMiuraActionDirichletIntegrand m q (B.lift q) (B.shift:ℂ) z) := by
    linear_combination -hb
  calc
    _ = d⁻¹*(d*NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
        (hillHminusCanonicalAction k) q) := by rw [← mul_assoc,inv_mul_cancel₀ hd,one_mul]
    _ = _ := by rw [hm]; dsimp only [dirichletContourVelocity,d]; ring

theorem exists_local_action_Dirichlet_velocity (B : HillHminusMiuraActionBall)
    (k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧ ∃ r : ℝ, 0 < r ∧
      ball q r ⊆ B.source ∩ hillHminusCanonicalDirichletDomain ∧
      (∀ p ∈ ball q r, sphere a R ⊆ sourceCanonicalRootDomain (by norm_num) (by norm_num) (B.diracSource p)) ∧
      ∀ m : ℕ+, AnalyticOnNhd ℂ (B.dirichletContourVelocity m a R) (ball q r) ∧
        ∀ p ∈ ball q r, NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
          (hillHminusCanonicalAction k) p = hillHminusDirichletSheet m p*B.dirichletContourVelocity m a R p := by
  obtain ⟨W,hDW,hroot,a,R,hR,r,hrpos,hsub,hcircle,hgradient⟩ := B.exists_fixed_action_gradient_contour k q hq hr
  refine ⟨a,R,hR,r,hrpos,hsub,(fun p hp z hz => (hcircle p hp z hz).2.2),?_⟩
  intro m
  refine ⟨B.analytic_dirichletContourVelocity W hDW hroot (ball q r) isOpen_ball
    (fun p hp => (hsub hp).2) a R hR.le hcircle m,?_⟩
  intro p hp
  exact B.Dirichlet_action_velocity_of_cotangent_contour k m p (hsub hp).2 a R hR
    (fun z hz => (hcircle p hp z hz).2.2) (hgradient p hp)

end NLS.KdV.HillHminusMiuraActionBall
