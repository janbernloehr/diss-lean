import NLS.KdV.HillLocalActionDirichletVelocity
import NLS.KdV.HillDirichletSheetLocalCancellation
import NLS.KdV.HillCanonicalAbelianActionVariation

/-! Actual off-index action variations through zero sheets. A fixed
action contour defines an analytic velocity before all divisor and
numerator indices. Analytic cancellation removes the physical sheet
from the verified cleared identity, including at branch terminals. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem hillHminus_offIndex_action_of_analytic_Dirichlet_velocity
    (U : Set PeriodOneHminusOne) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : U.Nonempty) (hsub : U ⊆ hillHminusPhysicalAbelianDomain)
    (n m k : ℕ+) (hmn : m ≠ n) (V : PeriodOneHminusOne → ℂ)
    (hV : AnalyticOnNhd ℂ V U)
    (hvelocity : ∀ p ∈ U, NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
      (hillHminusCanonicalAction k) p = hillHminusDirichletSheet m p*V p) :
    ∀ p ∈ U, NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue n m)
      (hillHminusCanonicalAction k) p = hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m p,p)*V p := by
  have hd := hsub.trans hillHminusPhysicalAbelianDomain_subset_Dirichlet
  have hp := hsub.trans hillHminusPhysicalAbelianDomain_subset_Psi
  have ha := hp.trans hillHminusCanonicalPsiDomain_subset_actionDomain
  have hpsi : AnalyticOnNhd ℂ (fun p => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m p,p)) U := by
    intro p hpu
    exact (analyticOnNhd_hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m p,p)
      ⟨mem_univ _,hp hpu⟩).comp
        (f := fun b : PeriodOneHminusOne => (hillHminusCanonicalDirichlet m b,b))
        ((analyticOnNhd_hillHminusCanonicalDirichlet m p (hd hpu)).prod analyticAt_id)
  apply hillHminusDirichletSheet_cancel_analytic m U hU hconn hne hd
    (NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue n m) (hillHminusCanonicalAction k))
    (fun p => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m p,p)*V p)
    (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
      ((analyticOnNhd_hillHminusPhysicalOffIndexAbelianValue n m hmn).mono hsub)
      ((analyticOnNhd_hillHminusCanonicalAction k).mono ha)) (hpsi.mul hV)
  intro p hpu
  have he := hillHminusPhysicalOffIndexAbelianValue_action_Gardner_cleared n m k hmn p (hsub hpu)
  rw [hvelocity p hpu] at he
  linear_combination he

theorem HillHminusMiuraActionBall.exists_local_offIndex_action_velocity
    (B : HillHminusMiuraActionBall) (k : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧ ∃ r : ℝ, 0 < r ∧
      ball q r ⊆ B.source ∩ hillHminusPhysicalAbelianDomain ∧
      (∀ p ∈ ball q r, sphere a R ⊆ sourceCanonicalRootDomain (by norm_num) (by norm_num) (B.diracSource p)) ∧
      ∀ m : ℕ+, AnalyticOnNhd ℂ (B.dirichletContourVelocity m a R) (ball q r) ∧
        (∀ p ∈ ball q r, NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
          (hillHminusCanonicalAction k) p = hillHminusDirichletSheet m p*B.dirichletContourVelocity m a R p) ∧
        ∀ n : ℕ+, m ≠ n → ∀ p ∈ ball q r,
          NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue n m)
            (hillHminusCanonicalAction k) p =
            hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m p,p)*B.dirichletContourVelocity m a R p := by
  obtain ⟨a,R,hR,r,hrpos,hsub,hcircle,hvelocity⟩ := B.exists_local_action_Dirichlet_velocity k q hq hr
  obtain ⟨s,hs,hsmall⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_ball.inter isOpen_hillHminusPhysicalAbelianDomain).mem_nhds
      ⟨mem_ball_self hrpos,real_mem_hillHminusPhysicalAbelianDomain q hr⟩)
  have hsource : ball q s ⊆ B.source ∩ hillHminusPhysicalAbelianDomain :=
    fun p hp => ⟨(hsub (hsmall hp).1).1,(hsmall hp).2⟩
  refine ⟨a,R,hR,s,hs,hsource,(fun p hp => hcircle p (hsmall hp).1),?_⟩
  intro m
  have hm := hvelocity m
  have hV := hm.1.mono (fun p hp => (hsmall hp).1)
  have hv : ∀ p ∈ ball q s, NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
      (hillHminusCanonicalAction k) p = hillHminusDirichletSheet m p*B.dirichletContourVelocity m a R p :=
    fun p hp => hm.2 p (hsmall hp).1
  refine ⟨hV,hv,?_⟩
  intro n hmn
  exact hillHminus_offIndex_action_of_analytic_Dirichlet_velocity (ball q s) isOpen_ball
    (convex_ball q s).isPreconnected ⟨q,mem_ball_self hs⟩ (fun p hp => (hsource hp).2)
    n m k hmn (B.dirichletContourVelocity m a R) hV hv

theorem exists_hillHminus_offIndex_Abelian_action_bracket_contour
    (n m k : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ u : Coeff 2, ∃ c : ℂ, periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c) ∧
      ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧
        CircleIntegrable (hillMiuraActionDirichletIntegrand m q u c) a R ∧
        deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q)*
          NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue n m)
            (hillHminusCanonicalAction k) q =
          -hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*(Real.pi:ℂ)⁻¹*
            (∮ z in C(a,R), hillMiuraActionDirichletIntegrand m q u c z) := by
  obtain ⟨B,hq⟩ := exists_hillHminusMiuraActionBall q hr
  obtain ⟨a,R,hR,r,hrpos,_,hcircle,hvelocity⟩ := B.exists_local_offIndex_action_velocity k q hq hr
  have hqr : q ∈ ball q r := mem_ball_self hrpos
  have hdir := real_mem_hillHminusCanonicalDirichletDomain q hr
  have hci : CircleIntegrable (hillMiuraActionDirichletIntegrand m q (B.lift q) (B.shift:ℂ)) a R :=
    ((analyticOnNhd_hillMiuraActionDirichletIntegrand m q hdir _ _).continuousOn.mono
      (hcircle q hqr)).circleIntegrable hR.le
  refine ⟨B.lift q,B.shift,B.image q hq,a,R,hR,hci,?_⟩
  let d := deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q)
  have hd : d ≠ 0 := deriv_hillHminusCanonicalDirichlet_ne_zero m q hdir
  have hv : d*B.dirichletContourVelocity m a R q = -(Real.pi:ℂ)⁻¹*
      (∮ z in C(a,R), hillMiuraActionDirichletIntegrand m q (B.lift q) (B.shift:ℂ) z) := by
    dsimp only [HillHminusMiuraActionBall.dirichletContourVelocity]
    change d*(-(Real.pi:ℂ)⁻¹*d⁻¹*_) = _
    calc
      _ = (-(Real.pi:ℂ)⁻¹*(∮ z in C(a,R), hillMiuraActionDirichletIntegrand m q
        (B.lift q) (B.shift:ℂ) z))*(d*d⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hd,mul_one]
  have hb := (hvelocity m).2.2 n hmn q hqr
  linear_combination d*hb+hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*hv

end NLS.KdV
