import NLS.KdV.HillOnIndexActionPhaseCharts
import NLS.KdV.HillOffIndexActionVelocity
import NLS.KdV.HillOffIndexCorrectionGardnerLimit

/-! Actual on-index phase/action variation through zero-sheet
terminals of an open selected gap. The same actual fixed action
circle controls all divisor indices and the complete correction. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

def completePhase (C : HillPhysicalOnIndexPhaseChart P n) (q : PeriodOneHminusOne) : ℂ :=
  C.phase q+hillHminusOffIndexAbelianCorrection n q

theorem analytic_completePhase (C : HillPhysicalOnIndexPhaseChart P n) :
    AnalyticOnNhd ℂ C.completePhase (C.source ∩ hillHminusOffIndexAnalyticDomain) :=
  (C.phase_analytic.mono inter_subset_left).add
    ((analyticOnNhd_hillHminusOffIndexAbelianCorrection n).mono inter_subset_right)

theorem phase_action_of_analytic_Dirichlet_velocity (C : HillPhysicalOnIndexPhaseChart P n)
    (U : Set PeriodOneHminusOne) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : U.Nonempty) (hsub : U ⊆ C.source) (k : ℕ+) (V : PeriodOneHminusOne → ℂ)
    (hV : AnalyticOnNhd ℂ V U)
    (hvelocity : ∀ p ∈ U, NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n)
      (hillHminusCanonicalAction k) p = hillHminusDirichletSheet n p*V p) :
    ∀ p ∈ U, NLS.Poisson.hminusGardnerBracket C.phase (hillHminusCanonicalAction k) p =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n p,p)*V p := by
  have hd := hsub.trans C.source_subset_dirichlet
  have hp := hsub.trans C.source_subset_psi
  have ha := hp.trans hillHminusCanonicalPsiDomain_subset_actionDomain
  have hpsi : AnalyticOnNhd ℂ (fun p => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n p,p)) U := by
    intro p hpu
    exact (analyticOnNhd_hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n p,p)
      ⟨mem_univ _,hp hpu⟩).comp
        (f := fun b : PeriodOneHminusOne => (hillHminusCanonicalDirichlet n b,b))
        ((analyticOnNhd_hillHminusCanonicalDirichlet n p (hd hpu)).prod analyticAt_id)
  apply hillHminusDirichletSheet_cancel_analytic n U hU hconn hne hd
    (NLS.Poisson.hminusGardnerBracket C.phase (hillHminusCanonicalAction k))
    (fun p => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n p,p)*V p)
    (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _ (C.phase_analytic.mono hsub)
      ((analyticOnNhd_hillHminusCanonicalAction k).mono ha)) (hpsi.mul hV)
  intro p hpu
  have he := C.phase_action_Gardner_cleared k p (hsub hpu)
  rw [hvelocity p hpu] at he
  linear_combination he

theorem exists_local_action_velocity (C : HillPhysicalOnIndexPhaseChart P n)
    (B : HillHminusMiuraActionBall) (k : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ C.source) (hqB : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧ ∃ r : ℝ, 0 < r ∧
      ball q r ⊆ (C.source ∩ B.source) ∩ hillHminusOffIndexAnalyticDomain ∧
      (∀ p ∈ ball q r, sphere a R ⊆ sourceCanonicalRootDomain (by norm_num) (by norm_num) (B.diracSource p)) ∧
      (∀ m : ℕ+, AnalyticOnNhd ℂ (B.dirichletContourVelocity m a R) (ball q r) ∧
        (∀ p ∈ ball q r, NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
          (hillHminusCanonicalAction k) p = hillHminusDirichletSheet m p*B.dirichletContourVelocity m a R p) ∧
        ∀ j : ℕ+, m ≠ j → ∀ p ∈ ball q r,
          NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue j m)
            (hillHminusCanonicalAction k) p =
            hillHminusCanonicalPsi j (hillHminusCanonicalDirichlet m p,p)*B.dirichletContourVelocity m a R p) ∧
      ∀ p ∈ ball q r, NLS.Poisson.hminusGardnerBracket C.phase (hillHminusCanonicalAction k) p =
        hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n p,p)*B.dirichletContourVelocity n a R p := by
  obtain ⟨a,R,hR,r,hrpos,hsub,hcircle,hvelocity⟩ := B.exists_local_offIndex_action_velocity k q hqB hr
  obtain ⟨s,hs,hsmall⟩ := Metric.mem_nhds_iff.mp
    (((isOpen_ball.inter C.source_open).inter isOpen_hillHminusOffIndexAnalyticDomain).mem_nhds
      ⟨⟨mem_ball_self hrpos,hq⟩,real_mem_hillHminusOffIndexAnalyticDomain q hr⟩)
  have hsource : ball q s ⊆ (C.source ∩ B.source) ∩ hillHminusOffIndexAnalyticDomain :=
    fun p hp => ⟨⟨(hsmall hp).1.2,(hsub (hsmall hp).1.1).1⟩,(hsmall hp).2⟩
  have hvel : ∀ m : ℕ+, AnalyticOnNhd ℂ (B.dirichletContourVelocity m a R) (ball q s) ∧
      (∀ p ∈ ball q s, NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
        (hillHminusCanonicalAction k) p = hillHminusDirichletSheet m p*B.dirichletContourVelocity m a R p) ∧
      ∀ j : ℕ+, m ≠ j → ∀ p ∈ ball q s,
        NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue j m)
          (hillHminusCanonicalAction k) p =
          hillHminusCanonicalPsi j (hillHminusCanonicalDirichlet m p,p)*B.dirichletContourVelocity m a R p := by
    intro m
    have hm := hvelocity m
    exact ⟨hm.1.mono (fun p hp => (hsmall hp).1.1),
      (fun p hp => hm.2.1 p (hsmall hp).1.1),
      (fun j hmj p hp => hm.2.2 j hmj p (hsmall hp).1.1)⟩
  refine ⟨a,R,hR,s,hs,hsource,(fun p hp => hcircle p (hsmall hp).1.1),hvel,?_⟩
  exact C.phase_action_of_analytic_Dirichlet_velocity (ball q s) isOpen_ball
    (convex_ball q s).isPreconnected ⟨q,mem_ball_self hs⟩ (fun p hp => (hsource hp).1.1)
    k (B.dirichletContourVelocity n a R) (hvel n).1 (hvel n).2.1

end NLS.KdV.HillPhysicalOnIndexPhaseChart
