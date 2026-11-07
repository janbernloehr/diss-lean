import NLS.KdV.HillActionVelocitySumNormalization
import NLS.KdV.HillPrescribedActionVelocity
import NLS.KdV.HillCompletePhaseActionSeries

/-! Evaluation of the actual complete local Abelian angle/action
Gardner bracket. The selected gap is open in its actual phase chart;
physical sheets may vanish and every other gap may be closed. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

theorem completePhase_action_Gardner_of_real (C : HillPhysicalOnIndexPhaseChart P n)
    (k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    NLS.Poisson.hminusGardnerBracket C.completePhase (hillHminusCanonicalAction k) q =
      -(if k=n then (1:ℂ) else 0) := by
  have hqP := (C.subset hq).1
  obtain ⟨r,hrpos,hsub,hvelocity⟩ := P.exists_local_prescribed_action_velocity k q hqP hr
  obtain ⟨s,hs,hsmall⟩ := Metric.mem_nhds_iff.mp
    (((isOpen_ball.inter C.source_open).inter isOpen_hillHminusPhysicalAbelianDomain).mem_nhds
      ⟨⟨mem_ball_self hrpos,hq⟩,real_mem_hillHminusPhysicalAbelianDomain q hr⟩)
  have hsq : q ∈ ball q s := mem_ball_self hs
  have hc := real_mem_hillHminusOffIndexAnalyticDomain q hr
  let V := P.prescribedActionDirichletVelocity k
  have hV (m : ℕ+) : AnalyticOnNhd ℂ (V m) (ball q s) :=
    (hvelocity m).1.mono (fun p hp => (hsmall hp).1.1)
  have hv (m : ℕ+) : ∀ p ∈ ball q s,
      NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m) (hillHminusCanonicalAction k) p =
        hillHminusDirichletSheet m p*V m p :=
    fun p hp => (hvelocity m).2 p (hsmall hp).1.1
  have hphase := C.phase_action_of_analytic_Dirichlet_velocity (ball q s) isOpen_ball
    (convex_ball q s).isPreconnected ⟨q,hsq⟩ (fun p hp => (hsmall hp).1.2) k (V n) (hV n) (hv n)
  have hbeta (m : ℕ+) (hmn : m ≠ n) :=
    hillHminus_offIndex_action_of_analytic_Dirichlet_velocity (ball q s) isOpen_ball
      (convex_ball q s).isPreconnected ⟨q,hsq⟩ (fun p hp => (hsmall hp).2)
      n m k hmn (V m) (hV m) (hv m) q hsq
  have ht := C.tendsto_completePhase_action_series k q hq hc V (hphase q hsq) hbeta
  have hu := P.tendsto_prescribed_action_velocity_sums n k q hqP hr
  have he : (fun N : ℕ => ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
      positiveScalarExtension (fun m : ℕ+ => hillHminusCanonicalPsi n
        (hillHminusCanonicalDirichlet m q,q)*V m q) j) =ᶠ[atTop]
      (fun N : ℕ => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*V n q+
        ∑ j ∈ Finset.Icc (-(N:ℤ)) N, positiveScalarExtension (hillHminusOffIndexVelocityTerm n V q) j) := by
    filter_upwards [eventually_ge_atTop (n:ℕ)] with N hN
    exact sum_positive_symmetricCutoff_reinsert_diagonal
      (fun m : ℕ+ => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*V m q) n N hN
  exact tendsto_nhds_unique ht (hu.congr' he)

theorem action_completePhase_Gardner_of_real (C : HillPhysicalOnIndexPhaseChart P n)
    (k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalAction k) C.completePhase q =
      if k=n then (1:ℂ) else 0 := by
  rw [NLS.Poisson.hminusGardnerBracket_antisymm,
    C.completePhase_action_Gardner_of_real k q hq hr,neg_neg]

theorem exists_local_completePhase_action_Gardner (C : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ C.source ∩ hillHminusOffIndexAnalyticDomain ∧
      AnalyticOnNhd ℂ C.completePhase (ball q r) ∧
      ∀ k : ℕ+, ∀ p ∈ ball q r,
        NLS.Poisson.hminusGardnerBracket C.completePhase (hillHminusCanonicalAction k) p =
          -(if k=n then (1:ℂ) else 0) ∧
        NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalAction k) C.completePhase p =
          if k=n then (1:ℂ) else 0 := by
  obtain ⟨r,hrpos,hsub⟩ := Metric.mem_nhds_iff.mp
    ((C.source_open.inter isOpen_hillHminusOffIndexAnalyticDomain).mem_nhds
      ⟨hq,real_mem_hillHminusOffIndexAnalyticDomain q hr⟩)
  have hphase := C.analytic_completePhase.mono hsub
  have ha : ball q r ⊆ hillHminusCanonicalActionDomain :=
    fun p hp => hillHminusCanonicalPsiDomain_subset_actionDomain (C.source_subset_psi (hsub hp).1)
  refine ⟨r,hrpos,hsub,hphase,?_⟩
  intro k
  have he := analytic_eqOn_of_real_periodOneHminus (ball q r) isOpen_ball
    (convex_ball q r).isPreconnected ⟨q,mem_ball_self hrpos,hr⟩
    (NLS.Poisson.hminusGardnerBracket C.completePhase (hillHminusCanonicalAction k))
    (fun _ => -(if k=n then (1:ℂ) else 0))
    (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _ hphase
      ((analyticOnNhd_hillHminusCanonicalAction k).mono ha)) analyticOnNhd_const
    (fun p hp hpr => C.completePhase_action_Gardner_of_real k p (hsub hp).1 hpr)
  intro p hp
  refine ⟨he hp,?_⟩
  rw [NLS.Poisson.hminusGardnerBracket_antisymm,he hp,neg_neg]

end NLS.KdV.HillPhysicalOnIndexPhaseChart
