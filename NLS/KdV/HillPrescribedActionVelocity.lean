import NLS.KdV.HillPrescribedActionCircle

/-! The prescribed, cycle-labelled action circle defines analytic
native Dirichlet velocities on one ball before all divisor indices.
Real-form uniqueness continues their actual Gardner identities. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_prescribed_action_velocity (P : HillProductEquationPatch)
    (k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ P.source ∧
      ∀ m : ℕ+, AnalyticOnNhd ℂ (P.prescribedActionDirichletVelocity k m) (ball q r) ∧
        ∀ p ∈ ball q r, NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
          (hillHminusCanonicalAction k) p =
          hillHminusDirichletSheet m p*P.prescribedActionDirichletVelocity k m p := by
  let B := P.parent.parent.miuraBall.actionBall
  obtain ⟨W,hW,_,hreal,hDW,hroot⟩ :=
    exists_global_source_analytic_canonicalRoot (p := 2) (by norm_num) (by norm_num)
  have hU : IsOpen (P.source ∩ P.sourcePsi ⁻¹' W) :=
    P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open hW
  obtain ⟨r,hrpos,hsub⟩ := Metric.mem_nhds_iff.mp
    (hU.mem_nhds ⟨hq,hreal (P.sourcePsi_real q hq hr)⟩)
  have hsource : ball q r ⊆ P.source := fun p hp => (hsub hp).1
  have hd := hsource.trans P.source_subset_canonicalDirichlet
  have ha : ball q r ⊆ hillHminusCanonicalActionDomain :=
    fun p hp => mem_iUnion.mpr ⟨B,(P.parent.subset (P.subset (hsource hp))).1⟩
  have hc : ∀ p ∈ ball q r, ∀ z ∈ sphere (P.centers ((k:ℕ):ℤ):ℂ) (P.radii ((k:ℕ):ℤ)),
      (z,p) ∈ B.rootJointDomain W := by
    intro p hp z hz
    let D := P.isolating.periodCircle (P.sourcePsi p) (P.image p (hsource hp)).2 ((k:ℕ):ℤ)
      (P.centers ((k:ℕ):ℤ)) (P.radii ((k:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
    exact ⟨⟨mem_univ _,(P.parent.subset (P.subset (hsource hp))).1⟩,
      (hsub hp).2,D.sphere_subset_rootDomain hz⟩
  refine ⟨r,hrpos,hsource,?_⟩
  intro m
  have hV : AnalyticOnNhd ℂ (P.prescribedActionDirichletVelocity k m) (ball q r) :=
    B.analytic_dirichletContourVelocity W hDW hroot (ball q r) isOpen_ball hd
      _ _ (P.radii_pos _).le hc m
  refine ⟨hV,?_⟩
  exact analytic_eqOn_of_real_periodOneHminus (ball q r) isOpen_ball
    (convex_ball q r).isPreconnected ⟨q,mem_ball_self hrpos,hr⟩ _ _
    (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
      ((analyticOnNhd_hillHminusCanonicalDirichlet m).mono hd)
      ((analyticOnNhd_hillHminusCanonicalAction k).mono ha))
    (((analyticOnNhd_hillHminusDirichletSheet m).mono hd).mul hV)
    (fun p hp hpr => P.Dirichlet_action_prescribed_velocity_of_real k m p (hsource hp) hpr)

end NLS.KdV.HillProductEquationPatch
