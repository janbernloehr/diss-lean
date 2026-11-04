import NLS.KdV.HillOnIndexActionVelocity

/-! The actual patch's prescribed positive-index circle computes the
corresponding action cotangent. Its cycle label and normalized psi
periods are retained while deriving analytic divisor velocities. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

def prescribedActionDirichletVelocity (P : HillProductEquationPatch) (k m : ℕ+)
    (q : PeriodOneHminusOne) : ℂ :=
  P.parent.parent.miuraBall.actionBall.dirichletContourVelocity m
    (P.centers ((k:ℕ):ℤ):ℂ) (P.radii ((k:ℕ):ℤ)) q

theorem action_cotangent_prescribed_circle_of_real (P : HillProductEquationPatch)
    (k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    fderiv ℂ (hillHminusCanonicalAction k) q = -(2*(Real.pi:ℂ)⁻¹) •
      (∮ z in C((P.centers ((k:ℕ):ℤ):ℂ),P.radii ((k:ℕ):ℤ)),
        hillMiuraActionCotangentIntegrand q (P.parent.parent.miuraBall.actionBall.lift q)
          (P.parent.parent.miuraBall.actionBall.shift:ℂ) z) := by
  let B := P.parent.parent.miuraBall.actionBall
  have hqB : q ∈ B.source := (P.parent.subset (P.subset hq)).1
  have hreal := P.sourcePsi_real q hq hr
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((k:ℕ):ℤ)
    (P.centers ((k:ℕ):ℤ)) (P.radii ((k:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  obtain ⟨_,_,_,_,hlevels⟩ := exists_sourceIndexedHigherAction_gradient_circle
    (by norm_num) (by norm_num) ((k:ℕ):ℤ) (P.sourcePsi q) hreal
  have hg (v : CoeffPair 2) :
      (fderiv ℂ (sourceIndexedHigherAction (by norm_num) (by norm_num) ((k:ℕ):ℤ) 1) (P.sourcePsi q)) v =
        -(Real.pi:ℂ)⁻¹*(∮ z in C((P.centers ((k:ℕ):ℤ):ℂ),P.radii ((k:ℕ):ℤ)), z*
          (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalDiscriminant (by norm_num) (periodOnePotential ψ) z)
            (P.sourcePsi q)) v/sourceCanonicalRoot (by norm_num) (by norm_num) (P.sourcePsi q) z) := by
    have he : sourceIndexedHigherAction (by norm_num) (by norm_num) ((k:ℕ):ℤ) 1 =ᶠ[𝓝 (P.sourcePsi q)]
        (fun ψ => sourceHigherActionCircle (by norm_num) (by norm_num) ψ
          (P.centers ((k:ℕ):ℤ):ℂ) (P.radii ((k:ℕ):ℤ)) 1) := by
      filter_upwards [P.V_open.mem_nhds (P.image q hq).2] with ψ hψ
      exact sourceIndexedHigherAction_eq_circle (P.isolating.periodCircle ψ hψ ((k:ℕ):ℤ)
        (P.centers ((k:ℕ):ℤ)) (P.radii ((k:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)) 1
    rw [he.fderiv_eq]
    simpa only [pow_one] using fderiv_sourceHigherActionCircle_eq_gradient_integral
      (by norm_num) (by norm_num) (P.sourcePsi q) hreal (P.centers ((k:ℕ):ℤ):ℂ) (P.radii ((k:ℕ):ℤ))
      (P.radii_pos _) D.sphere_subset_rootDomain 1 v
  have hci := circleIntegrable_hillMiuraActionCotangentIntegrand q (B.lift q) (B.shift:ℂ)
    (P.centers ((k:ℕ):ℤ):ℂ) (P.radii ((k:ℕ):ℤ)) (P.radii_pos _).le D.sphere_subset_rootDomain
  ext h
  simp only [smul_apply,smul_eq_mul]
  have hev := map_circleIntegral (ContinuousLinearMap.apply ℂ ℂ h) hci
  change (∮ z in C((P.centers ((k:ℕ):ℤ):ℂ),P.radii ((k:ℕ):ℤ)),
    hillMiuraActionCotangentIntegrand q (B.lift q) (B.shift:ℂ) z) h = _ at hev
  rw [hev]
  have hp := B.fderiv_action_fixed_circle_of_source_gradient k q hqB
    (P.centers ((k:ℕ):ℤ):ℂ) (P.radii ((k:ℕ):ℤ)) (hlevels 1).1 hg (P.radii_pos _).le h
  change (fderiv ℂ (hillHminusCanonicalAction k) q) h = -(2*(Real.pi:ℂ)⁻¹)*
    (∮ z in C((P.centers ((k:ℕ):ℤ):ℂ),P.radii ((k:ℕ):ℤ)),
      (z/sourceCanonicalRoot (by norm_num) (by norm_num) (B.diracSource q) z)*
        hillHminusDiscriminantCotangent (z^2-(B.shift:ℂ)) q h)
  simpa only [div_mul_eq_mul_div] using hp

theorem Dirichlet_action_prescribed_velocity_of_real (P : HillProductEquationPatch)
    (k m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m) (hillHminusCanonicalAction k) q =
      hillHminusDirichletSheet m q*P.prescribedActionDirichletVelocity k m q := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((k:ℕ):ℤ)
    (P.centers ((k:ℕ):ℤ)) (P.radii ((k:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  exact P.parent.parent.miuraBall.actionBall.Dirichlet_action_velocity_of_cotangent_contour k m q
    (P.source_subset_canonicalDirichlet hq) _ _ (P.radii_pos _) D.sphere_subset_rootDomain
      (P.action_cotangent_prescribed_circle_of_real k q hq hr)

end NLS.KdV.HillProductEquationPatch
