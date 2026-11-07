import NLS.KdV.SingularDirichletSpectrum

/-! Exact full-domain native Dirichlet resolvent identities. The inverse
has (A-zJ)^(-1) orientation; its negative has the source (z-A)^(-1) orientation. -/
noncomputable section
open Set
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
local instance dirichletIdentityH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletIdentityH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletIdentityBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletIdentityBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- The full inverse into the actual zero-trace H1 domain is analytic in energy. -/
theorem analyticAt_singularDirichletResolventToH1
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ)
    (hz : z ∈ singularDirichletResolventSet q) :
    AnalyticAt ℂ (singularDirichletResolventToH1 q) z :=
  (analyticAt_singularDirichletResolventToH1_joint (q,z) hz).comp
    (f := fun w : ℂ => (q,w)) (analyticAt_const.prod analyticAt_id)

/-- Energy analyticity uses the FULL native continuous dual base norm. -/
theorem analyticAt_singularDirichletBaseResolvent
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ)
    (hz : z ∈ singularDirichletResolventSet q) :
    AnalyticAt ℂ (singularDirichletBaseResolvent q) z :=
  (analyticAt_singularDirichletBaseResolvent_joint (q,z) hz).comp
    (f := fun w : ℂ => (q,w)) (analyticAt_const.prod analyticAt_id)

/-- The actual H1-valued inverse satisfies the resolvent identity on EVERY
native full-dual datum, with the original domain inclusion in the middle. -/
theorem singularDirichletResolventToH1_sub_apply
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z w : ℂ)
    (hz : z ∈ singularDirichletResolventSet q) (hw : w ∈ singularDirichletResolventSet q)
    (F : UnitDirichletHminus) :
    singularDirichletResolventToH1 q z F-singularDirichletResolventToH1 q w F =
      (z-w) • singularDirichletResolventToH1 q z
        (singularDirichletBaseResolvent q w F) := by
  let f := singularDirichletResolventToH1 q w F
  have hr := singularDirichletResolventToH1_right q w hw F
  have he : singularDirichletOperator q f-z • singularDirichletDomainInclusion f =
      F+(w-z) • singularDirichletDomainInclusion f := by
    change singularDirichletOperator q f-w • singularDirichletDomainInclusion f = F at hr
    calc
      _ = (singularDirichletOperator q f-w • singularDirichletDomainInclusion f)+
          (w-z) • singularDirichletDomainInclusion f := by module
      _ = _ := by rw [hr]
  have hl := singularDirichletResolventToH1_left q z hz f
  rw [he,map_add,map_smul] at hl
  change singularDirichletResolventToH1 q z F-f =
    (z-w) • singularDirichletResolventToH1 q z (singularDirichletDomainInclusion f)
  calc
    _ = singularDirichletResolventToH1 q z F-
        (singularDirichletResolventToH1 q z F+
          (w-z) • singularDirichletResolventToH1 q z (singularDirichletDomainInclusion f)) :=
      congrArg (fun v => singularDirichletResolventToH1 q z F-v) hl.symm
    _ = _ := by module

/-- The actual bounded full-base resolvents satisfy their exact operator identity. -/
theorem singularDirichletBaseResolvent_sub
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z w : ℂ)
    (hz : z ∈ singularDirichletResolventSet q) (hw : w ∈ singularDirichletResolventSet q) :
    singularDirichletBaseResolvent q z-singularDirichletBaseResolvent q w =
      (z-w) • (singularDirichletBaseResolvent q z*singularDirichletBaseResolvent q w) := by
  apply ContinuousLinearMap.ext
  intro F
  change singularDirichletDomainInclusion (singularDirichletResolventToH1 q z F)-
    singularDirichletDomainInclusion (singularDirichletResolventToH1 q w F) = _
  rw [← map_sub,singularDirichletResolventToH1_sub_apply q z w hz hw F,map_smul]
  rfl

/-- Conventional (z-A)^(-1) orientation for the original source Riesz integral. -/
theorem singularDirichlet_oriented_resolvent_identity
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z w : ℂ)
    (hz : z ∈ singularDirichletResolventSet q) (hw : w ∈ singularDirichletResolventSet q) :
    -singularDirichletBaseResolvent q z-(-singularDirichletBaseResolvent q w) =
      (w-z) • ((-singularDirichletBaseResolvent q z)*(-singularDirichletBaseResolvent q w)) := by
  apply ContinuousLinearMap.ext
  intro F
  have he := congrArg (fun T : UnitDirichletHminus →L[ℂ] UnitDirichletHminus => T F)
    (singularDirichletBaseResolvent_sub q z w hz hw)
  change singularDirichletBaseResolvent q z F-singularDirichletBaseResolvent q w F =
    (z-w) • singularDirichletBaseResolvent q z (singularDirichletBaseResolvent q w F) at he
  change -(singularDirichletBaseResolvent q z F)-(-singularDirichletBaseResolvent q w F) =
    (w-z) • (-(singularDirichletBaseResolvent q z (-(singularDirichletBaseResolvent q w F))))
  rw [map_neg,neg_neg]
  calc
    _ = -(singularDirichletBaseResolvent q z F-singularDirichletBaseResolvent q w F) := by module
    _ = -((z-w) • singularDirichletBaseResolvent q z (singularDirichletBaseResolvent q w F)) :=
      congrArg Neg.neg he
    _ = _ := by module

/-- Native resolvents commute at every pair of actual resolvent energies. -/
theorem commute_singularDirichletBaseResolvent
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z w : ℂ)
    (hz : z ∈ singularDirichletResolventSet q) (hw : w ∈ singularDirichletResolventSet q) :
    Commute (singularDirichletBaseResolvent q z) (singularDirichletBaseResolvent q w) := by
  by_cases hzw : z = w
  · subst w
    exact Commute.refl _
  apply ContinuousLinearMap.ext
  intro F
  have h₁ := congrArg (fun T : UnitDirichletHminus →L[ℂ] UnitDirichletHminus => T F)
    (singularDirichletBaseResolvent_sub q z w hz hw)
  have h₂ := congrArg (fun T : UnitDirichletHminus →L[ℂ] UnitDirichletHminus => T F)
    (singularDirichletBaseResolvent_sub q w z hw hz)
  change singularDirichletBaseResolvent q z F-singularDirichletBaseResolvent q w F =
    (z-w) • singularDirichletBaseResolvent q z (singularDirichletBaseResolvent q w F) at h₁
  change singularDirichletBaseResolvent q w F-singularDirichletBaseResolvent q z F =
    (w-z) • singularDirichletBaseResolvent q w (singularDirichletBaseResolvent q z F) at h₂
  have h₂' : singularDirichletBaseResolvent q z F-singularDirichletBaseResolvent q w F =
      (z-w) • singularDirichletBaseResolvent q w (singularDirichletBaseResolvent q z F) := by
    calc
      _ = -(singularDirichletBaseResolvent q w F-singularDirichletBaseResolvent q z F) := by module
      _ = -((w-z) • singularDirichletBaseResolvent q w (singularDirichletBaseResolvent q z F)) :=
        congrArg Neg.neg h₂
      _ = _ := by module
  have he := congrArg (fun v => (z-w)⁻¹ • v) (h₁.symm.trans h₂')
  change singularDirichletBaseResolvent q z (singularDirichletBaseResolvent q w F) =
    singularDirichletBaseResolvent q w (singularDirichletBaseResolvent q z F)
  simpa only [inv_smul_smul₀ (sub_ne_zero.mpr hzw)] using he

/-- The actual full native expression commutes with its H1-valued inverse
in the precise domain-to-base form needed for spectral projection commutation. -/
theorem singularDirichletOperator_resolvent_intertwine
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ)
    (hz : z ∈ singularDirichletResolventSet q) (f : UnitDirichletH1) :
    singularDirichletOperator q (singularDirichletResolventToH1 q z (singularDirichletDomainInclusion f)) =
      singularDirichletBaseResolvent q z (singularDirichletOperator q f) := by
  have hr := singularDirichletResolventToH1_right q z hz (singularDirichletDomainInclusion f)
  have hl := congrArg singularDirichletDomainInclusion (singularDirichletResolventToH1_left q z hz f)
  rw [map_sub,map_smul,map_sub,map_smul] at hl
  apply sub_left_inj.mp
  exact hr.trans hl.symm

end NLS.KdV
