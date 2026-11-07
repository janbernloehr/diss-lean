import NLS.MKdV.ClassicalUniqueness
import NLS.FunctionalAnalysis.PeriodicContinuousFamily
import NLS.FunctionalAnalysis.ContinuousMapTimeDerivative

/-! # Ordinary jointly smooth physical fields satisfy classical regularity

Joint smoothness on the real time-space cover gives continuous circle-valued
families of both partial derivatives. The time partial is the uniform-norm
derivative by the Banach-valued fundamental theorem of calculus.
-/
noncomputable section
set_option autoImplicit false
open Topology NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ContDiff
namespace NLS.MKdV

/-- Joint smoothness implies the uniform time derivative and a norm-continuous
family representing the first spatial derivative. -/
theorem classicalRegularity_of_jointly_smooth
    (u : ℝ → C(AddCircle (2:ℝ),ℂ))
    (hs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => u z.1 (z.2 : AddCircle (2:ℝ)))) :
    Differentiable ℝ u ∧
    ∃ d : ℝ → C(AddCircle (2:ℝ),ℂ), Continuous d ∧
      ∀ t x : ℝ, d t (x : AddCircle (2:ℝ)) = deriv (fun y : ℝ => u t (y : AddCircle (2:ℝ))) x := by
  let F : ℝ × ℝ → ℂ := fun z => u z.1 (z.2 : AddCircle (2:ℝ))
  let vt : ℝ → ℝ → ℂ := fun t x => fderiv ℝ F (t,x) (1,0)
  let vx : ℝ → ℝ → ℂ := fun t x => fderiv ℝ F (t,x) (0,1)
  have ht (t x : ℝ) : HasDerivAt (fun r => u r (x : AddCircle (2:ℝ))) (vt t x) t := by
    exact (hs.differentiable (by simp) (t,x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hx (t x : ℝ) : HasDerivAt (fun y : ℝ => u t (y : AddCircle (2:ℝ))) (vx t x) x := by
    exact (hs.differentiable (by simp) (t,x)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))
  have hct : Continuous (fun z : ℝ × ℝ => vt z.1 z.2) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcx : Continuous (fun z : ℝ × ℝ => vx z.1 z.2) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpt (t : ℝ) : Function.Periodic (vt t) 2 := by
    intro x
    have h := ht t (x+2)
    simp only [AddCircle.coe_add_period] at h
    exact h.unique (ht t x)
  have hpx (t : ℝ) : Function.Periodic (vx t) 2 := by
    have he : vx t = deriv (fun y : ℝ => u t (y : AddCircle (2:ℝ))) := funext (fun x => (hx t x).deriv.symm)
    rw [he]
    apply periodic_deriv_of_periodic
    intro x
    exact congrArg (u t) (AddCircle.coe_add_period (2:ℝ) x)
  let v := periodicContinuousFamily 2 vt hpt hct
  let d := periodicContinuousFamily 2 vx hpx hcx
  have hv : Continuous v := continuous_periodicContinuousFamily 2 vt hpt hct
  refine ⟨fun t => (hasDerivAt_continuousMap_of_pointwise_real_banach u v hv ?_ t).differentiableAt,
    d,continuous_periodicContinuousFamily 2 vx hpx hcx,fun t x => (hx t x).deriv.symm⟩
  intro t x
  induction x using QuotientAddGroup.induction_on with
  | H x => exact ht t x

/-- Ordinary smooth real periodic physical solutions meet the precise
classical uniqueness hypotheses, including uniform-norm time regularity. -/
theorem IsClassicalMKdVTrajectory.of_jointly_smooth
    (M : ℂ) (u : ℝ → C(AddCircle (2:ℝ),ℂ))
    (hs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => u z.1 (z.2 : AddCircle (2:ℝ))))
    (hp : ∀ t, Function.Periodic (fun x : ℝ => u t (x : AddCircle (2:ℝ))) 1)
    (hr : ∀ t x : ℝ, (u t (x : AddCircle (2:ℝ))).im = 0)
    (he : ∀ t x : ℝ, HasDerivAt (fun r => u r (x : AddCircle (2:ℝ)))
      (scalarClassicalMKdVField M (fun y : ℝ => u t (y : AddCircle (2:ℝ))) x) t) :
    IsClassicalMKdVTrajectory M u := by
  obtain ⟨ht,hd⟩ := classicalRegularity_of_jointly_smooth u hs
  refine ⟨ht,fun t => hs.comp (contDiff_const.prodMk contDiff_id),hp,hr,hd,?_⟩
  intro t x
  have h := (ContinuousMap.evalCLM ℝ (x : AddCircle (2:ℝ))).hasFDerivAt.comp_hasDerivAt t
    (ht t).hasDerivAt
  exact h.unique (he t x)

end NLS.MKdV
