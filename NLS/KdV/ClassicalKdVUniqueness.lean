import NLS.KdV.ClassicalKdVDifferenceEstimate
import NLS.ZakharovShabat.ClassicalNLSUniqueness
import NLS.FunctionalAnalysis.IntervalNormGronwall

/-! # Uniqueness of classical real periodic KdV trajectories

The time derivative is taken in the uniform norm. Continuity of the first
spatial derivative supplies compact-time bounds. The difference-energy
inequality is proved from the physical equation, rather than assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.ZakharovShabat
open scoped ContDiff ComplexConjugate InnerProductSpace
namespace NLS.KdV

/-- A real periodic physical KdV trajectory.
The continuous first-derivative family is part of classical regularity. -/
structure IsSmoothPhysicalKdVTrajectory (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) : Prop where
  time_differentiable : Differentiable ℝ u
  spatial_smooth : ∀ time, ContDiff ℝ ∞ (fun x : ℝ => u time (x : AddCircle (2 : ℝ)))
  periodic : ∀ time, Function.Periodic (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) 1
  real : ∀ (time x : ℝ), (u time (x : AddCircle (2 : ℝ))).im = 0
  first_derivative : ∃ d : ℝ → C(AddCircle (2 : ℝ), ℂ), Continuous d ∧
    ∀ (time x : ℝ), d time (x : AddCircle (2 : ℝ)) =
      deriv (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x
  equation : ∀ (time x : ℝ), deriv u time (x : AddCircle (2 : ℝ)) =
    scalarClassicalKdVField (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x

theorem IsSmoothPhysicalKdVTrajectory.velocity_periodic
    {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsSmoothPhysicalKdVTrajectory u) (time : ℝ) :
    Function.Periodic (fun x : ℝ => deriv u time (x : AddCircle (2 : ℝ))) 1 := by
  have he : (fun x : ℝ => deriv u time (x : AddCircle (2 : ℝ))) =
      scalarClassicalKdVField (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) :=
    funext (hu.equation time)
  rw [he]
  exact periodic_scalarClassicalKdVField _ (hu.periodic time)

/-- Squared L² distance of two continuous periodic representatives. -/
def classicalKdVDifferenceEnergy (u v : C(AddCircle (2 : ℝ), ℂ)) : ℝ :=
  ‖ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u-v)‖^2

/-- The energy derivative is derived from uniform-norm differentiability
and the actual PDE; it is not an additional solution hypothesis. -/
theorem IsSmoothPhysicalKdVTrajectory.hasDerivAt_difference_energy
    {u v : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsSmoothPhysicalKdVTrajectory u)
    (hv : IsSmoothPhysicalKdVTrajectory v) (time : ℝ) :
    HasDerivAt (fun r => classicalKdVDifferenceEnergy (u r) (v r))
      (2*(∫ x in (0 : ℝ)..1, conj (u time (x : AddCircle (2 : ℝ))-v time (x : AddCircle (2 : ℝ)))*
        (scalarClassicalKdVField (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x-
         scalarClassicalKdVField (fun y : ℝ => v time (y : AddCircle (2 : ℝ))) x)).re) time := by
  let L := (ContinuousMap.toLp (α := AddCircle (2 : ℝ)) 2 AddCircle.haarAddCircle ℂ (E := ℂ)).restrictScalars ℝ
  have hd := L.hasFDerivAt.comp_hasDerivAt time
    (((hu.time_differentiable time).hasDerivAt).sub ((hv.time_differentiable time).hasDerivAt))
  let := InnerProductSpace.rclikeToReal ℂ (Lp ℂ 2 (@AddCircle.haarAddCircle (2 : ℝ) inferInstance))
  have he := hd.norm_sq
  change HasDerivAt (fun r => classicalKdVDifferenceEnergy (u r) (v r))
    (2*(inner ℂ (L (u time-v time)) (L (deriv u time-deriv v time))).re) time at he
  convert he using 1
  congr 1
  change _ = (inner ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u time-v time))
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (deriv u time-deriv v time))).re
  rw [inner_toLp_eq_unit _ _ ((hu.periodic time).sub (hv.periodic time))
    ((hu.velocity_periodic time).sub (hv.velocity_periodic time))]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only [ContinuousMap.sub_apply]
  rw [hu.equation,hv.equation]

/-- The physical equation controls the actual L² distance derivative. -/
theorem IsSmoothPhysicalKdVTrajectory.abs_deriv_difference_energy_le
    {u v : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsSmoothPhysicalKdVTrajectory u) (hv : IsSmoothPhysicalKdVTrajectory v)
    (time R : ℝ)
    (hdum : ∀ x : ℝ, ‖deriv (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x‖ ≤ R)
    (hdvm : ∀ x : ℝ, ‖deriv (fun y : ℝ => v time (y : AddCircle (2 : ℝ))) x‖ ≤ R) :
    |deriv (fun r => classicalKdVDifferenceEnergy (u r) (v r)) time| ≤
      18*R*classicalKdVDifferenceEnergy (u time) (v time) := by
  rw [(hu.hasDerivAt_difference_energy hv time).deriv]
  unfold classicalKdVDifferenceEnergy
  rw [norm_toLp_sq_eq_unit _ ((hu.periodic time).sub (hv.periodic time))]
  exact abs_scalarClassicalKdV_difference_energy_le _ _
    (hu.spatial_smooth time) (hv.spatial_smooth time) (hu.periodic time) (hv.periodic time)
    (hu.real time) (hv.real time) R hdum hdvm

/-- Equal values at one time force equality at every real time.
All bounds needed by Grönwall are obtained on the compact time interval. -/
theorem IsSmoothPhysicalKdVTrajectory.eq_of_eq_at
    {u v : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsSmoothPhysicalKdVTrajectory u) (hv : IsSmoothPhysicalKdVTrajectory v)
    (initial : ℝ) (hinit : u initial = v initial) : u = v := by
  funext time
  let e := fun r => classicalKdVDifferenceEnergy (u r) (v r)
  obtain ⟨du,hdu,hdu_eq⟩ := hu.first_derivative
  obtain ⟨dv,hdv,hdv_eq⟩ := hv.first_derivative
  obtain ⟨Rdu,hRdu⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hdu.continuousOn (s := Icc (min initial time) (max initial time)))
  obtain ⟨Rdv,hRdv⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hdv.continuousOn (s := Icc (min initial time) (max initial time)))
  let R := max Rdu Rdv
  have h3 : Rdu ≤ R := le_max_left _ _
  have h4 : Rdv ≤ R := le_max_right _ _
  have hg := NLS.FunctionalAnalysis.norm_le_exp_abs_of_hasDerivWithinAt_Icc
    (f := e) (f' := deriv e) (a := initial) (b := time) (K := 18*R)
    (fun r _ => (hu.hasDerivAt_difference_energy hv r).differentiableAt.hasDerivAt.hasDerivWithinAt)
    (fun r hr => by
      have hb := hu.abs_deriv_difference_energy_le hv r R
        (fun x => by rw [← hdu_eq r x]; exact ((du r).norm_coe_le_norm _).trans ((hRdu r hr).trans h3))
        (fun x => by rw [← hdv_eq r x]; exact ((dv r).norm_coe_le_norm _).trans ((hRdv r hr).trans h4))
      have hnonneg : 0 ≤ e r := sq_nonneg _
      simpa only [Real.norm_eq_abs,abs_of_nonneg hnonneg] using hb)
  have hz : e initial = 0 := by simp [e,classicalKdVDifferenceEnergy,hinit]
  have hzero : e time = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hz] using hg) (norm_nonneg _))
  have hL : ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u time-v time) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  have heq : u time-v time = 0 :=
    ContinuousMap.toLp_injective (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ) (hL.trans (map_zero _).symm)
  exact sub_eq_zero.mp heq

end NLS.KdV
