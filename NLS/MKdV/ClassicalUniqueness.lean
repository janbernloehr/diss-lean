import NLS.MKdV.ClassicalDifferenceEstimate
import NLS.ZakharovShabat.ClassicalNLSUniqueness
import NLS.FunctionalAnalysis.IntervalNormGronwall

/-! # Uniqueness of classical real periodic mKdV trajectories

The time derivative is taken in the uniform norm. Continuity of the first
spatial derivative supplies compact-time bounds. The difference-energy
inequality is proved from the physical equation, rather than assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.ZakharovShabat
open scoped ContDiff ComplexConjugate InnerProductSpace
namespace NLS.MKdV

/-- A real periodic classical trajectory with its fixed initial mass.
The continuous first-derivative family is part of classical regularity. -/
structure IsClassicalMKdVTrajectory (M : ℂ) (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) : Prop where
  time_differentiable : Differentiable ℝ u
  spatial_smooth : ∀ time, ContDiff ℝ ∞ (fun x : ℝ => u time (x : AddCircle (2 : ℝ)))
  periodic : ∀ time, Function.Periodic (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) 1
  real : ∀ (time x : ℝ), (u time (x : AddCircle (2 : ℝ))).im = 0
  first_derivative : ∃ d : ℝ → C(AddCircle (2 : ℝ), ℂ), Continuous d ∧
    ∀ (time x : ℝ), d time (x : AddCircle (2 : ℝ)) =
      deriv (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x
  equation : ∀ (time x : ℝ), deriv u time (x : AddCircle (2 : ℝ)) =
    scalarClassicalMKdVField M (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x

theorem IsClassicalMKdVTrajectory.velocity_periodic
    {M : ℂ} {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalMKdVTrajectory M u) (time : ℝ) :
    Function.Periodic (fun x : ℝ => deriv u time (x : AddCircle (2 : ℝ))) 1 := by
  have he : (fun x : ℝ => deriv u time (x : AddCircle (2 : ℝ))) =
      scalarClassicalMKdVField M (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) :=
    funext (hu.equation time)
  rw [he]
  exact periodic_scalarClassicalMKdVField M _ (hu.periodic time)

/-- Squared L² distance of two continuous periodic representatives. -/
def classicalMKdVDifferenceEnergy (u v : C(AddCircle (2 : ℝ), ℂ)) : ℝ :=
  ‖ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u-v)‖^2

/-- The energy derivative is derived from uniform-norm differentiability
and the actual PDE; it is not an additional solution hypothesis. -/
theorem IsClassicalMKdVTrajectory.hasDerivAt_difference_energy
    {M : ℂ} {u v : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalMKdVTrajectory M u)
    (hv : IsClassicalMKdVTrajectory M v) (time : ℝ) :
    HasDerivAt (fun r => classicalMKdVDifferenceEnergy (u r) (v r))
      (2*(∫ x in (0 : ℝ)..1, conj (u time (x : AddCircle (2 : ℝ))-v time (x : AddCircle (2 : ℝ)))*
        (scalarClassicalMKdVField M (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x-
         scalarClassicalMKdVField M (fun y : ℝ => v time (y : AddCircle (2 : ℝ))) x)).re) time := by
  let L := (ContinuousMap.toLp (α := AddCircle (2 : ℝ)) 2 AddCircle.haarAddCircle ℂ (E := ℂ)).restrictScalars ℝ
  have hd := L.hasFDerivAt.comp_hasDerivAt time
    (((hu.time_differentiable time).hasDerivAt).sub ((hv.time_differentiable time).hasDerivAt))
  let := InnerProductSpace.rclikeToReal ℂ (Lp ℂ 2 (@AddCircle.haarAddCircle (2 : ℝ) inferInstance))
  have he := hd.norm_sq
  change HasDerivAt (fun r => classicalMKdVDifferenceEnergy (u r) (v r))
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
theorem IsClassicalMKdVTrajectory.abs_deriv_difference_energy_le
    {M : ℂ} {u v : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalMKdVTrajectory M u) (hv : IsClassicalMKdVTrajectory M v)
    (time R : ℝ) (hR : 0 ≤ R) (hum : ‖u time‖ ≤ R) (hvm : ‖v time‖ ≤ R)
    (hdum : ∀ x : ℝ, ‖deriv (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x‖ ≤ R)
    (hdvm : ∀ x : ℝ, ‖deriv (fun y : ℝ => v time (y : AddCircle (2 : ℝ))) x‖ ≤ R) :
    |deriv (fun r => classicalMKdVDifferenceEnergy (u r) (v r)) time| ≤
      36*R^2*classicalMKdVDifferenceEnergy (u time) (v time) := by
  rw [(hu.hasDerivAt_difference_energy hv time).deriv]
  unfold classicalMKdVDifferenceEnergy
  rw [norm_toLp_sq_eq_unit _ ((hu.periodic time).sub (hv.periodic time))]
  exact abs_scalarClassicalMKdV_difference_energy_le M _ _
    (hu.spatial_smooth time) (hv.spatial_smooth time) (hu.periodic time) (hv.periodic time)
    (hu.real time) (hv.real time) R hR
    (fun x => ((u time).norm_coe_le_norm _).trans hum)
    (fun x => ((v time).norm_coe_le_norm _).trans hvm) hdum hdvm

/-- Equal values at one time force equality at every real time.
All bounds needed by Grönwall are obtained on the compact time interval. -/
theorem IsClassicalMKdVTrajectory.eq_of_eq_at
    {M : ℂ} {u v : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalMKdVTrajectory M u) (hv : IsClassicalMKdVTrajectory M v)
    (initial : ℝ) (hinit : u initial = v initial) : u = v := by
  funext time
  let e := fun r => classicalMKdVDifferenceEnergy (u r) (v r)
  obtain ⟨du,hdu,hdu_eq⟩ := hu.first_derivative
  obtain ⟨dv,hdv,hdv_eq⟩ := hv.first_derivative
  obtain ⟨Ru,hRu⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hu.time_differentiable.continuous.continuousOn (s := Icc (min initial time) (max initial time)))
  obtain ⟨Rv,hRv⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hv.time_differentiable.continuous.continuousOn (s := Icc (min initial time) (max initial time)))
  obtain ⟨Rdu,hRdu⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hdu.continuousOn (s := Icc (min initial time) (max initial time)))
  obtain ⟨Rdv,hRdv⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hdv.continuousOn (s := Icc (min initial time) (max initial time)))
  let R := max 0 (max Ru (max Rv (max Rdu Rdv)))
  have hR : 0 ≤ R := le_max_left _ _
  have h1 : Ru ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : Rv ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h3 : Rdu ≤ R := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have h4 : Rdv ≤ R := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hg := NLS.FunctionalAnalysis.norm_le_exp_abs_of_hasDerivWithinAt_Icc
    (f := e) (f' := deriv e) (a := initial) (b := time) (K := 36*R^2)
    (fun r _ => (hu.hasDerivAt_difference_energy hv r).differentiableAt.hasDerivAt.hasDerivWithinAt)
    (fun r hr => by
      have hb := hu.abs_deriv_difference_energy_le hv r R hR
        ((hRu r hr).trans h1) ((hRv r hr).trans h2)
        (fun x => by rw [← hdu_eq r x]; exact ((du r).norm_coe_le_norm _).trans ((hRdu r hr).trans h3))
        (fun x => by rw [← hdv_eq r x]; exact ((dv r).norm_coe_le_norm _).trans ((hRdv r hr).trans h4))
      have hnonneg : 0 ≤ e r := sq_nonneg _
      simpa only [Real.norm_eq_abs,abs_of_nonneg hnonneg] using hb)
  have hz : e initial = 0 := by simp [e,classicalMKdVDifferenceEnergy,hinit]
  have hzero : e time = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hz] using hg) (norm_nonneg _))
  have hL : ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u time-v time) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  have heq : u time-v time = 0 :=
    ContinuousMap.toLp_injective (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ) (hL.trans (map_zero _).symm)
  exact sub_eq_zero.mp heq

end NLS.MKdV
