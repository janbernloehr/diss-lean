import NLS.ZakharovShabat.LocalClassicalNLSExistence
import NLS.ZakharovShabat.ClassicalNLSMass
import NLS.FunctionalAnalysis.ClosedDerivativeZero

/-! # Mass conservation for local classical NLS solutions -/
noncomputable section
open Set Complex MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
namespace NLS.ZakharovShabat

/-- The physical mass is continuous in the uniform spatial norm. -/
theorem continuous_classicalNLSMass : Continuous classicalNLSMass :=
  (ContinuousMap.toLp (α := AddCircle (2 : ℝ)) 2 AddCircle.haarAddCircle ℂ (E := ℂ)).continuous.norm.pow 2

/-- The local physical velocity retains period one at every interior time. -/
theorem IsClassicalNLSTrajectoryOn.velocity_periodic
    {a b : ℝ} {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalNLSTrajectoryOn a b u) (time : ℝ) (ht : time ∈ Ioo a b) :
    Function.Periodic (fun x : ℝ => deriv u time (x : AddCircle (2 : ℝ))) 1 := by
  have he : (fun x : ℝ => deriv u time (x : AddCircle (2 : ℝ))) =
      scalarClassicalNLSVectorField (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) :=
    funext (hu.equation time ht)
  rw [he]
  exact periodic_scalarClassicalNLSVectorField _ (hu.periodic time ⟨ht.1.le,ht.2.le⟩)

/-- The actual PDE makes the physical mass derivative zero in the interior. -/
theorem IsClassicalNLSTrajectoryOn.hasDerivAt_mass
    {a b : ℝ} {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalNLSTrajectoryOn a b u) (time : ℝ) (ht : time ∈ Ioo a b) :
    HasDerivAt (fun r => classicalNLSMass (u r)) 0 time := by
  let L := (ContinuousMap.toLp (α := AddCircle (2 : ℝ)) 2 AddCircle.haarAddCircle ℂ (E := ℂ)).restrictScalars ℝ
  have hd := L.hasFDerivAt.comp_hasDerivAt time ((hu.time_differentiable time ht).hasDerivAt)
  let := InnerProductSpace.rclikeToReal ℂ (Lp ℂ 2 (@AddCircle.haarAddCircle (2 : ℝ) inferInstance))
  have he := hd.norm_sq
  change HasDerivAt (fun r => classicalNLSMass (u r))
    (2*(inner ℂ (L (u time)) (L (deriv u time))).re) time at he
  apply he.congr_deriv
  change 2*(inner ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u time))
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (deriv u time))).re = 0
  rw [inner_toLp_eq_unit _ _ (hu.periodic time ⟨ht.1.le,ht.2.le⟩) (hu.velocity_periodic time ht)]
  have heq : (fun x : ℝ => conj (u time (x : AddCircle (2 : ℝ)))*deriv u time (x : AddCircle (2 : ℝ))) =
      fun x : ℝ => conj (u time (x : AddCircle (2 : ℝ)))*
        scalarClassicalNLSVectorField (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x := by
    funext x
    rw [hu.equation time ht]
  rw [heq,integral_conj_mul_scalarNLS_re_eq_zero _
    (hu.spatial_smooth time ⟨ht.1.le,ht.2.le⟩) (hu.periodic time ⟨ht.1.le,ht.2.le⟩),mul_zero]

/-- Local classical solutions conserve mass throughout the closed interval. -/
theorem IsClassicalNLSTrajectoryOn.mass_eq
    {a b : ℝ} {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalNLSTrajectoryOn a b u) {time initial : ℝ}
    (ht : time ∈ Icc a b) (hi : initial ∈ Icc a b) :
    classicalNLSMass (u time) = classicalNLSMass (u initial) :=
  FunctionalAnalysis.eq_of_hasDerivAt_zero_Icc
    (continuous_classicalNLSMass.comp_continuousOn hu.continuous) hu.hasDerivAt_mass ht hi

/-- Mass conservation is the literal integral over the original unit period. -/
theorem IsClassicalNLSTrajectoryOn.integral_mass_eq
    {a b : ℝ} {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalNLSTrajectoryOn a b u) {time initial : ℝ}
    (ht : time ∈ Icc a b) (hi : initial ∈ Icc a b) :
    (∫ x in (0 : ℝ)..1, ‖u time (x : AddCircle (2 : ℝ))‖^2) =
      ∫ x in (0 : ℝ)..1, ‖u initial (x : AddCircle (2 : ℝ))‖^2 := by
  rw [← classicalNLSMass_eq_integral _ (hu.periodic time ht),
    ← classicalNLSMass_eq_integral _ (hu.periodic initial hi)]
  exact hu.mass_eq ht hi

end NLS.ZakharovShabat
