import NLS.ZakharovShabat.ClassicalRenormalizedNLSGauge

/-! # Physical mass conservation for arbitrary classical solutions

Periodic integration by parts and the imaginary cubic term make the
mass derivative vanish. This applies to every classical trajectory,
without finite-gap hypotheses or a spectral reconstruction.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
namespace NLS.ZakharovShabat

/-- The real mass pairing of the actual scalar NLS field vanishes. -/
theorem integral_conj_mul_scalarNLS_re_eq_zero (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1, conj (u x)*scalarClassicalNLSVectorField u x).re = 0 := by
  have h := integral_scalarClassicalNLS_difference_re u (fun _ => 0) hu contDiff_const hp
    (fun _ => by rfl)
  simp only [scalarClassicalNLSVectorField,classicalNLSCubic,deriv_const',mul_zero,zero_mul,sub_zero,
    zero_pow (by decide : 2 ≠ 0)] at h
  change (∫ x in (0 : ℝ)..1, conj (u x)*(I*deriv (deriv u) x-I*(2*u x^2*conj (u x)))).re = 0
  rw [h]
  have hint : IntervalIntegrable (fun x => conj (u x)*(-I*(2*u x^2*conj (u x)))) volume 0 1 :=
    (hu.continuous.star.mul (continuous_const.mul
      ((continuous_const.mul (hu.continuous.pow 2)).mul hu.continuous.star))).intervalIntegrable 0 1
  refine (intervalIntegral.intervalIntegral_re hint).symm.trans ?_
  have hz : (fun x => (conj (u x)*(-I*(2*u x^2*conj (u x)))).re) = fun _ => 0 := by
    funext x
    simp [mul_re,mul_im,pow_two]
    ring
  change (∫ x in (0 : ℝ)..1, (conj (u x)*(-I*(2*u x^2*conj (u x)))).re) = 0
  rw [hz,intervalIntegral.integral_zero]

/-- Physical mass, computed using the normalized L² realization. -/
def classicalNLSMass (u : C(AddCircle (2 : ℝ), ℂ)) : ℝ :=
  ‖ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u‖^2

/-- This mass is exactly the integral over one physical period. -/
theorem classicalNLSMass_eq_integral (u : C(AddCircle (2 : ℝ), ℂ))
    (hp : Function.Periodic (fun x : ℝ => u (x : AddCircle (2 : ℝ))) 1) :
    classicalNLSMass u = ∫ x in (0 : ℝ)..1, ‖u (x : AddCircle (2 : ℝ))‖^2 :=
  norm_toLp_sq_eq_unit u hp

/-- Uniform-norm time differentiability and the actual PDE imply zero
mass derivative at every time. -/
theorem IsClassicalNLSTrajectory.hasDerivAt_mass
    {u : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u) (time : ℝ) :
    HasDerivAt (fun r => classicalNLSMass (u r)) 0 time := by
  let L := (ContinuousMap.toLp (α := AddCircle (2 : ℝ)) 2 AddCircle.haarAddCircle ℂ (E := ℂ)).restrictScalars ℝ
  have hd := L.hasFDerivAt.comp_hasDerivAt time ((hu.time_differentiable time).hasDerivAt)
  let := InnerProductSpace.rclikeToReal ℂ (Lp ℂ 2 (@AddCircle.haarAddCircle (2 : ℝ) inferInstance))
  have he := hd.norm_sq
  change HasDerivAt (fun r => classicalNLSMass (u r))
    (2*(inner ℂ (L (u time)) (L (deriv u time))).re) time at he
  apply he.congr_deriv
  change 2*(inner ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u time))
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (deriv u time))).re = 0
  rw [inner_toLp_eq_unit _ _ (hu.periodic time) (hu.velocity_periodic time)]
  have heq : (fun x : ℝ => conj (u time (x : AddCircle (2 : ℝ)))*deriv u time (x : AddCircle (2 : ℝ))) =
      fun x : ℝ => conj (u time (x : AddCircle (2 : ℝ)))*
        scalarClassicalNLSVectorField (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x := by
    funext x
    rw [hu.equation]
  rw [heq,integral_conj_mul_scalarNLS_re_eq_zero _ (hu.spatial_smooth time) (hu.periodic time),mul_zero]

/-- Arbitrary classical NLS solutions conserve physical mass at all times. -/
theorem IsClassicalNLSTrajectory.mass_eq
    {u : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u) (time initial : ℝ) :
    classicalNLSMass (u time) = classicalNLSMass (u initial) :=
  is_const_of_deriv_eq_zero (fun r => (hu.hasDerivAt_mass r).differentiableAt)
    (fun r => (hu.hasDerivAt_mass r).deriv) time initial

/-- Ordinary NLS mass conservation over the literal physical period. -/
theorem IsClassicalNLSTrajectory.integral_mass_eq
    {u : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u) (time initial : ℝ) :
    (∫ x in (0 : ℝ)..1, ‖u time (x : AddCircle (2 : ℝ))‖^2) =
      ∫ x in (0 : ℝ)..1, ‖u initial (x : AddCircle (2 : ℝ))‖^2 := by
  rw [← classicalNLSMass_eq_integral _ (hu.periodic time),
    ← classicalNLSMass_eq_integral _ (hu.periodic initial)]
  exact hu.mass_eq time initial

/-- A unit scalar gauge preserves mass at each time. -/
theorem classicalNLSMass_gauge (M : ℝ) (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) (time : ℝ) :
    classicalNLSMass (classicalNLSGauge M u time) = classicalNLSMass (u time) := by
  simp only [classicalNLSMass,classicalNLSGauge,map_smul,norm_smul,norm_classicalNLSGaugePhase,one_mul]

/-- Inverse gauge transfers mass conservation to every classical
renormalized trajectory, with any fixed real mass parameter. -/
theorem IsClassicalRenormalizedNLSTrajectory.mass_eq
    {M : ℝ} {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalRenormalizedNLSTrajectory M u) (time initial : ℝ) :
    classicalNLSMass (u time) = classicalNLSMass (u initial) := by
  simpa only [classicalNLSMass_gauge] using hu.ungauge.mass_eq time initial

/-- Conservation is expressed using the actual physical integral, without
any assumption that the fixed parameter is the initial mass. -/
theorem IsClassicalRenormalizedNLSTrajectory.integral_mass_eq
    {M : ℝ} {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalRenormalizedNLSTrajectory M u) (time initial : ℝ) :
    (∫ x in (0 : ℝ)..1, ‖u time (x : AddCircle (2 : ℝ))‖^2) =
      ∫ x in (0 : ℝ)..1, ‖u initial (x : AddCircle (2 : ℝ))‖^2 := by
  rw [← classicalNLSMass_eq_integral _ (hu.periodic time),
    ← classicalNLSMass_eq_integral _ (hu.periodic initial)]
  exact hu.mass_eq time initial

/-- When the parameter is the physical initial mass, the fixed-parameter
classical equation is the nonlocal renormalized NLS equation at every time. -/
theorem IsClassicalRenormalizedNLSTrajectory.equation_physical_mass
    {M : ℝ} {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalRenormalizedNLSTrajectory M u) (hM : M = classicalNLSMass (u 0))
    (time x : ℝ) :
    deriv u time (x : AddCircle (2 : ℝ)) =
      scalarClassicalNLSVectorField (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x +
        (4*(∫ y in (0 : ℝ)..1, ‖u time (y : AddCircle (2 : ℝ))‖^2) : ℂ)*I*
          u time (x : AddCircle (2 : ℝ)) := by
  rw [hu.equation,← classicalNLSMass_eq_integral _ (hu.periodic time),hu.mass_eq time 0,hM]

end NLS.ZakharovShabat
