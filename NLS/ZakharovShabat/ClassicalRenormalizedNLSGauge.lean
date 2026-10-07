import NLS.ZakharovShabat.ClassicalNLSUniqueness

/-! # Classical renormalized NLS and its physical phase rotation

The time-dependent scalar gauge carries a classical solution with mass
parameter M to one with parameter M+m. In particular, the inverse gauge
reduces the renormalized equation to ordinary NLS and transfers its
classical uniqueness theorem. No spectral coordinates are involved.
-/
noncomputable section
open Set Complex
open scoped ContDiff ComplexConjugate
namespace NLS.ZakharovShabat

/-- Classical periodic renormalized NLS with a fixed real mass parameter.
The physical initial mass is supplied when constructing the solution map. -/
structure IsClassicalRenormalizedNLSTrajectory (M : ℝ)
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) : Prop where
  time_differentiable : Differentiable ℝ u
  spatial_smooth : ∀ time, ContDiff ℝ ∞ (fun x : ℝ => u time (x : AddCircle (2 : ℝ)))
  periodic : ∀ time, Function.Periodic (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) 1
  equation : ∀ (time x : ℝ), deriv u time (x : AddCircle (2 : ℝ)) =
    scalarClassicalNLSVectorField (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x +
      (4*M : ℂ)*I*u time (x : AddCircle (2 : ℝ))

/-- A unit complex constant commutes with the scalar NLS spatial field. -/
theorem scalarClassicalNLSVectorField_phase (c : ℂ) (hc : ‖c‖ = 1) (u : ℝ → ℂ) (x : ℝ) :
    scalarClassicalNLSVectorField (fun y => c*u y) x = c*scalarClassicalNLSVectorField u x := by
  have hconj : c*conj c = 1 := by simpa only [hc,ofReal_one,one_pow] using Complex.mul_conj' c
  simp only [scalarClassicalNLSVectorField,deriv_const_mul_field',classicalNLSCubic,map_mul]
  calc
    _ = c*(I*deriv (deriv u) x)-I*(2*(c*conj c)*c*(u x)^2*conj (u x)) := by ring
    _ = _ := by rw [hconj]; ring

/-- The scalar gauge with the physical mass normalization. -/
def classicalNLSGaugePhase (m time : ℝ) : ℂ := Complex.exp (((4*m*time : ℝ) : ℂ)*I)

@[simp] theorem classicalNLSGaugePhase_zero (m : ℝ) : classicalNLSGaugePhase m 0 = 1 := by
  simp [classicalNLSGaugePhase]

@[simp] theorem norm_classicalNLSGaugePhase (m time : ℝ) : ‖classicalNLSGaugePhase m time‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The gauge derivative has the positive mass rotation in physical time. -/
theorem hasDerivAt_classicalNLSGaugePhase (m time : ℝ) :
    HasDerivAt (classicalNLSGaugePhase m)
      ((4*m : ℂ)*I*classicalNLSGaugePhase m time) time := by
  have hlin := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt time
    ((hasDerivAt_id time).const_mul (4*m))
  have hd := (hlin.mul_const I).cexp
  change HasDerivAt (classicalNLSGaugePhase m)
    (Complex.exp (((4*m*time : ℝ) : ℂ)*I)*((4*m*1 : ℝ)*I)) time at hd
  apply hd.congr_deriv
  simp only [classicalNLSGaugePhase,ofReal_mul,ofReal_ofNat,mul_one]
  ring

/-- Multiplication of the physical trajectory by the unit scalar phase. -/
def classicalNLSGauge (m : ℝ) (u : ℝ → C(AddCircle (2 : ℝ), ℂ))
    (time : ℝ) : C(AddCircle (2 : ℝ), ℂ) := classicalNLSGaugePhase m time • u time

@[simp] theorem classicalNLSGauge_zero_time (m : ℝ) (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) :
    classicalNLSGauge m u 0 = u 0 := by simp [classicalNLSGauge]

@[simp] theorem classicalNLSGauge_zero (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) :
    classicalNLSGauge 0 u = u := by funext time; simp [classicalNLSGauge,classicalNLSGaugePhase]

/-- Scalar gauges add their real mass parameters. -/
theorem classicalNLSGauge_add (m n : ℝ) (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) :
    classicalNLSGauge m (classicalNLSGauge n u) = classicalNLSGauge (m+n) u := by
  funext time
  simp only [classicalNLSGauge,smul_smul,classicalNLSGaugePhase,← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The inverse gauge recovers the original continuous trajectory exactly. -/
theorem classicalNLSGauge_injective (m : ℝ) : Function.Injective (classicalNLSGauge m) := by
  intro u v h
  have he := congrArg (classicalNLSGauge (-m)) h
  simpa only [classicalNLSGauge_add,neg_add_cancel,classicalNLSGauge_zero] using he

/-- Pointwise and uniform norms are unchanged by the gauge. -/
theorem norm_classicalNLSGauge (m : ℝ) (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) (time : ℝ) :
    ‖classicalNLSGauge m u time‖ = ‖u time‖ := by
  simp only [classicalNLSGauge,norm_smul,norm_classicalNLSGaugePhase,one_mul]

/-- The gauge transports the actual PDE, including its time derivative,
from mass parameter M to M+m. -/
theorem IsClassicalRenormalizedNLSTrajectory.gauge
    {M : ℝ} {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalRenormalizedNLSTrajectory M u) (m : ℝ) :
    IsClassicalRenormalizedNLSTrajectory (M+m) (classicalNLSGauge m u) := by
  have hd (time : ℝ) := (hasDerivAt_classicalNLSGaugePhase m time).smul
    (hu.time_differentiable time).hasDerivAt
  refine ⟨fun time => (hd time).differentiableAt,?_,?_,?_⟩
  · intro time
    exact contDiff_const.mul (hu.spatial_smooth time)
  · intro time x
    change classicalNLSGaugePhase m time * u time ((x+1 : ℝ) : AddCircle (2 : ℝ)) = _
    exact congrArg (fun z : ℂ => classicalNLSGaugePhase m time*z) (hu.periodic time x)
  · intro time x
    have hderiv : deriv (classicalNLSGauge m u) time =
        ((4*m : ℂ)*I*classicalNLSGaugePhase m time) • u time +
          classicalNLSGaugePhase m time • deriv u time := by
      simpa only [classicalNLSGauge,Pi.smul_def,add_comm] using! (hd time).deriv
    rw [hderiv]
    change ((4*m : ℂ)*I*classicalNLSGaugePhase m time)*u time (x : AddCircle (2 : ℝ)) +
      classicalNLSGaugePhase m time*deriv u time (x : AddCircle (2 : ℝ)) =
      scalarClassicalNLSVectorField (fun y : ℝ => classicalNLSGaugePhase m time*
        u time (y : AddCircle (2 : ℝ))) x +
      (4*((M+m : ℝ) : ℂ))*I*(classicalNLSGaugePhase m time*u time (x : AddCircle (2 : ℝ)))
    rw [hu.equation,scalarClassicalNLSVectorField_phase _ (norm_classicalNLSGaugePhase m time)]
    push_cast
    ring

/-- Zero mass parameter is exactly the ordinary classical equation. -/
theorem isClassicalRenormalizedNLSTrajectory_zero_iff
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) :
    IsClassicalRenormalizedNLSTrajectory 0 u ↔ IsClassicalNLSTrajectory u := by
  constructor
  · intro hu
    exact ⟨hu.time_differentiable,hu.spatial_smooth,hu.periodic,by simpa using hu.equation⟩
  · intro hu
    exact ⟨hu.time_differentiable,hu.spatial_smooth,hu.periodic,by simpa using hu.equation⟩

/-- Inverse rotation removes the mass term from every classical renormalized trajectory. -/
theorem IsClassicalRenormalizedNLSTrajectory.ungauge
    {M : ℝ} {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalRenormalizedNLSTrajectory M u) :
    IsClassicalNLSTrajectory (classicalNLSGauge (-M) u) := by
  apply (isClassicalRenormalizedNLSTrajectory_zero_iff _).mp
  simpa only [add_neg_cancel] using hu.gauge (-M)

/-- The positive mass rotation turns an ordinary solution into a renormalized one. -/
theorem IsClassicalNLSTrajectory.gauge
    {u : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u) (M : ℝ) :
    IsClassicalRenormalizedNLSTrajectory M (classicalNLSGauge M u) := by
  simpa only [zero_add] using ((isClassicalRenormalizedNLSTrajectory_zero_iff u).mpr hu).gauge M

/-- Classical renormalized trajectories with the same mass parameter and
value at one time coincide on all of real time. -/
theorem IsClassicalRenormalizedNLSTrajectory.eq_of_eq_at
    {M : ℝ} {u v : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalRenormalizedNLSTrajectory M u)
    (hv : IsClassicalRenormalizedNLSTrajectory M v) (initial : ℝ)
    (hinit : u initial = v initial) : u = v := by
  apply classicalNLSGauge_injective (-M)
  apply hu.ungauge.eq_of_eq_at hv.ungauge initial
  simp only [classicalNLSGauge,hinit]

end NLS.ZakharovShabat
