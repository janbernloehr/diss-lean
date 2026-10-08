import NLS.Fourier.FourierNLSPhysicalEquation
import NLS.Fourier.SmoothInitialFourierNLS
import NLS.ZakharovShabat.ClassicalNLSUniqueness

/-! # Local classical NLS existence for arbitrary smooth periodic data

The constructed solution is continuous in the uniform norm on a closed time
interval, differentiable in that norm at interior times, smooth in space,
and satisfies the actual defocusing NLS equation. Global existence is separate.
-/
noncomputable section
open Set
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The interval version of the classical trajectory predicate. Ordinary time
 derivatives are asserted in the interior, so no arbitrary exterior values
 of a locally constructed curve enter the equation. -/
structure IsClassicalNLSTrajectoryOn (a b : ℝ)
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) : Prop where
  continuous : ContinuousOn u (Icc a b)
  time_differentiable : ∀ time ∈ Ioo a b, DifferentiableAt ℝ u time
  spatial_smooth : ∀ time ∈ Icc a b,
    ContDiff ℝ ∞ (fun x : ℝ => u time (x : AddCircle (2 : ℝ)))
  periodic : ∀ time ∈ Icc a b,
    Function.Periodic (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) 1
  equation : ∀ time ∈ Ioo a b, ∀ x : ℝ, deriv u time (x : AddCircle (2 : ℝ)) =
    scalarClassicalNLSVectorField (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x

/-- Every global classical trajectory restricts to the interval predicate. -/
theorem IsClassicalNLSTrajectory.onInterval
    {u : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u) (a b : ℝ) :
    IsClassicalNLSTrajectoryOn a b u :=
  ⟨hu.time_differentiable.continuous.continuousOn,fun time _ => hu.time_differentiable time,
    fun time _ => hu.spatial_smooth time,fun time _ => hu.periodic time,fun time _ => hu.equation time⟩

/-- A smooth Fourier curve with a continuous order-two lift is a local classical
solution of the original physical NLS equation. -/
theorem isClassicalNLSTrajectoryOn_of_fourier
    {a b : ℝ} {z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1}
    (hz : Fourier.IsFourierNLSTrajectoryOn SpectralWeight.one a b z)
    (v : ℝ → WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1)
    (hv : ContinuousOn v (Icc a b))
    (he : ∀ time ∈ Icc a b, ∀ n : ℤ, (v time).val n = (z time).val n)
    (hsmooth : ∀ time ∈ Icc a b,
      ContDiff ℝ ∞ (fun x : ℝ => Fourier.fourierNLSPhysicalCurve SpectralWeight.one z time
        (x : AddCircle (2 : ℝ)))) :
    IsClassicalNLSTrajectoryOn a b (Fourier.fourierNLSPhysicalCurve SpectralWeight.one z) := by
  refine ⟨hz.continuous_physical,?_,hsmooth,?_,?_⟩
  · intro time ht
    obtain ⟨velocity,hd,_⟩ := hz.hasDerivWithinAt_physical v hv he time ⟨ht.1.le,ht.2.le⟩
    exact (hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt
  · intro time _
    exact Fourier.fourierNLSPhysicalCurve_periodic _ z time
  · intro time ht x
    obtain ⟨velocity,hd,hfield⟩ := hz.hasDerivWithinAt_physical v hv he time ⟨ht.1.le,ht.2.le⟩
    rw [(hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
    exact hfield x

/-- Every smooth period-one function is the exact initial value of a local
classical defocusing NLS solution. No coefficient membership or supplied
classical trajectory is assumed. -/
theorem exists_local_classicalNLS_of_smooth_periodic
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    ∃ T > 0, ∃ u : ℝ → C(AddCircle (2 : ℝ), ℂ),
      (fun x : ℝ => u 0 (x : AddCircle (2 : ℝ))) = f ∧
      IsClassicalNLSTrajectoryOn (-T) T u := by
  obtain ⟨T,hT,z,_,hz,hinit,_,hlift,hsmooth⟩ :=
    Fourier.exists_local_fourierNLS_of_smooth_periodic f hf hp
  obtain ⟨v,hv,he⟩ := hlift 2 (by norm_num)
  exact ⟨T,hT,Fourier.fourierNLSPhysicalCurve SpectralWeight.one z,hinit,
    isClassicalNLSTrajectoryOn_of_fourier hz v hv.continuous he (fun time ht => (hsmooth time ht).2)⟩

end NLS.ZakharovShabat
