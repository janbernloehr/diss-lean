import NLS.Fourier.SmoothPeriodicCoefficients
import NLS.Fourier.FourierNLSPhysicalSynthesis

/-! # Local Fourier NLS existence from arbitrary smooth periodic physical data

The initial coefficients are the actual unit-period Fourier integrals. Every
Sobolev membership is derived from physical smoothness, and synthesis recovers
the prescribed initial function everywhere. The local interval is common to
all orders and the physical curve is continuous in the uniform norm.
-/
noncomputable section
open Set
open scoped ContDiff
namespace NLS.Fourier

/-- Canonical original coefficients of arbitrary smooth period-one initial data. -/
def smoothPeriodOneFourierData (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    WeightedCoeff SpectralWeight.one.toWeight 1 := ⟨periodOneCoefficient f,by
  have h := memlp_periodOneCoefficient_sobolev_one 0 le_rfl f hf hp
  change Memℓp (fun n => (SpectralWeight.one n : ℂ)*periodOneCoefficient f n) 1
  simpa only [SpectralWeight.one_apply,Weight.sobolev_apply,Real.rpow_zero] using h⟩

@[simp] theorem smoothPeriodOneFourierData_apply (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f 1) (n : ℤ) :
    (smoothPeriodOneFourierData f hf hp).val n = periodOneCoefficient f n := rfl

/-- Physical smoothness supplies all weighted assumptions of local smooth Fourier existence. -/
theorem smoothPeriodOneFourierData_all_sobolev (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f 1) (s : ℝ) (hs : 0 ≤ s) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*(smoothPeriodOneFourierData f hf hp).val n) 1 :=
  memlp_periodOneCoefficient_sobolev_one s hs f hf hp

/-- Reconstruction of the original smooth function is pointwise, with no choice of representative. -/
theorem periodOneSynthesis_smoothPeriodOneFourierData (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f 1) :
    periodOneSynthesis (SpectralWeight.one.toCoeff (smoothPeriodOneFourierData f hf hp)) = f := by
  apply eq_of_periodOneCoefficient_eq _ f (continuous_periodOneSynthesis _) hf.continuous
    (periodOneSynthesis_periodic _) hp
  intro n
  simp only [periodOneCoefficient_synthesis,SpectralWeight.toCoeff_apply,smoothPeriodOneFourierData_apply]

/-- Arbitrary smooth period-one physical data produce a local Fourier NLS
trajectory on one interval for all Sobolev orders. Its physical realization
is continuous in uniform norm, spatially smooth, periodic, and starts at the
original function. Identification of the physical time derivative is separate. -/
theorem exists_local_fourierNLS_of_smooth_periodic
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    ∃ T > 0, ∃ z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1,
      z 0 = smoothPeriodOneFourierData f hf hp ∧
      IsFourierNLSTrajectoryOn SpectralWeight.one (-T) T z ∧
      (fun x : ℝ => fourierNLSPhysicalCurve SpectralWeight.one z 0 (x : AddCircle (2 : ℝ))) = f ∧
      ContinuousOn (fourierNLSPhysicalCurve SpectralWeight.one z) (Icc (-T) T) ∧
      (∀ s : ℝ, ∀ hs : 0 ≤ s,
        ∃ u : ℝ → WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1,
          IsFourierNLSTrajectoryOn (SpectralWeight.sobolev s hs) (-T) T u ∧
          ∀ time ∈ Icc (-T) T, ∀ n : ℤ, (u time).val n = (z time).val n) ∧
      ∀ time ∈ Icc (-T) T,
        Function.Periodic (fun x : ℝ => fourierNLSPhysicalCurve SpectralWeight.one z time (x : AddCircle (2 : ℝ))) 1 ∧
        ContDiff ℝ ∞ (fun x : ℝ => fourierNLSPhysicalCurve SpectralWeight.one z time (x : AddCircle (2 : ℝ))) := by
  obtain ⟨T,hT,z,hz0,hz,hlift,hsmooth⟩ := exists_local_fourierNLS_all_sobolev SpectralWeight.one
    (smoothPeriodOneFourierData f hf hp) (smoothPeriodOneFourierData_all_sobolev f hf hp)
  refine ⟨T,hT,z,hz0,hz,?_,hz.continuous_physical,hlift,?_⟩
  · simpa only [fourierNLSPhysicalCurve_apply,hz0] using periodOneSynthesis_smoothPeriodOneFourierData f hf hp
  · intro time ht
    exact ⟨fourierNLSPhysicalCurve_periodic _ z time,hsmooth time ht⟩

end NLS.Fourier
