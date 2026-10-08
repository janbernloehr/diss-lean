import NLS.Fourier.GlobalSmoothFourierNLS

/-! # Global classical NLS existence from arbitrary smooth periodic data

One physical curve is defined for every real time. It satisfies the existing
global classical trajectory predicate and is unique among all such curves
with the same initial value.
-/
noncomputable section
open Set NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Classical trajectories on every symmetric interval form a global
classical trajectory, with ordinary time differentiation at every real time. -/
theorem isClassicalNLSTrajectory_of_symmetric_intervals
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hu : ∀ R > 0, IsClassicalNLSTrajectoryOn (-R) R u) : IsClassicalNLSTrajectory u := by
  have ht (time : ℝ) : time ∈ Ioo (-(|time|+1)) (|time|+1) := by
    constructor <;> linarith [le_abs_self time,neg_abs_le time]
  have hp (time : ℝ) : 0 < |time|+1 := by positivity
  refine ⟨fun time => (hu _ (hp time)).time_differentiable time (ht time),
    fun time => (hu _ (hp time)).spatial_smooth time ⟨(ht time).1.le,(ht time).2.le⟩,
    fun time => (hu _ (hp time)).periodic time ⟨(ht time).1.le,(ht time).2.le⟩,
    fun time x => (hu _ (hp time)).equation time (ht time) x⟩

/-- A smooth all-time Fourier trajectory is an actual global classical
solution of the physical period-one NLS equation. -/
theorem isClassicalNLSTrajectory_of_global_fourier
    (z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1)
    (hz : ∀ a b : ℝ, IsFourierNLSTrajectoryOn SpectralWeight.one a b z)
    (hall : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*(z 0).val n) 1) :
    IsClassicalNLSTrajectory (fourierNLSPhysicalCurve SpectralWeight.one z) := by
  apply isClassicalNLSTrajectory_of_symmetric_intervals
  intro R hR
  exact (hz (-R) R).isClassical_physical_of_all_sobolev 0 ⟨by linarith,hR.le⟩ hall

/-- Every smooth period-one physical initial function has one classical
NLS solution defined for every real time, with its exact prescribed initial value. -/
theorem exists_global_classicalNLS_of_smooth_periodic
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    ∃ u : ℝ → C(AddCircle (2 : ℝ), ℂ),
      (fun x : ℝ => u 0 (x : AddCircle (2 : ℝ))) = f ∧ IsClassicalNLSTrajectory u := by
  obtain ⟨z,hz0,hz⟩ := exists_global_smooth_fourierNLS (smoothPeriodOneFourierData f hf hp)
    (smoothPeriodOneFourierData_all_sobolev f hf hp)
  refine ⟨fourierNLSPhysicalCurve SpectralWeight.one z,?_,?_⟩
  · simpa only [fourierNLSPhysicalCurve_apply,hz0] using periodOneSynthesis_smoothPeriodOneFourierData f hf hp
  · apply isClassicalNLSTrajectory_of_global_fourier z hz
    simpa only [hz0] using smoothPeriodOneFourierData_all_sobolev f hf hp

/-- The global classical solution is unique without a Fourier-space premise
on a competing solution. -/
theorem existsUnique_global_classicalNLS_of_smooth_periodic
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    ∃! u : ℝ → C(AddCircle (2 : ℝ), ℂ),
      (fun x : ℝ => u 0 (x : AddCircle (2 : ℝ))) = f ∧ IsClassicalNLSTrajectory u := by
  obtain ⟨u,hi,hu⟩ := exists_global_classicalNLS_of_smooth_periodic f hf hp
  refine ⟨u,⟨hi,hu⟩,?_⟩
  intro v hv
  apply hv.2.eq_of_eq_at hu 0
  apply ContinuousMap.ext
  intro x
  exact Quotient.inductionOn x (fun r => (congrFun hv.1 r).trans (congrFun hi r).symm)

/-- The uniquely determined global classical solution of smooth periodic data. -/
def globalClassicalNLS (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    ℝ → C(AddCircle (2 : ℝ), ℂ) :=
  (exists_global_classicalNLS_of_smooth_periodic f hf hp).choose

theorem globalClassicalNLS_initial (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    (fun x : ℝ => globalClassicalNLS f hf hp 0 (x : AddCircle (2 : ℝ))) = f :=
  (exists_global_classicalNLS_of_smooth_periodic f hf hp).choose_spec.1

theorem globalClassicalNLS_isClassical (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    IsClassicalNLSTrajectory (globalClassicalNLS f hf hp) :=
  (exists_global_classicalNLS_of_smooth_periodic f hf hp).choose_spec.2

end NLS.ZakharovShabat
