import NLS.Fourier.FourierNLSConservedBound

/-! # Smooth continuation past every finite endpoint

The conserved physical mass and energy supply the absolute Fourier bound
required by local continuation. There is no assumed endpoint value, limit,
or bound on the trajectory. The extended curve is an actual classical NLS
solution and retains all old values on the half-open interval.
-/
noncomputable section
open Set NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.Fourier

/-- Smooth initial data rule out a finite right endpoint of a Fourier NLS
trajectory. The equation is assumed only on closed truncations before it. -/
theorem exists_fourierNLS_extension_of_smooth_Ico
    (a b : ℝ) (hab : a < b) (u : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1)
    (hu : ∀ c ∈ Ico a b, IsFourierNLSTrajectoryOn SpectralWeight.one a c u)
    (hall : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*(u a).val n) 1) :
    ∃ d > b, ∃ z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1,
      IsFourierNLSTrajectoryOn SpectralWeight.one a d z ∧ EqOn z u (Ico a b) ∧
      IsClassicalNLSTrajectoryOn a d (fourierNLSPhysicalCurve SpectralWeight.one z) := by
  let u₀ := fourierNLSHilbertData (u a) (hall 1 (by norm_num))
  have hbnd (r : ℝ) (hr : r ∈ Ico a b) : ‖u r‖ ≤ nlsConservedBound u₀ :=
    (hu r hr).norm_le_conserved a ⟨le_rfl,hr.1⟩ hall u₀
      (fourierNLSHilbertData_apply _ _) r ⟨hr.1,le_rfl⟩
  obtain ⟨d,hd,z,hz,he⟩ := exists_fourierNLS_extension_of_bounded_Ico
    SpectralWeight.one a b hab u hu (nlsConservedBound u₀) (nlsConservedBound_nonneg u₀) hbnd
  refine ⟨d,hd,z,hz,he,hz.isClassical_physical_of_all_sobolev a ⟨le_rfl,hab.le.trans hd.le⟩ ?_⟩
  intro s hs
  simpa only [he ⟨le_rfl,hab⟩] using hall s hs

/-- The corresponding backward continuation theorem at a finite left endpoint. -/
theorem exists_fourierNLS_extension_of_smooth_Ioc
    (a b : ℝ) (hab : a < b) (u : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1)
    (hu : ∀ c ∈ Ioc a b, IsFourierNLSTrajectoryOn SpectralWeight.one c b u)
    (hall : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*(u b).val n) 1) :
    ∃ d < a, ∃ z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1,
      IsFourierNLSTrajectoryOn SpectralWeight.one d b z ∧ EqOn z u (Ioc a b) ∧
      IsClassicalNLSTrajectoryOn d b (fourierNLSPhysicalCurve SpectralWeight.one z) := by
  let u₀ := fourierNLSHilbertData (u b) (hall 1 (by norm_num))
  have hbnd (r : ℝ) (hr : r ∈ Ioc a b) : ‖u r‖ ≤ nlsConservedBound u₀ :=
    (hu r hr).norm_le_conserved b ⟨hr.2,le_rfl⟩ hall u₀
      (fourierNLSHilbertData_apply _ _) r ⟨le_rfl,hr.2⟩
  obtain ⟨d,hd,z,hz,he⟩ := exists_fourierNLS_extension_of_bounded_Ioc
    SpectralWeight.one a b hab u hu (nlsConservedBound u₀) (nlsConservedBound_nonneg u₀) hbnd
  refine ⟨d,hd,z,hz,he,hz.isClassical_physical_of_all_sobolev b ⟨hd.le.trans hab.le,le_rfl⟩ ?_⟩
  intro s hs
  simpa only [he ⟨hab,le_rfl⟩] using hall s hs

/-- Right continuation directly from arbitrary smooth periodic physical
initial data, with no supplied weighted membership or norm bound. -/
theorem exists_fourierNLS_extension_of_smooth_periodic_Ico
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (a b : ℝ) (hab : a < b) (u : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1)
    (hu : ∀ c ∈ Ico a b, IsFourierNLSTrajectoryOn SpectralWeight.one a c u)
    (hinit : ∀ n : ℤ, (u a).val n = periodOneCoefficient f n) :
    ∃ d > b, ∃ z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1,
      IsFourierNLSTrajectoryOn SpectralWeight.one a d z ∧ EqOn z u (Ico a b) ∧
      IsClassicalNLSTrajectoryOn a d (fourierNLSPhysicalCurve SpectralWeight.one z) := by
  apply exists_fourierNLS_extension_of_smooth_Ico a b hab u hu
  intro s hs
  simpa only [hinit] using memlp_periodOneCoefficient_sobolev_one s hs f hf hp

/-- Left continuation from smooth periodic physical initial data. -/
theorem exists_fourierNLS_extension_of_smooth_periodic_Ioc
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (a b : ℝ) (hab : a < b) (u : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1)
    (hu : ∀ c ∈ Ioc a b, IsFourierNLSTrajectoryOn SpectralWeight.one c b u)
    (hinit : ∀ n : ℤ, (u b).val n = periodOneCoefficient f n) :
    ∃ d < a, ∃ z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1,
      IsFourierNLSTrajectoryOn SpectralWeight.one d b z ∧ EqOn z u (Ioc a b) ∧
      IsClassicalNLSTrajectoryOn d b (fourierNLSPhysicalCurve SpectralWeight.one z) := by
  apply exists_fourierNLS_extension_of_smooth_Ioc a b hab u hu
  intro s hs
  simpa only [hinit] using memlp_periodOneCoefficient_sobolev_one s hs f hf hp

end NLS.Fourier
