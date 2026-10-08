import NLS.ZakharovShabat.SmoothNLSData
import NLS.ZakharovShabat.SourceFiniteGapMassDivergence

/-! # Smooth initial data are sequentially dense in the original source norm -/
noncomputable section
open Set Filter Topology NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real finite-gap source has a smooth physical initial representative. -/
def smoothNLSDataOfFiniteGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) : SmoothNLSData where
  value := sourceFiniteGapClassicalTrajectory hp hp1 φ hf 0
  smooth := (sourceFiniteGapClassicalTrajectory_spec hp hp1 φ hf).1.spatial_smooth 0
  periodic := (sourceFiniteGapClassicalTrajectory_spec hp hp1 φ hf).1.periodic 0

@[simp] theorem smoothNLSDataOfFiniteGap_source (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    (smoothNLSDataOfFiniteGap hp hp1 φ hf).source p = φ := by
  apply realTypeSource_eq_of_fst
  intro n
  rw [SmoothNLSData.source,smoothPeriodOneSourceAt_fst]
  change periodOneCoefficient (fun x : ℝ =>
    sourceFiniteGapClassicalTrajectory hp hp1 φ hf 0 (x : AddCircle (2 : ℝ))) n = _
  rw [funext (sourceFiniteGapClassicalTrajectory_spec hp hp1 φ hf).2]
  exact (periodOneCoefficient_sourceFiniteGapPhysicalPair hp hp1 φ hf n).1

/-- Every finite-p real source is a limit of smooth physical initial data.
This witnesses non-vacuity of the all-smooth-sequence solution definition. -/
theorem exists_smoothNLSData_sequence (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) :
    ∃ f : ℕ → SmoothNLSData, Tendsto (fun j => (f j).source p) atTop (𝓝 φ) := by
  obtain ⟨ψ,hf,hψ⟩ := exists_sourceFiniteGap_sequence hp hp1 φ
  refine ⟨fun j => smoothNLSDataOfFiniteGap hp hp1 (ψ j) (hf j),?_⟩
  simpa only [smoothNLSDataOfFiniteGap_source] using hψ

end NLS.ZakharovShabat
