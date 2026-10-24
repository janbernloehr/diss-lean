import NLS.FunctionalAnalysis.InverseCayleyCoordinate
import NLS.ZakharovShabat.L2WholeLineCayleyMeasureNoAtoms

/-! # Transport of the actual physical Cayley measures to the real line -/
noncomputable section
set_option autoImplicit false
open MeasureTheory NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The actual physical scalar measure transported by the inverse Cayley coordinate.
The exceptional fiber at one has already been proved null. The identification
with the unbounded resolvent still requires its integral representation. -/
def wholeLineRealSpectralMeasure (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2) : Measure ℝ :=
  (wholeLineCayleySpectralMeasure u hu v).map
    (fun x : spectrum ℂ (wholeLineCayley u hu) => inverseCayleyReal x)

instance wholeLineRealSpectralMeasure_isFiniteMeasure (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2) :
    IsFiniteMeasure (wholeLineRealSpectralMeasure u hu v) := by
  unfold wholeLineRealSpectralMeasure
  infer_instance

/-- Transport preserves the original squared Hilbert norm as total mass. -/
theorem wholeLineRealSpectralMeasure_real_univ (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2) :
    (wholeLineRealSpectralMeasure u hu v).real Set.univ = ‖v‖^2 := by
  have hm : Measurable (fun x : spectrum ℂ (wholeLineCayley u hu) => inverseCayleyReal x) :=
    measurable_inverseCayleyReal.comp measurable_subtype_coe
  rw [Measure.real,wholeLineRealSpectralMeasure,Measure.map_apply hm MeasurableSet.univ]
  exact wholeLineCayleySpectralMeasure_real_univ u hu v

/-- A real-coordinate fiber lies in the union of its true Cayley fiber and the
exceptional fiber at one, both of which have zero actual spectral mass. -/
instance wholeLineRealSpectralMeasure_nullSingletonClass (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2) :
    NullSingletonClass (wholeLineRealSpectralMeasure u hu v) := by
  constructor
  intro t
  have hm : Measurable (fun x : spectrum ℂ (wholeLineCayley u hu) => inverseCayleyReal x) :=
    measurable_inverseCayleyReal.comp measurable_subtype_coe
  rw [wholeLineRealSpectralMeasure,Measure.map_apply hm (measurableSet_singleton t)]
  apply measure_mono_null (t := {x : spectrum ℂ (wholeLineCayley u hu) | (x : ℂ) = 1} ∪
    {x | (x : ℂ) = ((t : ℂ)-Complex.I)/((t : ℂ)+Complex.I)})
  · intro x hx
    change inverseCayleyReal (x : ℂ) = t at hx
    by_cases hone : (x : ℂ) = 1
    · exact Or.inl hone
    · apply Or.inr
      have he := cayley_inverseCayleyReal x
        (wholeLineCayley_spectrum_subset_unitary u hu x.property) hone
      rw [hx] at he
      exact he.symm
  · exact measure_union_null
      (wholeLineCayleySpectralMeasure_coordinate_fiber_zero u hu v 1)
      (wholeLineCayleySpectralMeasure_coordinate_fiber_zero u hu v _)

/-- Every countable subset of the real line has zero transported physical measure. -/
theorem wholeLineRealSpectralMeasure_countable_zero (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2)
    (s : Set ℝ) (hs : s.Countable) : wholeLineRealSpectralMeasure u hu v s = 0 :=
  hs.measure_zero _

end NLS.ZakharovShabat
