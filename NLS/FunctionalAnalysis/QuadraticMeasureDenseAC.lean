import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Extending absolute continuity of quadratic vector measures by density -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace NLS.FunctionalAnalysis
variable {X E D : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

/-- Finite vector measures with squared-norm mass and the quadratic sum bound
are absolutely continuous for every vector once this holds on a dense range. -/
theorem absolutelyContinuous_quadraticMeasure_of_denseRange
    (μ : E → Measure X) [∀ v, IsFiniteMeasure (μ v)]
    (hmass : ∀ v, (μ v).real univ = ‖v‖^2)
    (hadd : ∀ v w, μ (v+w) ≤ (μ v+μ v)+(μ w+μ w))
    (f : D → E) (hd : DenseRange f) (ν : Measure X)
    (hf : ∀ d, μ (f d) ≪ ν) (v : E) : μ v ≪ ν := by
  intro s hs
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ measureReal_nonneg
  by_contra hn
  have hm : 0 < (μ v).real s := lt_of_not_ge hn
  let δ := Real.sqrt ((μ v).real s)
  have hδ : 0 < δ := Real.sqrt_pos.mpr hm
  have hδsq : δ^2 = (μ v).real s := Real.sq_sqrt hm.le
  obtain ⟨d,hdist⟩ := Metric.denseRange_iff.mp hd v (δ/2) (by positivity)
  rw [dist_eq_norm] at hdist
  have hz : μ (f d) s = 0 := hf d hs
  have hb : μ v s ≤ μ (v-f d) univ+μ (v-f d) univ := by
    calc
      _ ≤ μ (v-f d) s+μ (v-f d) s := by
        simpa only [sub_add_cancel, Measure.add_apply, hz, add_zero] using hadd (v-f d) (f d) s
      _ ≤ _ := add_le_add (measure_mono (subset_univ _)) (measure_mono (subset_univ _))
  have hr := ENNReal.toReal_mono (by finiteness) hb
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hr
  change (μ v).real s ≤ (μ (v-f d)).real univ+(μ (v-f d)).real univ at hr
  rw [hmass] at hr
  have hsmall : ‖v-f d‖^2 < (δ/2)^2 :=
    (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mpr hdist
  nlinarith

end NLS.FunctionalAnalysis
