import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Complex.Basic

/-!
# Gluing compatible holomorphic charts

A chosen chart value defines a function on the union of the chart
domains. Agreement on overlaps proves exact local representation,
independence of the choice, and holomorphy on the whole open union.
-/

noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis

def glueHolomorphicCharts {ι E F : Type*} [Zero F]
    (U : ι → Set E) (f : ι → E → F) (x : E) : F := by
  classical
  exact if h : ∃ i, x ∈ U i then f (Classical.choose h) x else 0

theorem glueHolomorphicCharts_eq_on
    {ι E F : Type*} [Zero F] (U : ι → Set E) (f : ι → E → F)
    (hcompat : ∀ i j, EqOn (f i) (f j) (U i ∩ U j))
    (i : ι) : EqOn (glueHolomorphicCharts U f) (f i) (U i) := by
  classical
  intro x hx
  have hex : ∃ j, x ∈ U j := ⟨i,hx⟩
  rw [glueHolomorphicCharts,dif_pos hex]
  exact hcompat (Classical.choose hex) i ⟨Classical.choose_spec hex,hx⟩

theorem glueHolomorphicCharts_eventuallyEq
    {ι E F : Type*} [TopologicalSpace E] [Zero F]
    (U : ι → Set E) (f : ι → E → F) (hU : ∀ i, IsOpen (U i))
    (hcompat : ∀ i j, EqOn (f i) (f j) (U i ∩ U j))
    (i : ι) (x : E) (hx : x ∈ U i) :
    glueHolomorphicCharts U f =ᶠ[𝓝 x] f i := by
  filter_upwards [(hU i).mem_nhds hx] with y hy
  exact glueHolomorphicCharts_eq_on U f hcompat i hy

theorem differentiableOn_glueHolomorphicCharts
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (U : ι → Set E) (f : ι → E → F) (hU : ∀ i, IsOpen (U i))
    (hcompat : ∀ i j, EqOn (f i) (f j) (U i ∩ U j))
    (hf : ∀ i, DifferentiableOn ℂ (f i) (U i)) :
    DifferentiableOn ℂ (glueHolomorphicCharts U f) (⋃ i, U i) := by
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  have hlocal := glueHolomorphicCharts_eventuallyEq U f hU hcompat i x hi
  exact (((hf i x hi).differentiableAt ((hU i).mem_nhds hi)).congr_of_eventuallyEq hlocal).differentiableWithinAt

end NLS.ComplexAnalysis
