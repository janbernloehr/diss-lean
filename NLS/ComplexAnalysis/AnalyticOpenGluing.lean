import NLS.ComplexAnalysis.AnalyticGermSign

/-! # Exact analytic gluing on open covers

One total function retains every supplied chart on its entire domain.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.ComplexAnalysis

theorem exists_analytic_open_gluing
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) (f : ι → E → F)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) (U i))
    (he : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) :
    ∃ g : E → F, AnalyticOnNhd ℂ g (⋃ i, U i) ∧ ∀ i, EqOn g (f i) (U i) := by
  classical
  let pick : {x // x ∈ ⋃ i, U i} → ι := fun x => Classical.choose (mem_iUnion.mp x.property)
  have hpick (x : {x // x ∈ ⋃ i, U i}) : x.val ∈ U (pick x) :=
    Classical.choose_spec (mem_iUnion.mp x.property)
  let g : E → F := fun x => if h : x ∈ ⋃ i, U i then f (pick ⟨x,h⟩) x else 0
  have hg (i : ι) : EqOn g (f i) (U i) := by
    intro x hx
    have hm : x ∈ ⋃ j, U j := mem_iUnion.mpr ⟨i,hx⟩
    dsimp only [g]
    rw [dif_pos hm]
    exact he (pick ⟨x,hm⟩) i ⟨hpick ⟨x,hm⟩,hx⟩
  refine ⟨g,?_,hg⟩
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  have hnear : f i =ᶠ[𝓝 x] g := by
    filter_upwards [(hU i).mem_nhds hi] with y hy
    exact (hg i hy).symm
  exact (hf i x hi).congr hnear

end NLS.ComplexAnalysis
