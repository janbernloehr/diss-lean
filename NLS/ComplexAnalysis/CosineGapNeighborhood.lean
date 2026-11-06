import NLS.ComplexAnalysis.CosineSegmentGeometry
import Mathlib.Topology.Compactness.Compact

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem exists_open_cosineGapPoint_real_neighborhood
    {A : Type*} [TopologicalSpace A] (τ δ : A → ℂ) (hτ : Continuous τ) (hδ : Continuous δ)
    (E : Set ℂ) (hE : IsOpen E) (a : A)
    (hgap : segment ℝ (τ a-δ a) (τ a+δ a) ⊆ E) :
    ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ ∀ b ∈ V, ∀ θ ∈ Icc (0 : ℝ) Real.pi,
      cosineGapPoint (τ b) (δ b) (θ : ℂ) ∈ E := by
  let T : ℂ × A → ℂ := fun x => cosineGapPoint (τ x.2) (δ x.2) x.1
  have hT : Continuous T := by
    exact (hτ.comp continuous_snd).add ((hδ.comp continuous_snd).mul
      (Complex.continuous_cos.comp continuous_fst))
  let K : Set ℂ := Complex.ofReal '' Icc (0 : ℝ) Real.pi
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hbase : K ×ˢ {a} ⊆ T ⁻¹' E := by
    rintro ⟨z,b⟩ ⟨⟨θ,hθ,hz⟩,hb⟩
    have he : b = a := hb
    subst b
    change (θ : ℂ) = z at hz
    subst z
    exact hgap (cosineGapPoint_real_mem_segment (τ a) (δ a) θ)
  obtain ⟨U,V,_,hV,hKU,haV,hUV⟩ := generalized_tube_lemma hK isCompact_singleton (hE.preimage hT) hbase
  refine ⟨V,hV,haV (mem_singleton _),?_⟩
  intro b hb θ hθ
  have hm : ((θ : ℂ),b) ∈ U ×ˢ V := ⟨hKU ⟨θ,hθ,rfl⟩,hb⟩
  exact hUV hm

end NLS.ComplexAnalysis
