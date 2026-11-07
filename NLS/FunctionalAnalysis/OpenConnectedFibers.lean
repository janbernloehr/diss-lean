import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions.SumProd

/-! # Connectedness of an open product domain with connected vertical fibers -/
open Set
namespace NLS.FunctionalAnalysis
variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

theorem isPreconnected_open_product_of_fibers (S : Set (E × F)) (B : Set F)
    (hS : IsOpen S) (hB : IsPreconnected B) (hproj : Prod.snd '' S = B)
    (hfib : ∀ b ∈ B, IsPreconnected {a : E | (a,b) ∈ S}) : IsPreconnected S := by
  intro U V hU hV hcover hSU hSV
  let P := Prod.snd '' (S ∩ U)
  let Q := Prod.snd '' (S ∩ V)
  have hP : IsOpen P := isOpenMap_snd _ (hS.inter hU)
  have hQ : IsOpen Q := isOpenMap_snd _ (hS.inter hV)
  have hcov : B ⊆ P ∪ Q := by
    intro b hb
    rw [← hproj] at hb
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := hb
    rcases hcover hab with h | h
    · exact Or.inl ⟨(a,b),⟨hab,h⟩,rfl⟩
    · exact Or.inr ⟨(a,b),⟨hab,h⟩,rfl⟩
  have hBP : (B ∩ P).Nonempty := by
    obtain ⟨⟨a,b⟩,hab,hu⟩ := hSU
    exact ⟨b,hproj ▸ mem_image_of_mem Prod.snd hab,⟨(a,b),⟨hab,hu⟩,rfl⟩⟩
  have hBQ : (B ∩ Q).Nonempty := by
    obtain ⟨⟨a,b⟩,hab,hv⟩ := hSV
    exact ⟨b,hproj ▸ mem_image_of_mem Prod.snd hab,⟨(a,b),⟨hab,hv⟩,rfl⟩⟩
  obtain ⟨b,hb,hbP,hbQ⟩ := hB P Q hP hQ hcov hBP hBQ
  obtain ⟨⟨a,b⟩,⟨hab,haU⟩,rfl⟩ := hbP
  obtain ⟨⟨a',b⟩,⟨ha'b,ha'V⟩,rfl⟩ := hbQ
  have hu : IsOpen {a : E | (a,b) ∈ U} := hU.preimage (continuous_id.prodMk continuous_const)
  have hv : IsOpen {a : E | (a,b) ∈ V} := hV.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨c,hc,hcU,hcV⟩ := hfib b hb _ _ hu hv
    (fun a ha => hcover ha) ⟨a,hab,haU⟩ ⟨a',ha'b,ha'V⟩
  exact ⟨(c,b),hc,hcU,hcV⟩

end NLS.FunctionalAnalysis
