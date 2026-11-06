import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Pulling an open local quotient back through a continuous lift -/
open Set
namespace NLS.ComplexAnalysis
variable {A B C D : Type*} [TopologicalSpace A] [TopologicalSpace B]

/-- A quotient chart in an intermediate image lifts to an open source
neighborhood with exact image and exact recovery. -/
theorem exists_local_factor_lift (Q : A → B) (P : B → C) (f : A → D) (G : B → D) (g : C → D)
    (V : Set A) (S : Set B) (T : Set C) (a : A)
    (hQ : Continuous Q) (hV : IsOpen V) (hS : IsOpen S) (ha : a ∈ V) (hQa : Q a ∈ S)
    (hSsub : S ⊆ Q '' V) (himage : P '' S = T)
    (hrec : ∀ z ∈ V, G (Q z) = f z) (hg : ∀ b ∈ S, g (P b) = G b) :
    ∃ Z : Set A, IsOpen Z ∧ a ∈ Z ∧ Z ⊆ V ∧
      (fun z => P (Q z)) '' Z = T ∧ ∀ z ∈ Z, g (P (Q z)) = f z := by
  refine ⟨V ∩ Q ⁻¹' S,hV.inter (hS.preimage hQ),⟨ha,hQa⟩,fun _ hz => hz.1,?_,?_⟩
  · rw [← himage]
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨Q z,hz.2,rfl⟩
    · rintro _ ⟨b,hb,rfl⟩
      obtain ⟨z,hz,rfl⟩ := hSsub hb
      exact ⟨z,⟨hz,hb⟩,rfl⟩
  · intro z hz
    exact (hg _ hz.2).trans (hrec z hz.1)

/-- A bounded linear map preserves the zero base point in a pulled-back set. -/
theorem zero_mem_preimage_clm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) (U : Set F) (h0 : (0 : F) ∈ U) : (0 : E) ∈ L ⁻¹' U := by
  change L 0 ∈ U
  rw [map_zero]
  exact h0

end NLS.ComplexAnalysis
