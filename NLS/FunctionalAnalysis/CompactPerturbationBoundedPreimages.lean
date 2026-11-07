import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Compact remainders of a Banach isomorphism yield compact inverse
images after restricting to a closed set on which the remainders have
relatively compact images. No global properness is inferred. -/
noncomputable section
open Set
namespace NLS.FunctionalAnalysis
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem isCompact_preimage_inter_of_compact_remainders
    (f P L : E → F) (e : E ≃L[𝕜] F) (hf : Continuous f)
    (he : ∀ x, f x=e x+P x-L x)
    (S : Set E) (hS : IsClosed S)
    (hP : IsCompact (closure (P '' S))) (hL : IsCompact (closure (L '' S)))
    (K : Set F) (hK : IsCompact K) : IsCompact (f ⁻¹' K ∩ S) := by
  let g : F × (F × F) → E := fun p => e.symm (p.1-p.2.1+p.2.2)
  have hg : Continuous g := e.symm.continuous.comp
    ((continuous_fst.sub (continuous_fst.comp continuous_snd)).add
      (continuous_snd.comp continuous_snd))
  have hc : IsCompact (g '' (K ×ˢ (closure (P '' S) ×ˢ closure (L '' S)))) :=
    (hK.prod (hP.prod hL)).image hg
  apply hc.of_isClosed_subset ((hK.isClosed.preimage hf).inter hS)
  intro x hx
  refine ⟨(f x,P x,L x),⟨hx.1,subset_closure ⟨x,hx.2,rfl⟩,
    subset_closure ⟨x,hx.2,rfl⟩⟩,?_⟩
  dsimp only [g]
  rw [he]
  have ha : e x+P x-L x-P x+L x=e x := by abel
  rw [ha,e.symm_apply_apply]

end NLS.FunctionalAnalysis
