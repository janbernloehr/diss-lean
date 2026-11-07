import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Uniform estimates pull back through one analytic germ and its exact
coefficient diagram, on a common open neighborhood. -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis

theorem exists_uniform_analytic_pullback
    {𝕜 E F Q A : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup Q] [NormedSpace 𝕜 Q]
    (L : E →L[𝕜] Q) (D : Set Q) (hD : IsOpen D) (q : E) (hqD : L q∈D)
    (U : Set E) (hU : IsOpen U) (hqU : q∈U) (g : E → F) (hg : AnalyticOnNhd 𝕜 g U)
    (B : Set F) (hB : IsOpen B) (hgq : g q∈B)
    (R : Q → A) (S : F → A) (he : ∀ p∈U, S (g p)=R (L p))
    (Bound : A → Prop) (hb : ∀ b∈B, Bound (S b)) :
    ∃ V : Set E, IsOpen V ∧ q∈V ∧ V⊆U ∧ ∀ p∈V, L p∈D ∧ Bound (R (L p)) := by
  let V := (U∩g ⁻¹' B)∩L ⁻¹' D
  refine ⟨V,(hg.continuousOn.isOpen_inter_preimage hU hB).inter (hD.preimage L.continuous),
    ⟨⟨hqU,hgq⟩,hqD⟩,(fun p hp => hp.1.1),?_⟩
  intro p hp
  exact ⟨hp.2,he p hp.1.1 ▸ hb (g p) hp.1.2⟩

end NLS.ComplexAnalysis
