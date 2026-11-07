import NLS.ComplexAnalysis.AnalyticDomainPullback

/-! A bounded analytic Banach-valued realization pulls back through an
actual stronger germ with its exact original-source observation. -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis

theorem exists_bounded_analytic_pullback
    {𝕜 E G Q Y Z : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup Q] [NormedSpace 𝕜 Q] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (L : E →L[𝕜] Q) (D : Set Q) (hD : IsOpen D) (q : E) (hqD : L q∈D)
    (V : Set E) (hV : IsOpen V) (hqV : q∈V) (g : E → G) (hga : AnalyticOnNhd 𝕜 g V)
    (B : Set G) (hB : IsOpen B) (hgqB : g q∈B) (R : G → Y) (hRa : AnalyticOnNhd 𝕜 R B)
    (C : ℝ) (hb : ∀ a∈B,‖R a‖≤C) (obs : Y → Z) (T : Q → Z)
    (he : ∀ p∈V,g p∈B → obs (R (g p))=T (L p)) :
    ∃ U : Set E,IsOpen U ∧ q∈U ∧ U⊆V ∧ ∃ F : E → Y,AnalyticOnNhd 𝕜 F U ∧
      ∀ p∈U,L p∈D ∧ ‖F p‖≤C ∧ obs (F p)=T (L p) := by
  let U := (V∩g ⁻¹' B)∩L ⁻¹' D
  refine ⟨U,(hga.continuousOn.isOpen_inter_preimage hV hB).inter (hD.preimage L.continuous),
    ⟨⟨hqV,hgqB⟩,hqD⟩,(fun _ hp => hp.1.1),(fun p => R (g p)),?_,?_⟩
  · intro p hp
    exact (hRa (g p) hp.1.2).comp (hga p hp.1.1)
  · intro p hp
    exact ⟨hp.2,hb (g p) hp.1.2,he p hp.1.1 hp.1.2⟩

end NLS.ComplexAnalysis
