import NLS.ComplexAnalysis.AnalyticDomainPullback

/-! Combine an original-source uniform bound with common scalar family
analyticity through the exact bounded source inclusion. -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis

theorem exists_analytic_family_bound_pullback
    {𝕜 E Q ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Q] [NormedSpace 𝕜 Q]
    (L : E →L[𝕜] Q) (D : Set Q) (V : Set E) (hV : IsOpen V) (T : Set Q) (hT : IsOpen T)
    (q : E) (hqV : q∈V) (hqT : L q∈T) (R : ι → Q → 𝕜)
    (hRa : ∀ i,AnalyticOnNhd 𝕜 (R i) T) (Bound : Q → Prop)
    (hd : ∀ p∈V,L p∈D) (hb : ∀ p∈V,Bound (L p)) :
    ∃ U : Set E,IsOpen U ∧ q∈U ∧ (∀ p∈U,L p∈D) ∧
      (∀ i,AnalyticOnNhd 𝕜 (fun p => R i (L p)) U) ∧ ∀ p∈U,Bound (L p) := by
  let U := V∩L ⁻¹' T
  refine ⟨U,hV.inter (hT.preimage L.continuous),⟨hqV,hqT⟩,(fun p hp => hd p hp.1),?_,fun p hp => hb p hp.1⟩
  intro i
  exact (analyticOnNhd_clm_preimage L (R i) T (hRa i)).mono inter_subset_right

end NLS.ComplexAnalysis
