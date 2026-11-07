import NLS.SequenceSpaces.BoundedAnalyticSymbolExponent
import NLS.ComplexAnalysis.AnalyticGermPullback

/-! # Physical symbol-packet germs retaining a compact derivative principal -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Coeff

theorem analytic_symbol_packet_compact_germ_properties
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {p : ℝ≥0∞} [Fact (1≤p)] (hp : p≠⊤)
    (L : E →L[ℂ] H) (D : Set H) (hD : IsOpen D) (q : E) (hqD : L q∈D)
    (U : Set E) (hU : IsOpen U) (hqU : q∈U)
    (σ : H → Coeff ⊤) (hσ : AnalyticOnNhd ℂ σ D)
    (F : E → Coeff p) (hF : AnalyticOnNhd ℂ F U)
    (Q : E →L[ℂ] Coeff p) (hFc : IsCompactOperator (fderiv ℂ F q-Q))
    (A : Coeff p →L[ℂ] Coeff p) (P : E → Coeff p → Prop)
    (hP : ∀ x, x∈U → L x∈D → P x (A (holderProduct (q := p) (σ (L x)) (F x)))) :
    ∃ V : Set E, IsOpen V ∧ q∈V ∧ ∃ G : E → Coeff p,
      AnalyticOnNhd ℂ G V ∧
      IsCompactOperator (fderiv ℂ G q-A.comp ((holderProduct (q := p) (σ (L q))).comp Q)) ∧
      ∀ x∈V, P x (G x) := by
  let V := U∩L ⁻¹' D
  let B : E → Coeff p := fun x => holderProduct (q := p) (σ (L x)) (F x)
  have hBa : AnalyticOnNhd ℂ B V := by
    intro x hx
    exact (holderProduct.analyticAt_bilinear _).comp₂
      ((hσ (L x) hx.2).comp (L.analyticAt x)) (hF x hx.1)
  have hBc := isCompactOperator_fderiv_symbol_packet_sub_principal_exponent hp
    (fun x => σ (L x)) F q
    (((hσ (L q) hqD).comp (L.analyticAt q)).differentiableAt)
    (hF q hqU).differentiableAt Q hFc
  refine ⟨V,hU.inter (hD.preimage L.continuous),⟨hqU,hqD⟩,
    (fun x => A (B x)),?_,?_,?_⟩
  · intro x hx
    exact (A.analyticAt _).comp (hBa x hx)
  · have he := (A.hasFDerivAt.comp q (hBa q ⟨hqU,hqD⟩).differentiableAt.hasFDerivAt).fderiv
    change IsCompactOperator (fderiv ℂ (A ∘ B) q-A.comp ((holderProduct (q := p) (σ (L q))).comp Q))
    rw [he]
    have he' : A.comp (fderiv ℂ B q-(holderProduct (q := p) (σ (L q))).comp Q)=
        A.comp (fderiv ℂ B q)-A.comp ((holderProduct (q := p) (σ (L q))).comp Q) := by
      apply ContinuousLinearMap.ext
      intro x
      exact map_sub A _ _
    rw [←he']
    exact hBc.clm_comp A
  · intro x hx
    exact hP x hx.1 hx.2

end NLS.Coeff
