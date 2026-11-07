import NLS.SequenceSpaces.BoundedAnalyticSymbol

/-! # Compact analytic symbol-packet derivatives at every finite exponent -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

/-- The ACTUAL full analytic symbol multiplies the given compact
principal derivative. Symbol differentiation remains compact. -/
theorem isCompactOperator_fderiv_symbol_packet_sub_principal_exponent
    {p : ℝ≥0∞} [Fact (1≤p)] (hp : p≠⊤)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : E → Coeff ⊤) (F : E → Coeff p) (q : E)
    (hσ : DifferentiableAt ℂ σ q) (hF : DifferentiableAt ℂ F q)
    (Q : E →L[ℂ] Coeff p) (hQ : IsCompactOperator (fderiv ℂ F q-Q)) :
    IsCompactOperator (fderiv ℂ (fun x => holderProduct (q := p) (σ x) (F x)) q-
      (holderProduct (q := p) (σ q)).comp Q) := by
  let M := holderProduct (p := ⊤) (r := p) (q := p) (σ q)
  have he : fderiv ℂ (fun x => holderProduct (q := p) (σ x) (F x)) q-M.comp Q=
      (fderiv ℂ (fun x => holderProduct (q := p) (σ x) (F x)) q-M.comp (fderiv ℂ F q))+
        M.comp (fderiv ℂ F q-Q) := by
    apply ContinuousLinearMap.ext
    intro h
    change (fderiv ℂ (fun x => holderProduct (q := p) (σ x) (F x)) q) h-M (Q h)=
      ((fderiv ℂ (fun x => holderProduct (q := p) (σ x) (F x)) q) h-M (fderiv ℂ F q h))+
        M (fderiv ℂ F q h-Q h)
    rw [map_sub]
    abel
  rw [he]
  exact (isCompactOperator_fderiv_holderProduct_packet_sub hp σ F q hσ hF).add
    (hQ.clm_comp M)

end NLS.Coeff
