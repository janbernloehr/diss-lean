import NLS.SequenceSpaces.CompactHolderDerivative
import NLS.SequenceSpaces.CompactSobolevInclusion

/-! A finite-exponent analytic symbol makes BOTH derivative terms of
its product with a finite-exponent sequence compact. This holds in any
original weighted coefficient norm, in particular weighted ell1. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS
namespace Coeff
variable {p r : ℝ≥0∞} [Fact (1≤p)] [Fact (1≤r)]

theorem isCompactOperator_fderiv_finiteSymbol_packet
    (hp : p≠⊤) (hr : r≠⊤)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : E → Coeff r) (F : E → Coeff p) (a : E)
    (hσ : DifferentiableAt ℂ σ a) (hF : DifferentiableAt ℂ F a) :
    IsCompactOperator (fderiv ℂ
      (fun x => holderProduct (q := p) (exponentInclusion (show r≤⊤ from le_top) (σ x)) (F x)) a) := by
  let J := exponentInclusion (show r≤⊤ from le_top)
  have hJσ : DifferentiableAt ℂ (fun x => J (σ x)) a :=
    J.differentiableAt.comp a hσ
  rw [fderiv_holderProduct_packet (fun x => J (σ x)) F a hJσ hF]
  have hprincipal : IsCompactOperator (holderProduct (p := ⊤) (r := p) (q := p) (J (σ a))) := by
    have he : holderProduct (p := ⊤) (r := p) (q := p) (J (σ a))=multiplierCLM (p := p) (J (σ a)) := by
      ext v n
      rfl
    rw [he]
    exact isCompactOperator_multiplier_of_finite_symbol hr (σ a)
  exact (hprincipal.comp_clm (fderiv ℂ F a)).add
    ((isCompactOperator_holderProduct_fixed_right hp (F a)).comp_clm (fderiv ℂ (fun x => J (σ x)) a))

end Coeff
namespace WeightedCoeff
variable {p r : ℝ≥0∞} [Fact (1≤p)] [Fact (1≤r)]

theorem exists_analytic_finiteSymbol_packet_compact
    (w : Weight) (hp : p≠⊤) (hr : r≠⊤)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (σ : E → Coeff r) (F : E → WeightedCoeff w p)
    (hσ : AnalyticOnNhd ℂ σ U) (hF : AnalyticOnNhd ℂ F U) :
    ∃ G : E → WeightedCoeff w p, AnalyticOnNhd ℂ G U ∧
      (∀ a n, (G a).val n=σ a n*(F a).val n) ∧
      ∀ a∈U, IsCompactOperator (fderiv ℂ G a) := by
  let J := (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap
  let K := (weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let L := Coeff.exponentInclusion (show r≤⊤ from le_top)
  let H := fun a => Coeff.holderProduct (q := p) (L (σ a)) (J (F a))
  have hH : AnalyticOnNhd ℂ H U := by
    intro a ha
    exact ((Coeff.holderProduct (p := ⊤) (r := p) (q := p)).analyticAt_bilinear _).comp₂
      ((L.analyticAt _).comp (hσ a ha)) ((J.analyticAt _).comp (hF a ha))
  refine ⟨fun a => K (H a),analyticOnNhd_postcompose_clm K H U hH,?_,?_⟩
  · intro a n
    change ((σ a n)*((w n : ℂ)*(F a).val n))/(w n : ℂ)=_
    rw [mul_left_comm,mul_div_cancel_left₀ _ (w.complex_ne_zero n)]
  · intro a ha
    have hc : IsCompactOperator (fderiv ℂ H a) :=
      Coeff.isCompactOperator_fderiv_finiteSymbol_packet hp hr σ (fun a => J (F a)) a
        (hσ a ha).differentiableAt (((J.analyticAt _).comp (hF a ha)).differentiableAt)
    change IsCompactOperator (fderiv ℂ (K ∘ H) a)
    rw [(K.hasFDerivAt.comp a (hH a ha).differentiableAt.hasFDerivAt).fderiv]
    exact hc.clm_comp K

/-- A diagonal finite-symbol factorization plus an already compact
remainder proves compactness of the full corrected derivative. The
factorization is a separate hypothesis, not a spectral assertion. -/
theorem isCompactOperator_corrected_fderiv_of_finiteSymbol
    (w : Weight) (hp : p≠⊤) (hr : r≠⊤)
    (U : Set (WeightedCoeff w p)) (hU : IsOpen U) (c : ℂ)
    (F R : WeightedCoeff w p → WeightedCoeff w p) (σ : WeightedCoeff w p → Coeff r)
    (hF : AnalyticOnNhd ℂ F U) (hR : AnalyticOnNhd ℂ R U) (hσ : AnalyticOnNhd ℂ σ U)
    (hRc : ∀ a∈U, IsCompactOperator (fderiv ℂ R a))
    (he : ∀ a∈U, ∀ n : ℤ, (F a).val n+c*a.val n=(R a).val n+σ a n*a.val n)
    (a : WeightedCoeff w p) (ha : a∈U) :
    IsCompactOperator (fderiv ℂ F a+c • ContinuousLinearMap.id ℂ (WeightedCoeff w p)) := by
  obtain ⟨G,hG,hraw,hGc⟩ := exists_analytic_finiteSymbol_packet_compact w hp hr U σ
    (fun a : WeightedCoeff w p => a) hσ analyticOnNhd_id
  have heN : (fun b => F b+c • b)=ᶠ[𝓝 a] (fun b => R b+G b) := by
    filter_upwards [hU.mem_nhds ha] with b hb
    apply Subtype.ext
    funext n
    simpa only [add_val,smul_val,hraw] using he b hb n
  have hdF : HasFDerivAt (fun b => F b+c • b)
      (fderiv ℂ F a+c • ContinuousLinearMap.id ℂ (WeightedCoeff w p)) a :=
    (hF a ha).differentiableAt.hasFDerivAt.add ((hasFDerivAt_id a).const_smul c)
  have hdRG : HasFDerivAt (fun b => R b+G b) (fderiv ℂ R a+fderiv ℂ G a) a :=
    (hR a ha).differentiableAt.hasFDerivAt.add (hG a ha).differentiableAt.hasFDerivAt
  rw [←hdF.fderiv,heN.fderiv_eq,hdRG.fderiv]
  exact (hRc a ha).add (hGc a ha)

end WeightedCoeff
end NLS
