import NLS.SequenceSpaces.WeightedSymbolGauge
import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.SequenceSpaces.CompactOperatorTail

/-! An analytic bounded symbol tending to one contributes only a
compact derivative correction when multiplying an analytic weighted
sequence map. Both the diagonal symbol correction and the differentiated
symbol term are actual compact operators. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem isCompactOperator_boundedSymbol_sub_id (w : Weight) (s : Coeff ⊤)
    (ht : ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ k : ℤ, K ≤ k.natAbs → ‖s k-1‖ ≤ ε) :
    IsCompactOperator (boundedSymbolBilinear (p := p) w s -
      ContinuousLinearMap.id ℂ (WeightedCoeff w p)) := by
  let W := (weightIsometry w p).toContinuousLinearEquiv
  have hc := Coeff.isCompactOperator_multiplier_sub_smul_id_of_constantTail (p := p) s 1 ht
  rw [one_smul] at hc
  have he : boundedSymbolBilinear (p := p) w s - ContinuousLinearMap.id ℂ (WeightedCoeff w p) =
      W.symm.toContinuousLinearMap.comp
        ((Coeff.multiplierCLM s-ContinuousLinearMap.id ℂ (Coeff p)).comp W.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro a
    apply W.injective
    change W (boundedSymbolBilinear w s a-a) =
      W (W.symm (Coeff.multiplier s (W a)-W a))
    rw [W.apply_symm_apply]
    ext k
    change (w k:ℂ)*(s k*a.val k-a.val k) = s k*((w k:ℂ)*a.val k)-(w k:ℂ)*a.val k
    ring
  rw [he]
  exact (hc.comp_clm W.toContinuousLinearMap).clm_comp W.symm.toContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fderiv_boundedSymbol_sub (w : Weight) (s : E → Coeff ⊤)
    (g : E → WeightedCoeff w p) (q : E) (hs : AnalyticAt ℂ s q) (hg : AnalyticAt ℂ g q) :
    fderiv ℂ (fun x => boundedSymbolBilinear w (s x) (g x)) q - fderiv ℂ g q =
      (boundedSymbolBilinear w (s q)-ContinuousLinearMap.id ℂ (WeightedCoeff w p)).comp
        (fderiv ℂ g q) + ((boundedSymbolBilinear w).flip (g q)).comp (fderiv ℂ s q) := by
  let f := fun x => boundedSymbolBilinear w (s x) (g x)
  have hf : AnalyticAt ℂ f q := ((boundedSymbolBilinear w).analyticAt_bilinear _).comp (hs.prod hg)
  apply ContinuousLinearMap.ext
  intro h
  apply Subtype.ext
  funext k
  let ev := evalCLM w p k
  let es := lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ k
  have hd := (es.hasFDerivAt.comp q hs.differentiableAt.hasFDerivAt).fun_mul
    (ev.hasFDerivAt.comp q hg.differentiableAt.hasFDerivAt)
  change HasFDerivAt (fun x => (f x).val k) _ q at hd
  have hfd := ev.hasFDerivAt.comp q hf.differentiableAt.hasFDerivAt
  have hh := congrArg (fun L : E →L[ℂ] ℂ => L h) (hd.unique hfd)
  change s q k*((fderiv ℂ g q) h).val k+(g q).val k*((fderiv ℂ s q) h k) =
    ((fderiv ℂ f q) h).val k at hh
  change ((fderiv ℂ f q) h).val k-((fderiv ℂ g q) h).val k =
    (s q k*((fderiv ℂ g q) h).val k-((fderiv ℂ g q) h).val k)+
      ((fderiv ℂ s q) h k)*(g q).val k
  linear_combination -hh

theorem isCompactOperator_fderiv_boundedSymbol_sub (w : Weight) (hp : p ≠ ⊤)
    (s : E → Coeff ⊤) (g : E → WeightedCoeff w p) (q : E)
    (hs : AnalyticAt ℂ s q) (hg : AnalyticAt ℂ g q)
    (ht : ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ k : ℤ, K ≤ k.natAbs → ‖s q k-1‖ ≤ ε) :
    IsCompactOperator (fderiv ℂ (fun x => boundedSymbolBilinear w (s x) (g x)) q - fderiv ℂ g q) := by
  rw [fderiv_boundedSymbol_sub w s g q hs hg]
  exact ((isCompactOperator_boundedSymbol_sub_id w (s q) ht).comp_clm (fderiv ℂ g q)).add
    ((isCompactOperator_boundedSymbol_fixed w hp (g q)).comp_clm (fderiv ℂ s q))

end NLS.WeightedCoeff
