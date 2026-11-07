import NLS.Articles.KdVPseudomeasures.SourceSharpResonantEpsilon
import NLS.Articles.KdVPseudomeasures.SourceWeightedSpectral

/-! Both signs in the sharp resonant estimate. The arbitrary spectral
weight and the original endpoint infinity exponent are retained. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem source_negativeShiftedNorm_reflection (w : SpectralWeight) (r : ℝ) (hr : 0≤r)
    (l : ℤ) (f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    w.negativeShiftedNorm r hr l ⊤ (weightReflection _ (w.negativeSobolev_neg r) f)=
      w.negativeShiftedNorm r hr (-l) ⊤ f := by
  have he : w.negativeShiftEquiv r hr l ⊤ (weightReflection _ (w.negativeSobolev_neg r) f)=
      (shiftReflection _ (w.negativeSobolev_neg r) l).symm (w.negativeShiftEquiv r hr (-l) ⊤ f) := by
    apply Subtype.ext
    funext k
    simp only [SpectralWeight.negativeShiftEquiv_apply,weightReflection_apply,shiftReflection_symm_apply]
  unfold SpectralWeight.negativeShiftedNorm
  rw [he,LinearIsometryEquiv.norm_map]

theorem source_widePerturbation_reflection (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    (wideEndpointHillPerturbation w r hr hr1 n hn z hz
      (weightReflection _ (w.negativeSobolev_neg r) q)
      (weightReflection _ (w.negativeSobolev_neg r) f)).val (n:ℤ)=
        (wideEndpointHillPerturbation w r hr hr1 n hn z hz q f).val (-(n:ℤ)) := by
  rw [wideEndpointHillPerturbation_apply,wideEndpointHillPerturbation_apply]
  have he := (Equiv.neg ℤ).tsum_eq (fun k : ℤ =>
    (weightReflection _ (w.negativeSobolev_neg r) q).val ((n:ℤ)-k)*wideHillSymbol n z k*
      (weightReflection _ (w.negativeSobolev_neg r) f).val k)
  rw [← he]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply,weightReflection_apply,neg_neg,wideHillSymbol,Int.natAbs_neg,freeHillValue_neg,
    show -((n:ℤ)- -k)=-(n:ℤ)-k by omega]

theorem sourceLemma2_10 (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) :
    ∃ C : ℝ, 1≤C ∧ 13*endpointHillConstant r≤C ∧
      ∀ (w : SpectralWeight) (q f : WeightedCoeff (w.negativeSobolev r) ⊤),
      ∀ (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ wideHillStrip n),
        (w.negativeSobolev r (2*(n:ℤ))*
          ‖(wideEndpointHillPerturbation w r hr hr1 n hn z hz q f).val (n:ℤ)‖ ≤
            C*sourcePredualEpsilon r n*‖q‖*w.negativeShiftedNorm r hr (n:ℤ) ⊤ f) ∧
        (w.negativeSobolev r (2*(n:ℤ))*
          ‖(wideEndpointHillPerturbation w r hr hr1 n hn z hz q f).val (-(n:ℤ))‖ ≤
            C*sourcePredualEpsilon r n*‖q‖*w.negativeShiftedNorm r hr (-(n:ℤ)) ⊤ f) := by
  obtain ⟨C,hC,hCwide,h⟩ := sourceLemma2_10_plus r hr hr1
  refine ⟨C,hC,hCwide,?_⟩
  intro w q f n hn z hz
  have hminus := h w (weightReflection _ (w.negativeSobolev_neg r) q)
    (weightReflection _ (w.negativeSobolev_neg r) f) n hn z hz
  rw [source_widePerturbation_reflection,LinearIsometryEquiv.norm_map,source_negativeShiftedNorm_reflection] at hminus
  exact ⟨h w q f n hn z hz,hminus⟩

end NLS.Articles.KdVPseudomeasures
