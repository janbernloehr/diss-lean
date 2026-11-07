import NLS.Articles.KdVPseudomeasures.SourceLemma210Source
import NLS.KdV.PseudomeasureWideWeightedErrors

/-! The sharp epsilon estimate applies to the same actual solved physical
couplings, with no change of determinant, weight or test exponent. -/
noncomputable section
open NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem source_wideCorrectedMode_error_identity (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖≤1/2) (j k : ℤ) :
    (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs j).val k-q.val (k-j)=
      (wideEndpointHillPerturbation w r hr hr1 n hn z hz q
        (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs j)).val k := by
  have he := congrArg (fun a : WeightedCoeff (w.negativeSobolev r) ⊤ => a.val k)
    (wideEndpointHillTailInverse_right w r hr hr1 n hn z hz q hs (w.negativeModulation r hr j q))
  change (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs j).val k-
    (wideEndpointHillPerturbation w r hr hr1 n hn z hz q
      (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs j)).val k=
        (w.negativeModulation r hr j q).val k at he
  rw [SpectralWeight.negativeModulation_apply] at he
  linear_combination he

theorem source_wideCoupling_errors_sharp (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) :
    ∃ C : ℝ, 1≤C ∧ 13*endpointHillConstant r≤C ∧
      ∀ (w : SpectralWeight) (q : WeightedCoeff (w.negativeSobolev r) ⊤)
      (n : ℕ) (_hn : 2≤n) (z : ℂ) (_hz : z ∈ wideHillStrip n)
      (_hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖≤1/2),
        (w.negativeSobolev r (2*(n:ℤ))*
          ‖endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z)-q.val (2*(n:ℤ))‖≤
            2*C*sourcePredualEpsilon r n*‖q‖^2) ∧
        (w.negativeSobolev r (2*(n:ℤ))*
          ‖endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z)-q.val (-(2*(n:ℤ)))‖≤
            2*C*sourcePredualEpsilon r n*‖q‖^2) := by
  obtain ⟨C,hC,hCwide,h⟩ := sourceLemma2_10 r hr hr1
  refine ⟨C,hC,hCwide,?_⟩
  intro w q n hn z hz hs
  have hE := wideEndpointCoefficients_eq_weightedCorrectedModes w r hr hr1 n hn z hz q hs
  rw [hE.2.1,hE.2.2]
  have hnonneg : 0≤C*sourcePredualEpsilon r n*‖q‖ := by
    exact mul_nonneg (mul_nonneg (by linarith) (sourcePredualEpsilon_nonneg r n (by omega))) (norm_nonneg q)
  constructor
  · have he := source_wideCorrectedMode_error_identity w r hr hr1 n hn z hz q hs (-(n:ℤ)) (n:ℤ)
    rw [show (n:ℤ)- -(n:ℤ)=2*(n:ℤ) by ring] at he
    rw [he]
    have ht := (h w q (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs (-(n:ℤ))) n hn z hz).1
    have hk := negativeShiftedNorm_wideEndpointHillCorrectedMode_le w r hr hr1 n hn z hz q hs
      (-(n:ℤ)) (Or.inr rfl)
    simp only [neg_neg] at hk
    calc
      _ ≤ (C*sourcePredualEpsilon r n*‖q‖)*
          w.negativeShiftedNorm r hr (n:ℤ) ⊤ (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs (-(n:ℤ))) := ht
      _ ≤ (C*sourcePredualEpsilon r n*‖q‖)*(2*‖q‖) := mul_le_mul_of_nonneg_left hk hnonneg
      _ = _ := by ring
  · have he := source_wideCorrectedMode_error_identity w r hr hr1 n hn z hz q hs (n:ℤ) (-(n:ℤ))
    rw [show -(n:ℤ)-(n:ℤ)=-(2*(n:ℤ)) by ring] at he
    rw [he]
    have ht := (h w q (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs (n:ℤ)) n hn z hz).2
    have hk := negativeShiftedNorm_wideEndpointHillCorrectedMode_le w r hr hr1 n hn z hz q hs
      (n:ℤ) (Or.inl rfl)
    calc
      _ ≤ (C*sourcePredualEpsilon r n*‖q‖)*
          w.negativeShiftedNorm r hr (-(n:ℤ)) ⊤ (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs (n:ℤ)) := ht
      _ ≤ (C*sourcePredualEpsilon r n*‖q‖)*(2*‖q‖) := mul_le_mul_of_nonneg_left hk hnonneg
      _ = _ := by ring

end NLS.Articles.KdVPseudomeasures
