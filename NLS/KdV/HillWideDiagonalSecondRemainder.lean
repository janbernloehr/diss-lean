import NLS.KdV.PseudomeasureWideOperatorErrors
import NLS.SequenceSpaces.UnitWeightedInfinityNorm
import NLS.FunctionalAnalysis.NeumannSecondRemainder
import NLS.FunctionalAnalysis.NeumannVectorSeries

/-! A second Born expansion of the actual wide-strip diagonal under a
unit-valued total weight. The remainder uses the literal shifted operator norm. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.FunctionalAnalysis NLS.WeightedCoeff

theorem wideEndpointDiagonal_second_remainder (w : SpectralWeight)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (hv : ∀ k, w.negativeSobolev r k=1)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1/2)
    (hT : wideEndpointShiftedOperatorNorm w r hr hr1 n hn z hz q (-(n:ℤ)) ≤ t) :
    ‖endpointDiagonal r hr hr1 n (endpointForgetWeight w r q,z)-q.val 0-
      (wideEndpointHillPerturbation w r hr hr1 n hn z hz q
        (w.negativeModulation r hr (n:ℤ) q)).val n‖ ≤ 2*t^2*‖q‖ := by
  let e := w.negativeShiftEquiv r hr (-(n:ℤ)) ⊤
  let T := wideEndpointHillPerturbation w r hr hr1 n hn z hz q
  let b := w.negativeModulation r hr (n:ℤ) q
  let g := wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs n
  have hg : g-T g=b := wideEndpointHillTailInverse_right w r hr hr1 n hn z hz q hs b
  have hnorm : ‖e.conjContinuousAlgEquiv T‖ ≤ t := hT
  have he := conjugate_vector_sub_equation e T g b hg
  have hrem := norm_neumann_second_remainder_le (e.conjContinuousAlgEquiv T)
    t ht ht1 hnorm (e b) (e g) he
  have hb : ‖e b‖=‖q‖ := w.negativeShiftedNorm_negativeModulation r hr (n:ℤ) q
  rw [hb] at hrem
  have hshift (k : ℤ) : (w.negativeSobolev r).shift (-(n:ℤ)) k=1 := by
    rw [Weight.shift_apply,hv]
  have hev := (norm_apply_le_of_unit_values _ hshift
    (e g-(e b+e.conjContinuousAlgEquiv T (e b))) n).trans hrem
  have hraw := (wideEndpointCoefficients_eq_weightedCorrectedModes w r hr hr1 n hn z hz q hs).1
  have hex :
      (e g-(e b+e.conjContinuousAlgEquiv T (e b))).val n =
        endpointDiagonal r hr hr1 n (endpointForgetWeight w r q,z)-q.val 0-(T b).val n := by
    simp only [WeightedCoeff.sub_val,WeightedCoeff.add_val,
      ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
      ContinuousLinearEquiv.symm_apply_apply,SpectralWeight.negativeShiftEquiv_apply,
      SpectralWeight.negativeModulation_apply,sub_self,e,b]
    rw [hraw]
    change g.val n-(q.val 0+(T b).val n)=g.val n-q.val 0-(T b).val n
    ring
  rw [hex] at hev
  exact hev

end NLS.KdV
