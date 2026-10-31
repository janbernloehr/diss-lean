import NLS.SequenceSpaces.AppendixBSourceInequalities

/-! # The intermediate exponent and outer power in the proof of Lemma B.3 -/

noncomputable section
open scoped ENNReal
namespace NLS

/-- Under (B.2), the intermediate exponent is at least beta exactly when
the output exponent is at least the first input exponent. -/
theorem mixedYoung_intermediate_order_iff {β p q γ : ℝ}
    (hβ : 0 < β) (hp : 0 < p) (hq : 0 < q) (hγ : 0 < γ)
    (h : 1 / β + 1 / γ = 1 / p + 1 / q) : β ≤ q ↔ p ≤ γ := by
  rw [← one_div_le_one_div hq hβ, ← one_div_le_one_div hγ hp]
  constructor <;> intro hle <;> linarith

/-- The single finite positive exponent condition is equivalent to the two
successive powered Young conditions (B.2) and (B.3). -/
theorem mixedYoungRelation_iff_exists_intermediate {α β γ p₁ p₂ p₃ : ℝ} :
    MixedYoungRelation α β γ p₁ p₂ p₃ ↔
      ∃ q : ℝ, PowerYoungRelation p₂ p₃ q α ∧ PowerYoungRelation p₁ q γ β := by
  constructor
  · exact MixedYoungRelation.exists_intermediate
  · rintro ⟨q, hi, ho⟩
    refine ⟨hi.t_pos, ho.t_pos, ho.t_le_p, ?_, hi.t_le_p, hi.t_le_q, ?_⟩
    · exact (mixedYoung_intermediate_order_iff ho.t_pos ho.p_pos ho.q_pos ho.r_pos
        ho.relation).mp ho.t_le_q
    · linarith [hi.relation, ho.relation]

namespace Coeff

/-- The outer sum in the proof is bounded by the gamma-th power of the product
of input norms. Taking its positive gamma-th root gives Lemma B.3. -/
theorem mixedYoung_outer_sum_le {α β γ p₁ p₂ p₃ : ℝ}
    (h : MixedYoungRelation α β γ p₁ p₂ p₃)
    (a : Coeff (ENNReal.ofReal p₁)) (b : Coeff (ENNReal.ofReal p₂))
    (c : Coeff (ENNReal.ofReal p₃)) :
    Summable (fun k : ℤ => mixedYoungRow α β a b c k ^ (γ / β)) ∧
      (∑' k : ℤ, mixedYoungRow α β a b c k ^ (γ / β)) ≤
        ‖a‖ ^ γ * ‖b‖ ^ γ * ‖c‖ ^ γ := by
  have hb := (mixedYoung_summable_and_le h a b c).2.2
  refine ⟨hb.1, ?_⟩
  have hs : 0 ≤ ∑' k : ℤ, mixedYoungRow α β a b c k ^ (γ / β) :=
    tsum_nonneg (fun k => Real.rpow_nonneg (mixedYoungRow_nonneg _ _ _ _ _ k) _)
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hs _) hb.2 h.gamma_pos.le
  rw [one_div, Real.rpow_inv_rpow hs h.gamma_pos.ne'] at hp
  simpa only [Real.mul_rpow (mul_nonneg (lp.norm_nonneg' a) (lp.norm_nonneg' b))
    (lp.norm_nonneg' c), Real.mul_rpow (lp.norm_nonneg' a) (lp.norm_nonneg' b)] using hp

end Coeff
end NLS
