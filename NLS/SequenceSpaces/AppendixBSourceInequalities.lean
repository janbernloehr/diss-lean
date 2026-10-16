import NLS.SequenceSpaces.ReciprocalSeries
import NLS.SequenceSpaces.MixedYoung

/-!
# Appendix B: source statements with convergence

B.1 retains both printed reciprocal-series bounds. B.2 allows all Banach
exponents, including infinity. B.3 uses finite positive auxiliary exponents,
as required by its displayed divisions, and includes input exponents below one.
Its unit constant is optimal for every admissible tuple.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- Lemma B.1: convergence and both printed bounds, with `q` conjugate to `p`. -/
theorem sourceLemmaB1 {α p q : ℝ} (hα : 0 ≤ α) (hpq : p.HolderConjugate q) :
    Summable (fun n : ℕ => 1 / (α + (n + 1 : ℝ)) ^ q) ∧
    (∑' n : ℕ, 1 / (α + (n + 1 : ℝ)) ^ q) ≤ (q + α) / (q - 1) / (1 + α) ^ q ∧
    (q + α) / (q - 1) / (1 + α) ^ q ≤ p / (1 + α) ^ (q - 1) := by
  refine ⟨?_, ReciprocalSeries.shifted_reciprocal_series_bounds hα hpq⟩
  have h := ReciprocalSeries.summable_nat_shifted_rpow (by linarith : 0 < 1 + α) hpq.symm.lt
  convert h using 1
  funext n
  rw [Real.rpow_neg (by positivity), one_div]
  congr 2
  ring

namespace Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- Lemma B.2: the unique convolution in the target space, with its sharp unit bound.
Every Banach Young triple is allowed, including infinity endpoints. -/
theorem sourceLemmaB2 (h : YoungRelation p q r) (a : Coeff p) (b : Coeff q) :
    ∃! c : Coeff r, (∀ n : ℤ, HasSum (fun k : ℤ => a (n - k) * b k) (c n)) ∧ ‖c‖ ≤ ‖a‖ * ‖b‖ := by
  refine ⟨youngConvolution h a b, ⟨?_, norm_youngConvolution_le h a b⟩, ?_⟩
  · intro n
    rw [youngConvolution_apply]
    exact (summable_norm_youngConvolution_terms h a b n).of_norm.hasSum
  · intro c hc
    ext n
    rw [youngConvolution_apply]
    exact (hc.1 n).tsum_eq.symm

/-- Lemma B.3 for finite positive auxiliary exponents: every nested sum converges
and the displayed estimate has constant one. Positive input exponents below one are allowed.
The printed zero auxiliary endpoints are undefined; see `MixedYoungZeroExponent`. -/
theorem sourceLemmaB3_positive {α β γ p₁ p₂ p₃ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβp : β ≤ p₁) (hpγ : p₁ ≤ γ)
    (hαp₂ : α ≤ p₂) (hαp₃ : α ≤ p₃)
    (h : 1 / α + 1 / β + 1 / γ = 1 / p₁ + 1 / p₂ + 1 / p₃)
    (a : Coeff (ENNReal.ofReal p₁)) (b : Coeff (ENNReal.ofReal p₂))
    (c : Coeff (ENNReal.ofReal p₃)) :
    (∀ k l : ℤ, Summable (fun m : ℤ => ‖a (k - l) * b (l - m) * c m‖ ^ α)) ∧
    (∀ k : ℤ, Summable (fun l : ℤ => (∑' m : ℤ, ‖a (k - l) * b (l - m) * c m‖ ^ α) ^ (β / α))) ∧
    Summable (fun k : ℤ => (∑' l : ℤ, (∑' m : ℤ, ‖a (k - l) * b (l - m) * c m‖ ^ α) ^ (β / α)) ^ (γ / β)) ∧
    (∑' k : ℤ, (∑' l : ℤ, (∑' m : ℤ, ‖a (k - l) * b (l - m) * c m‖ ^ α) ^ (β / α)) ^ (γ / β)) ^ (1 / γ) ≤
      ‖a‖ * ‖b‖ * ‖c‖ :=
  mixedYoung_summable_and_le ⟨hα, hβ, hβp, hpγ, hαp₂, hαp₃, h⟩ a b c

/-- No smaller constant works in B.3 for any admissible finite positive exponent tuple. -/
theorem sourceLemmaB3_constant_sharp {α β γ p₁ p₂ p₃ K : ℝ}
    (h : MixedYoungRelation α β γ p₁ p₂ p₃)
    (hK : ∀ (a : Coeff (ENNReal.ofReal p₁)) (b : Coeff (ENNReal.ofReal p₂))
      (c : Coeff (ENNReal.ofReal p₃)),
      (∑' k : ℤ, mixedYoungRow α β a b c k ^ (γ / β)) ^ (1 / γ) ≤ K * ‖a‖ * ‖b‖ * ‖c‖) : 1 ≤ K := by
  have hh := hK (lp.single _ 0 1) (lp.single _ 0 1) (lp.single _ 0 1)
  rw [lp.coeFn_single, lp.coeFn_single, lp.coeFn_single, mixedYoung_unit_modes h.alpha_pos h.beta_pos h.gamma_pos,
    lp.norm_single (ENNReal.ofReal_pos.mpr (h.beta_pos.trans_le h.beta_le_p₁)),
    lp.norm_single (ENNReal.ofReal_pos.mpr (h.alpha_pos.trans_le h.alpha_le_p₂)),
    lp.norm_single (ENNReal.ofReal_pos.mpr (h.alpha_pos.trans_le h.alpha_le_p₃))] at hh
  simpa using hh

end Coeff
end NLS
