import NLS.SequenceSpaces.WeightedReciprocalDecay

/-! # Exact multipliers between arbitrary Sobolev sequence weights

A power bound on a symbol gives a bounded multiplication operator with
the corresponding real weight shift, for every Banach exponent including
infinity.
-/

noncomputable section
open Set Metric Complex MeasureTheory
open scoped ENNReal

namespace NLS.WeightedCoeff

/-- A power bound on a symbol gives the exact corresponding shift of Sobolev sequence weights. -/
theorem exists_sobolev_power_multiplier {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (r d : ℝ) (f : ℤ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ n : ℤ, (1+|(n:ℝ)|)^d*‖f n‖ ≤ K) :
    ∃ T : WeightedCoeff (Weight.sobolev r) p →L[ℂ] WeightedCoeff (Weight.sobolev (r+d)) p,
      (∀ a n, (T a).val n = f n*a.val n) ∧ ‖T‖ ≤ K := by
  have hw (n : ℤ) : Weight.sobolev (r+d) n*‖f n‖ ≤ K*Weight.sobolev r n := by
    simp only [Weight.sobolev_apply,Real.rpow_add (by positivity : 0 < 1+|(n:ℝ)|)]
    calc
      _ = (1+|(n:ℝ)|)^r*((1+|(n:ℝ)|)^d*‖f n‖) := by ring
      _ ≤ (1+|(n:ℝ)|)^r*K := mul_le_mul_of_nonneg_left (hf n) (Real.rpow_pos_of_pos (by positivity) r).le
      _ = _ := by ring
  let T := weightedMultiplierCLM (p := p) (Weight.sobolev r) (Weight.sobolev (r+d)) f K hK hw
  refine ⟨T,fun _ _ => rfl,T.opNorm_le_bound hK (fun a => ?_)⟩
  exact norm_weightedMultiplier_le _ _ f K hK hw a

end NLS.WeightedCoeff
