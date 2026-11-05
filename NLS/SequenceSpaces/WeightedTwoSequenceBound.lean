import NLS.SequenceSpaces.TwoSequenceBound
import NLS.SequenceSpaces.WeightedAnalyticRealization

/-! # Weighted realizations controlled by two actual coefficient sequences -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A bound by two actual coefficient sequences gives weighted membership,
exact raw coordinates, and a norm bound for the full realization. -/
theorem exists_of_two_sequence_bound (w : Weight) (f : ℤ → ℂ)
    (a b : Coeff p) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, ‖(w n : ℂ)*f n‖ ≤ C*(‖a n‖+‖b n‖)) :
    ∃ v : WeightedCoeff w p, (∀ n, v.val n = f n) ∧ ‖v‖ ≤ C*(‖a‖+‖b‖) := by
  obtain ⟨hm,hn⟩ := Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound
    (fun n => (w n : ℂ)*f n) a b C hC hf
  let v : WeightedCoeff w p := ⟨f,hm⟩
  have he : Coeff.ofFunctionOrZero p (fun n => (w n : ℂ)*f n) = weightEquiv w p v :=
    Coeff.ofFunctionOrZero_eq_of_coordinates _ _ (fun _ => rfl)
  rw [he] at hn
  exact ⟨v,fun _ => rfl,hn⟩

end NLS.WeightedCoeff
