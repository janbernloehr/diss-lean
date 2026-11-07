import NLS.Fourier.PeriodicWeightedExponentInclusion

/-! Equal weights give literal isometric identities of the original
distribution spaces and weighted coefficient spaces. -/
noncomputable section
open scoped ENNReal
namespace NLS.Weight

theorem eq_of_values (w v : Weight) (h : ∀ k, w k=v k) : w=v := by
  cases w with
  | mk f hf =>
    cases v with
    | mk g hg =>
      have he : f=g := funext h
      cases he
      rfl

end NLS.Weight
namespace NLS.Fourier.PeriodicFourierLebesgue
variable {L : ℝ} [Fact (0 < L)] (p : ℝ≥0∞) [Fact (1 ≤ p)]

def equalWeightIsometry (w v : Weight) (hwv : w=v) :
    PeriodicFourierLebesgue L w p ≃ₗᵢ[ℂ] PeriodicFourierLebesgue L v p := by
  subst v
  exact LinearIsometryEquiv.refl ℂ _

theorem equalWeightIsometry_val (w v : Weight) (hwv : w=v) (q : PeriodicFourierLebesgue L w p) :
    (equalWeightIsometry p w v hwv q).val = q.val := by
  subst v
  rfl

end NLS.Fourier.PeriodicFourierLebesgue
namespace NLS.WeightedCoeff
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

def equalWeightIsometry (w v : Weight) (hwv : w=v) : WeightedCoeff w p ≃ₗᵢ[ℂ] WeightedCoeff v p := by
  subst v
  exact LinearIsometryEquiv.refl ℂ _

theorem equalWeightIsometry_apply (w v : Weight) (hwv : w=v) (q : WeightedCoeff w p) (k : ℤ) :
    (equalWeightIsometry p w v hwv q).val k = q.val k := by
  subst v
  rfl

end NLS.WeightedCoeff
