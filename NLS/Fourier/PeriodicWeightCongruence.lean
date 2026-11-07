import NLS.Fourier.PeriodicFourierLebesgueSpace

/-! Equality of weights preserves the entire original distribution and its exact norm. -/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
variable {L : ℝ} [Fact (0 < L)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Pointwise equal weights give an isometric identification with no change
of any original smooth-test action. -/
def weightCongr (w v : Weight) (h : ∀ k, w k = v k) :
    PeriodicFourierLebesgue L w p ≃ₗᵢ[ℂ] PeriodicFourierLebesgue L v p := by
  have he : w = v := by
    cases w with | mk f hf =>
      cases v with | mk g hg =>
        have hh : f = g := funext h
        cases hh
        rfl
  subst v
  exact LinearIsometryEquiv.refl ℂ _

/-- The isometric identification retains the ENTIRE original distribution. -/
theorem weightCongr_val (w v : Weight) (h : ∀ k, w k = v k)
    (q : PeriodicFourierLebesgue L w p) : (weightCongr w v h q).val = q.val := by
  have he : w = v := by
    cases w with | mk f hf =>
      cases v with | mk g hg =>
        have hh : f = g := funext h
        cases hh
        rfl
  subst v
  rfl

end NLS.Fourier.PeriodicFourierLebesgue
