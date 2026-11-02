import NLS.SequenceSpaces.Insertion
import NLS.SequenceSpaces.Weighted

/-! # Isometric zero insertion in weighted coefficient spaces

Pulling the target weight back along an index embedding makes zero
insertion an exact isometry, with the original raw coefficients retained.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- Pull a positive Fourier weight back along any integer index map. -/
def Weight.pullback (w : Weight) (f : ℤ → ℤ) : Weight :=
  ⟨fun n => w (f n), fun n => w.positive (f n)⟩

@[simp] theorem Weight.pullback_apply (w : Weight) (f : ℤ → ℤ) (n : ℤ) :
    w.pullback f n = w (f n) := rfl

namespace WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Insert raw coefficients along an embedding, using the exact pulled-back weight. -/
def insertIsometry (w : Weight) (e : ℤ ↪ ℤ) :
    WeightedCoeff (w.pullback e) p →ₗᵢ[ℂ] WeightedCoeff w p :=
  (weightIsometry w p).symm.toLinearIsometry.comp
    ((Coeff.insertIsometry e).comp (weightIsometry (w.pullback e) p).toLinearIsometry)

@[simp] theorem insertIsometry_image (w : Weight) (e : ℤ ↪ ℤ)
    (a : WeightedCoeff (w.pullback e) p) (n : ℤ) :
    (insertIsometry w e a).val (e n) = a.val n := by
  change Coeff.insert e (weightEquiv (w.pullback e) p a) (e n)/(w (e n) : ℂ) = _
  rw [Coeff.insert_apply_image, weightEquiv_apply, Weight.pullback_apply]
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero (e n))

theorem insertIsometry_outside (w : Weight) (e : ℤ ↪ ℤ)
    (a : WeightedCoeff (w.pullback e) p) (k : ℤ) (hk : k ∉ Set.range e) :
    (insertIsometry w e a).val k = 0 := by
  change Coeff.insert e (weightEquiv (w.pullback e) p a) k/(w k : ℂ) = _
  rw [Coeff.insert_apply_outside e _ k hk, zero_div]

@[simp] theorem norm_insertIsometry (w : Weight) (e : ℤ ↪ ℤ)
    (a : WeightedCoeff (w.pullback e) p) : ‖insertIsometry w e a‖ = ‖a‖ :=
  (insertIsometry w e).norm_map a

end WeightedCoeff
end NLS
