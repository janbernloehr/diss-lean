import NLS.SequenceSpaces.ShiftedWeight
import NLS.SequenceSpaces.Reflection

/-! # Isometric reflection between opposite shifted symmetric weights -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1≤p)]

/-- Raw reflection for every symmetric positive weight, including product weights. -/
def weightReflection (w : Weight) (_hw : ∀ k,w (-k)=w k) :
    WeightedCoeff w p ≃ₗᵢ[ℂ] WeightedCoeff w p :=
  ((weightIsometry w p).trans Coeff.reflection).trans (weightIsometry w p).symm

@[simp] theorem weightReflection_apply (w : Weight) (hw : ∀ k,w (-k)=w k)
    (a : WeightedCoeff w p) (k : ℤ) : (weightReflection w hw a).val k = a.val (-k) := by
  change ((w (-k):ℂ)*a.val (-k))/(w k:ℂ)=_
  rw [hw]
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero k)

/-- Reflection exchanges the source's +l and -l shifted norms exactly. -/
def shiftReflection (w : Weight) (_hw : ∀ k,w (-k)=w k) (l : ℤ) :
    WeightedCoeff (w.shift l) p ≃ₗᵢ[ℂ] WeightedCoeff (w.shift (-l)) p :=
  ((weightIsometry (w.shift l) p).trans Coeff.reflection).trans
    (weightIsometry (w.shift (-l)) p).symm

@[simp] theorem shiftReflection_apply (w : Weight) (hw : ∀ k,w (-k)=w k) (l : ℤ)
    (a : WeightedCoeff (w.shift l) p) (k : ℤ) :
    (shiftReflection w hw l a).val k = a.val (-k) := by
  change ((w (-k+l):ℂ)*a.val (-k))/(w (k+-l):ℂ)=_
  rw [show -k+l=-(k+-l) by omega,hw]
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero _)

@[simp] theorem shiftReflection_symm_apply (w : Weight) (hw : ∀ k,w (-k)=w k) (l : ℤ)
    (a : WeightedCoeff (w.shift (-l)) p) (k : ℤ) :
    ((shiftReflection w hw l).symm a).val k = a.val (-k) := by
  have h := congrArg (fun b : WeightedCoeff (w.shift (-l)) p => b.val (-k))
    ((shiftReflection w hw l).apply_symm_apply a)
  simpa only [shiftReflection_apply,neg_neg] using h

end NLS.WeightedCoeff
