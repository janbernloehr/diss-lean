import NLS.ZakharovShabat.L2WholeLineSelfAdjoint

/-! # Absolute-continuity representatives for the actual whole-line closure -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace NLS.ZakharovShabat

/-- The actual closure satisfies the original weak differential equation
with its own operator image. -/
theorem wholeLineMinimalOperator_closure_weakEquation (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u))
    (f : (wholeLineMinimalOperator u).closure.domain) :
    WholeLineWeakEquation u f ((wholeLineMinimalOperator u).closure f) := by
  have he := wholeLineMinimalOperator_closure_eq_adjoint u hu
  have hf := (le_of_eq he).1 f.property
  have ha : (wholeLineMinimalOperator u).closure f =
      (wholeLineMinimalOperator u).adjoint ⟨(f : WholeLineL2),hf⟩ := (le_of_eq he).2 rfl
  rw [ha]
  exact wholeLineMinimalOperator_adjoint_weakEquation u ⟨(f : WholeLineL2),hf⟩

/-- A closure-domain vector has a locally AC representative with the
exact original weak derivative determined by its actual closure image. -/
theorem wholeLineMinimalOperator_closure_exists_AC_representative (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u))
    (f : (wholeLineMinimalOperator u).closure.domain) :
    ∃ F : ℝ → ℂ × ℂ, wholeLineL2Pair f =ᵐ[volume] F ∧
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) ∧
      ∀ᵐ t : ℝ, HasDerivAt F
        (wholeLineWeakDerivative u f ((wholeLineMinimalOperator u).closure f) t) t :=
  (wholeLineMinimalOperator_closure_weakEquation u hu f).exists_AC_representative hu

end NLS.ZakharovShabat
