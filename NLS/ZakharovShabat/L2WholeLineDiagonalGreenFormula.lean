import NLS.ZakharovShabat.L2WholeLineScalarGreenFormula
import NLS.ZakharovShabat.L2WholeLineDiagonalInverse
import NLS.ZakharovShabat.L2WholeLineMatrixMultiplication

/-! # One-sided Green formulas for the existing diagonal L2 inverse -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Complex
namespace NLS.ZakharovShabat

/-- The diagonal inverse has exactly its two scalar inverses as physical pair coordinates. -/
theorem wholeLineDiagonalODEInverse_pair_ae (α β : ℂ) (hα : α.re ≠ 0) (hβ : β.re ≠ 0)
    (h : WholeLineL2) :
    wholeLineL2Pair (wholeLineDiagonalODEInverse α β hα hβ h) =ᵐ[volume]
      (fun t => (wholeLineScalarODEInverse α hα (wholeLineFirstCoordinate h) t,
        wholeLineScalarODEInverse β hβ (wholeLineSecondCoordinate h) t)) := by
  let f := wholeLineScalarODEInverse α hα (wholeLineFirstCoordinate h)
  let g := wholeLineScalarODEInverse β hβ (wholeLineSecondCoordinate h)
  change wholeLineL2Pair (wholeLineFirstEmbedding f+wholeLineSecondEmbedding g) =ᵐ[volume] _
  filter_upwards [wholeLineL2Pair_add_ae (wholeLineFirstEmbedding f) (wholeLineSecondEmbedding g),
    wholeLineFirstEmbedding_pair_ae f,wholeLineSecondEmbedding_pair_ae g] with t ht hf hg
  rw [ht,hf,hg]
  simp [f,g]

/-- The stable coordinate uses a forward integral and the unstable one a backward integral. -/
theorem wholeLineDiagonalODEInverse_ae_green_integrals (α β : ℂ)
    (hα : α.re < 0) (hβ : 0 < β.re) (h : WholeLineL2) (a b : ℝ)
    (hleft : ∀ᵐ t : ℝ, t ≤ a → wholeLineL2Pair h t = 0)
    (hright : ∀ᵐ t : ℝ, b ≤ t → wholeLineL2Pair h t = 0) :
    wholeLineL2Pair (wholeLineDiagonalODEInverse α β hα.ne hβ.ne' h) =ᵐ[volume]
      (fun t => (∫ s in a..t, Complex.exp (α*((t-s : ℝ) : ℂ))*
          wholeLineFirstCoordinate h s,
        -(∫ s in t..b, Complex.exp (β*((t-s : ℝ) : ℂ))*wholeLineSecondCoordinate h s))) := by
  have hl : ∀ᵐ t : ℝ, t ≤ a → wholeLineFirstCoordinate h t = 0 := by
    filter_upwards [wholeLineFirstCoordinate_ae h,hleft] with t ht hz
    intro hta
    rw [ht,hz hta]
    rfl
  have hr : ∀ᵐ t : ℝ, b ≤ t → wholeLineSecondCoordinate h t = 0 := by
    filter_upwards [wholeLineSecondCoordinate_ae h,hright] with t ht hz
    intro hbt
    rw [ht,hz hbt]
    rfl
  filter_upwards [wholeLineDiagonalODEInverse_pair_ae α β hα.ne hβ.ne' h,
    wholeLineScalarODEInverse_ae_forward_integral α hα (wholeLineFirstCoordinate h) a hl,
    wholeLineScalarODEInverse_ae_backward_integral β hβ (wholeLineSecondCoordinate h) b hr]
      with t ht hf hb
  rw [ht,hf,hb]

end NLS.ZakharovShabat
