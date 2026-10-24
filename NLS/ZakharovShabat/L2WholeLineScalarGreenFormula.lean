import NLS.FunctionalAnalysis.ScalarL2OneSidedFormula
import NLS.ZakharovShabat.L2WholeLineScalarODEInverse

/-! # The original bounded scalar inverse equals its one-sided Green integral -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Complex NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The original scalar L2 forcing is integrable on every compact interval. -/
theorem wholeLineScalarL2_intervalIntegrable (h : WholeLineScalarL2) (a b : ℝ) :
    IntervalIntegrable h volume a b :=
  (intervalIntegrable_iff').mpr
    (((Lp.memLp h).locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_uIcc)

/-- For a positive real exponent, the already constructed scalar inverse
is the backward Green integral when the forcing vanishes on a right half-line. -/
theorem wholeLineScalarODEInverse_ae_backward_integral
    (α : ℂ) (hα : 0 < α.re) (h : WholeLineScalarL2) (R : ℝ)
    (hzero : ∀ᵐ t : ℝ, R ≤ t → h t = 0) :
    wholeLineScalarODEInverse α hα.ne' h =ᵐ[volume]
      (fun t => -(∫ s in t..R, Complex.exp (α*((t-s : ℝ) : ℂ))*h s)) := by
  obtain ⟨y,he,hy,hac,hd⟩ := wholeLineScalarODEInverse_exists_AC_solution α hα.ne' h
  filter_upwards [he] with t ht
  exact ht.trans (scalarL2_backward_integral α hα.le y h hy hac
    (wholeLineScalarL2_intervalIntegrable h) hd R hzero t)

/-- For a negative real exponent, the already constructed scalar inverse
is the forward Green integral when the forcing vanishes on a left half-line. -/
theorem wholeLineScalarODEInverse_ae_forward_integral
    (α : ℂ) (hα : α.re < 0) (h : WholeLineScalarL2) (R : ℝ)
    (hzero : ∀ᵐ t : ℝ, t ≤ R → h t = 0) :
    wholeLineScalarODEInverse α hα.ne h =ᵐ[volume]
      (fun t => ∫ s in R..t, Complex.exp (α*((t-s : ℝ) : ℂ))*h s) := by
  obtain ⟨y,he,hy,hac,hd⟩ := wholeLineScalarODEInverse_exists_AC_solution α hα.ne h
  filter_upwards [he] with t ht
  exact ht.trans (scalarL2_forward_integral α hα.le y h hy hac
    (wholeLineScalarL2_intervalIntegrable h) hd R hzero t)

end NLS.ZakharovShabat
