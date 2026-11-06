import NLS.KdV.HillL2AllGapSquares
import NLS.ComplexAnalysis.CoshSquareCoordinateDerivative

/-! # Filling the physical shifted primitive/root quotient

The quotient is expressed using the derivative of the entire squared
cosh coordinate. Its denominator stays nonzero on the complete intrinsic
gap disc, including both endpoints and a collapsed gap. The original
canonical sign is retained on the cut complement.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

def hillFilledPrimitiveRootQuotient (p : Coeff 2) (k : ℕ) (E : ℂ) : ℂ :=
  (-1:ℂ)^k * (4*deriv coshSquareCoordinate (hillL2RealGapPrimitiveSquare p k E))⁻¹

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillShiftedPrimitive_coshSquare_derivative_identity (k : ℕ) (E : ℂ) :
    4*deriv coshSquareCoordinate (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) k E)*
        (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E+I*(k:ℂ)*Real.pi) =
      (-1:ℂ)^k*hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E := by
  have hh := deriv_coshSquareCoordinate_sq_mul
    (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E+I*(k:ℂ)*Real.pi)
  rw [sinh_add_I_nat_pi] at hh
  dsimp only [hillL2RealGapPrimitiveSquare,hillL2RealCutRoot]
  linear_combination 2*hh

theorem hillShiftedPrimitive_coshSquare_derivative_ne_zero_of_cut
    (k : ℕ) (E : ℂ) (hE : E∈hillL2RealCutDomain q hq hr) :
    deriv coshSquareCoordinate (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) k E)≠0 := by
  intro he
  have hh := hillShiftedPrimitive_coshSquare_derivative_identity q k E
  rw [he,mul_zero,zero_mul] at hh
  exact mul_ne_zero (pow_ne_zero k (by norm_num))
    (hillL2RealCutRoot_ne_zero q hq hr E hE) hh.symm

/-- There is no loss of the endpoint or the closed-gap diagonal in the
analytic denominator. On the gap its argument is the nonnegative square
of the original physical gap profile. -/
theorem hillShiftedPrimitive_coshSquare_derivative_ne_zero
    (k : ℕ) (hk : 1≤k) (E : ℂ)
    (hE : E∈ball (hillRealGapCenter q hq hr k:ℂ)
      (hillRealGapHalfLength q hq hr k+2*hillRealGapCollar q hq hr k)) :
    deriv coshSquareCoordinate (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) k E)≠0 := by
  by_cases hg : E∈segment ℝ (hillRealLabels q hq hr (2*k-1):ℂ) (hillRealLabels q hq hr (2*k):ℂ)
  · have hx := re_mem_Icc_of_mem_real_segment _ _
      (monotone_hillRealLabels q hq hr (show 2*k-1≤2*k by omega)) E hg
    have hi := im_eq_zero_of_mem_real_segment _ _ E hg
    have he : E=(E.re:ℂ) := by apply Complex.ext <;> simp [hi]
    rw [he,hillL2RealGapPrimitiveSquare_on_gap q hq hr k hk E.re hx]
    exact deriv_coshSquareCoordinate_sq_ne_zero _ (hillRealGapProfile_nonneg q hq hr k hk E.re hx)
  · exact hillShiftedPrimitive_coshSquare_derivative_ne_zero_of_cut q hq hr k E
      ((hillRealGapContour_geometry q hq hr k hk).2.2.2.2 ⟨hE,hg⟩)

theorem analyticOnNhd_hillFilledPrimitiveRootQuotient (k : ℕ) (hk : 1≤k) :
    AnalyticOnNhd ℂ (hillFilledPrimitiveRootQuotient (SpectralWeight.one.toCoeff q) k)
      (ball (hillRealGapCenter q hq hr k:ℂ)
        (hillRealGapHalfLength q hq hr k+2*hillRealGapCollar q hq hr k)) := by
  intro E hE
  have hS := analyticOnNhd_hillL2RealGapPrimitiveSquare q hq hr k hk E hE
  have hD := (analyticOnNhd_coshSquareCoordinate.deriv _ (mem_univ _)).comp hS
  exact analyticAt_const.mul ((analyticAt_const.mul hD).inv
    (mul_ne_zero (by norm_num) (hillShiftedPrimitive_coshSquare_derivative_ne_zero q hq hr k hk E hE)))

/-- Literal agreement with the globally normalized physical quotient,
including its sign, at every point of the original cut domain. -/
theorem hillFilledPrimitiveRootQuotient_eq_physical (k : ℕ) (E : ℂ)
    (hE : E∈hillL2RealCutDomain q hq hr) :
    hillFilledPrimitiveRootQuotient (SpectralWeight.one.toCoeff q) k E =
      (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E+I*(k:ℂ)*Real.pi) /
        hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E := by
  have hD := hillShiftedPrimitive_coshSquare_derivative_ne_zero_of_cut q hq hr k E hE
  have hroot := hillL2RealCutRoot_ne_zero q hq hr E hE
  have hh := hillShiftedPrimitive_coshSquare_derivative_identity q k E
  dsimp only [hillFilledPrimitiveRootQuotient]
  field_simp
  linear_combination -hh

end NLS.KdV
