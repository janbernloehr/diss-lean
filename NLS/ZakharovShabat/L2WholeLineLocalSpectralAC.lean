import NLS.FunctionalAnalysis.LocalPoissonAbsoluteContinuity
import NLS.ZakharovShabat.L2WholeLinePoissonIntegral

/-! # A local resolvent criterion for the actual physical spectral measure -/
noncomputable section
set_option autoImplicit false
open MeasureTheory NLS.FunctionalAnalysis Set
open scoped NNReal
namespace NLS.ZakharovShabat

/-- A local uniform bound on the original physical resolvent expectation
implies absolute continuity of the actual measure on a smaller interval.
The resolvent bound remains a hypothesis to be established inside bands. -/
theorem wholeLineRealSpectralMeasure_restrict_Icc_absolutelyContinuous_of_resolvent_bound
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u))
    (v : WholeLineL2) (a b δ η : ℝ) (C : ℝ≥0) (hδ : 0 < δ) (hη : 0 < η)
    (h : ∀ x ∈ Ioo (a-δ) (b+δ), ∀ ε : ℝ, (hε : 0 < ε) → ε < η →
      ‖inner ℂ v (wholeLineNonrealResolvent u hu ((x : ℂ)+(ε : ℂ)*Complex.I)
        (by simpa using ne_of_gt hε) v)‖ ≤ C) :
    (wholeLineRealSpectralMeasure u hu v).restrict (Icc a b) ≪ (volume : Measure ℝ) := by
  apply absolutelyContinuous_restrict_Icc_of_local_poisson_bound _ a b δ η C hδ hη
  intro x hx ε hε he
  rw [wholeLineRealSpectralMeasure_poisson_integral u hu v x ε hε]
  exact (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (h x hx ε hε he))

end NLS.ZakharovShabat
