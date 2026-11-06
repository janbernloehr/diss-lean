import NLS.KdV.HillFiniteGapPhysicalPhase
import NLS.ComplexAnalysis.QuarticInversionContour

/-! # Actual physical energy in the constructed finite-gap phase contour -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.KdV

/-- The constructed phase of every smooth real mean-zero finite-gap Hill
source has the exact physical energy contour coefficient. This is a
frequency-circle identity for that actual discriminant phase; matching it
to the globally normalized source primitive is a separate obligation. -/
theorem exists_hill_finiteGap_physical_energy_contour
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0)
    (N : ℕ) (hN : 1 ≤ N)
    (hclosed : ∀ n : ℕ, N ≤ n →
      hillHminusRealLabels (hillOriginalHminusSource (hillContinuousCoefficients Q))
          (hillOriginalHminusSource_real _ hr) (2*n) =
        hillHminusRealLabels (hillOriginalHminusSource (hillContinuousCoefficients Q))
          (hillOriginalHminusSource_real _ hr) (2*n-1)) :
    ∃ T : ℝ, 0 < T ∧ ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ B 0 = 0 ∧
      (∀ z : ℂ, T < ‖z‖ → 2*cosh (-I*z+B z⁻¹) =
        classicalHillDiscriminant (hillUnitPotentialCurve Q) (z^2)) ∧
      ∀ R : ℝ, T ≤ R →
        (∮ z in C(0,R), (-I*z+B z⁻¹)^4*(2*z)) =
          -(Real.pi : ℂ)*I*classicalHamiltonian (fun x => Q (x : AddCircle (2 : ℝ))) := by
  obtain ⟨T,hT,B,hB,hB0,hrep,h1,h2,h3,h4,h5⟩ :=
    exists_hill_finiteGap_physical_phase Q hr hf hp hmean N hN hclosed
  obtain ⟨S,hS,hcontour⟩ := exists_phase_fourth_weighted_contour B hB hB0
    (classicalQuadraticInvariant (fun x => Q (x : AddCircle (2 : ℝ))))
    (classicalHamiltonian (fun x => Q (x : AddCircle (2 : ℝ)))) h1 h2 h3 h4 h5
  exact ⟨max T S,hT.trans_le (le_max_left _ _),B,hB,hB0,
    fun z hz => hrep z ((le_max_left _ _).trans_lt hz),
    fun R hR => hcontour R ((le_max_right _ _).trans hR)⟩

end NLS.KdV
