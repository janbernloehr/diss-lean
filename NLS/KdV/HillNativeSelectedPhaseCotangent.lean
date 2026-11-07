import NLS.KdV.HillNativeProductPhase
import NLS.KdV.HillCompletePhaseReality
import NLS.ComplexAnalysis.SelectedPhaseCotangent

/-! The actual complete phase cotangent only uses the selected pair of
actual native coordinate cotangents. Other gaps may all be collapsed. -/
noncomputable section
open Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusCompletePhaseCotangent_eq_selected_pair (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    hillHminusCompletePhaseCotangent n q=(I/2) •
      ((hillHminusNativeCoordinate (n:ℤ) q)⁻¹ • fderiv ℂ (hillHminusNativeCoordinate (n:ℤ)) q-
        (hillHminusNativeCoordinate (-(n:ℤ)) q)⁻¹ • fderiv ℂ (hillHminusNativeCoordinate (-(n:ℤ))) q) := by
  have hn := hillHminusNativeCoordinates_ne_zero_of_real_open_gap n q hr hg
  have hd := fderiv_hillHminusNativeCoordinates_from_action_phase n q hr hg
  exact phaseCotangent_eq_of_signed_pair _ _ hn.1 hn.2 _ _ _ _ hd.1 hd.2

namespace HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

theorem completePhase_fderiv_eq_selected_pair (A : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ A.source) (hr : IsRealPeriodOneHminusOne q) :
    fderiv ℂ A.completePhase q=(I/2) •
      ((hillHminusNativeCoordinate (n:ℤ) q)⁻¹ • fderiv ℂ (hillHminusNativeCoordinate (n:ℤ)) q-
        (hillHminusNativeCoordinate (-(n:ℤ)) q)⁻¹ • fderiv ℂ (hillHminusNativeCoordinate (-(n:ℤ))) q) := by
  rw [← A.completePhaseCotangent_eq_fderiv_of_real q hq hr]
  exact hillHminusCompletePhaseCotangent_eq_selected_pair n q hr (A.original_gap_ne_zero_of_real q hq hr)

end HillPhysicalOnIndexPhaseChart
end NLS.KdV
