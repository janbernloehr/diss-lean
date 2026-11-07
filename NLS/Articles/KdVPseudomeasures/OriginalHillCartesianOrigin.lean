import NLS.Articles.KdVPseudomeasures.OriginalHillNativeCartesianMap
import NLS.KdV.HillAbelianFreeCorrections

/-! The ACTUAL native Cartesian map has the required origin value.
Full free spectral labels, norming-sheet signs and literal phase
corrections are proved inputs for the remaining Fourier differential. -/
noncomputable section
open Complex NLS.KdV
open scoped Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_free_periodic_pair
    (hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne)) (n : ℕ+) :
    hillHminusLabels 0 hr (2*(n:ℕ)-1) = freeHillValue (n:ℕ) ∧
      hillHminusLabels 0 hr (2*(n:ℕ)) = freeHillValue (n:ℕ) :=
  hillHminusLabels_free_pair hr n

theorem original_Hill_free_gap_and_action_zero (n : ℕ+) :
    hillHminusCanonicalGapSquare n 0 = 0 ∧ hillHminusCanonicalAction n 0 = 0 :=
  ⟨hillHminusCanonicalGapSquare_zero n,hillHminusCanonicalAction_zero n⟩

theorem original_Hill_native_Cartesian_map_zero : hillHminusNativeCartesianMap 0 = 0 :=
  hillHminusNativeCartesianMap_zero

theorem original_Hill_native_Cartesian_map_of_zero (q : OriginalHminusOnePotential) (hq : q.val = 0) :
    hillHminusNativeCartesianMap (originalPeriodOneCoefficients q) = 0 := by
  rw [originalPeriodOneCoefficients,hq,map_zero,hillHminusNativeCartesianMap_zero]

theorem original_Hill_free_norming_sheet_and_infinite_correction (n : ℕ+) :
    hillHminusDirichletNorming n 0 = (-1:ℂ)^(n:ℕ) ∧
      hillHminusDirichletSheet n 0 = 0 ∧ hillHminusOffIndexAbelianCorrection n 0 = 0 :=
  ⟨hillHminusDirichletNorming_zero n,hillHminusDirichletSheet_zero n,
    hillHminusOffIndexAbelianCorrection_zero n⟩

end NLS.Articles.KdVPseudomeasures
