import NLS.KdV.HillHminusOriginalLabels
import NLS.KdV.HillRealGapIntegrals
import NLS.KdV.HillHminusOneRealPeriodFormulas

/-! # Original physical real gap integrals recover the intrinsic rough periods -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
namespace NLS.KdV

theorem hillHminusRealGapContourMoment_original_source
    (p : RealPeriodOneHillPotential) (n : ℕ+) (m : ℕ) :
    hillHminusRealGapContourMoment (hillOriginalHminusSource p.val)
      (hillOriginalHminusSource_real p.val p.property.2) n m =
      (hillRealGapIntegral p.val p.property.1 p.property.2 (n : ℕ) m : ℂ) := by
  rw [hillHminusRealGapContourMoment_eq_profile_integral,
    hillHminusRealLabels_original_source p]
  apply congrArg Complex.ofReal
  unfold hillRealGapIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  unfold hillHminusRealGapProfile hillRealGapProfile
  dsimp only
  rw [hillHminusDiscriminant_original_source_agreement p.val p.property.1]

end NLS.KdV
