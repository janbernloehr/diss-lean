import NLS.KdV.HillHminusOriginalSheets

noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

/-- Exact original physical labels, including every repeated endpoint. -/
theorem hillHminusRealLabels_original_source (q : RealPeriodOneHillPotential) :
    hillHminusRealLabels (hillOriginalHminusSource q.val)
      (hillOriginalHminusSource_real q.val q.property.2)=
      hillRealLabels q.val q.property.1 q.property.2 :=
  hillHminusRealLabels_eq_physical q

end NLS.KdV
