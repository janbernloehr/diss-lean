import NLS.KdV.HillHminusOneCanonicalRealLabels
import NLS.KdV.HillHminusOriginalSheets
import NLS.KdV.HillCanonicalRealLabels

noncomputable section
set_option autoImplicit false
open Set Complex
open scoped Classical
namespace NLS.KdV

/-- EVERY native canonical periodic label is the original physical label,
from the lowest root onwards, including all repeated/collapsed endpoints.
Equality of the actual entire radicands and of every analytic multiplicity
fixes the full monotone enumeration; no agreement of tails is assumed. -/
theorem hillHminusLabels_original_source (q : RealPeriodOneHillPotential) :
    hillHminusLabels (hillOriginalHminusSource q.val)
      (hillOriginalHminusSource_real q.val q.property.2)=
      hillRealLabels q.val q.property.1 q.property.2 := by
  apply ordered_nat_enumeration_eq_of_multiplicity
  · exact hillHminusLabels_finite_fiber _ _
  · intro x
    exact (hillRealLabels_global_multiplicity q.val q.property.1 q.property.2 x).1
  · exact monotone_hillHminusLabels _ _
  · exact monotone_hillRealLabels q.val q.property.1 q.property.2
  · intro x
    rw [hillHminusLabels_global_multiplicity,
      (hillRealLabels_global_multiplicity q.val q.property.1 q.property.2 x).2]
    rw [show hillHminusRadicand (hillOriginalHminusSource q.val)=
      hillL2Radicand (SpectralWeight.one.toCoeff q.val) from
      funext (hillHminusRadicand_original_source_agreement q.val q.property.1)]

end NLS.KdV
