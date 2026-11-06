import NLS.KdV.HillHminusPhysicalGermDifferentials

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The genuine H-minus-one Gardner bracket is intrinsic to original real
L2 germs. Matching merely their point values would not be sufficient. -/
theorem hillHminusPhysicalGerm_Gardner_eq_of_eventuallyEq
    (q : RealPeriodOneHillPotential) (F G A B : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hA : AnalyticAt ℂ A (hillOriginalHminusSource q.val))
    (hB : AnalyticAt ℂ B (hillOriginalHminusSource q.val))
    (hFA : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = A (hillOriginalHminusSource p.val))
    (hGB : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (hillOriginalHminusSource p.val) = B (hillOriginalHminusSource p.val)) :
    NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource q.val) =
      NLS.Poisson.hminusGardnerBracket A B (hillOriginalHminusSource q.val) := by
  unfold NLS.Poisson.hminusGardnerBracket NLS.Poisson.hminusScalarGradient
  rw [hillHminusPhysicalGerm_fderiv_eq_of_eventuallyEq q F A hF hA hFA,
    hillHminusPhysicalGerm_fderiv_eq_of_eventuallyEq q G B hG hB hGB]

end NLS.KdV
