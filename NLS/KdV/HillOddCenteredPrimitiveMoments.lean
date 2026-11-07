import NLS.KdV.HillPrimitiveMomentsPhysical
import NLS.ZakharovShabat.SourceOddWeightedMomentCircle

/-! ALL odd centered moments of the actual Hill differential vanish on
the original assigned positive frequency circles. The source can be
complex and the selected gap can be collapsed. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch
variable {W : Set (CoeffPair 2)}

theorem odd_centeredMoment_eq_zero (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (l : ℕ) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) :
    (∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)),
      (sourceFullAbelianPrimitive (by simp) (by norm_num) W (m:ℤ) (z,P.sourcePsi q))^(2*l+1) *
        P.abelianFrequencyDifferential n (z,q)) = 0 := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq.1).2 (m:ℤ)
    (P.centers (m:ℤ)) (P.radii (m:ℤ)) (P.radii_pos _) (P.discs_eq _)
  have he := C.odd_weighted_moment_circle_eq_zero (m:ℤ) l (P.sourcePsi q) hq.2
    (P.centers (m:ℤ):ℂ) (P.radii (m:ℤ)) (P.radii_pos _).le
    D.closedBall_subset_omittedDomain D.sphere_subset_rootDomain
    (fun z => P.abelianGapNumerator n m (z,q)) (by
      intro z hz
      exact (P.analytic_abelianGapNumerator_on_patch n m (z,q) ⟨hz,hq.1⟩).comp
        (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const))
  convert he using 1
  apply circleIntegral.integral_congr (P.radii_pos (m:ℤ)).le
  intro z hz
  dsimp only
  rw [P.abelianFrequencyDifferential_eq_gap_quotient n m (z,q) (D.sphere_subset_rootDomain hz)]

end NLS.KdV.HillProductEquationPatch
