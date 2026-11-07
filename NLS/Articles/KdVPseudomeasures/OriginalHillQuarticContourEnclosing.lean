import NLS.Articles.KdVPseudomeasures.OriginalHillQuarticPhaseVariation
import NLS.ZakharovShabat.SourceFullAbelianPhysicalContourLocal

/-! The actual quartic energy contour has its physical value on ANY
positive circle enclosing the open gaps. Collapsed gaps remain filled. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem hillH1_quarticEnergyContour_eq_physical_of_enclosing
    (P : HillProductEquationPatch) {W : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus)
    (hq : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ P.momentSource C)
    (R : ℝ) (hR : 0 < R)
    (hgap : ∀ k : ℤ, canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (P.sourcePsi (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))))
      (periodOnePotential_mem _) k ≠ 0 →
      sourcePeriodicSegment (by simp) (by norm_num)
        (P.sourcePsi (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))) k ⊆ ball 0 R) :
    P.quarticEnergyContour W 0 R (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))=
      periodOneKdVHamiltonian (signedOneRealToScalarDomain q) := by
  let Q := hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)
  obtain ⟨E⟩ := C.charts (P.sourcePsi Q) hq.2
  obtain ⟨T,_,hphysical⟩ := hillH1_exists_quarticEnergyContour_eq_physical P C q hf hq
  let S := max R T
  have ha : AnalyticOnNhd ℂ (fun z => z*(P.liftedAbelianPrimitive W 0 (z,Q))^4)
      (closedBall 0 S \ ball 0 R) := by
    intro z hz
    have hzO : z ∈ sourceOpenGapComplement (by simp) (by norm_num) (P.sourcePsi Q) := by
      intro k hk hzk
      exact hz.2 (hgap k hk hzk)
    exact analyticAt_id.mul ((sourceFullAbelianPrimitive_spectral_analytic E 0 z hzO).pow 4)
  have he := circleIntegral_eq_of_differentiable_on_annulus_off_countable hR (le_max_left R T)
    countable_empty ha.continuousOn (by
      intro z hz
      exact (ha z ⟨ball_subset_closedBall hz.1.1,
        fun h => hz.1.2 (ball_subset_closedBall h)⟩).differentiableAt)
  rw [← hphysical S (le_max_right R T)]
  exact congrArg (fun a : ℂ => (2*I/(Real.pi:ℂ))*a) he.symm

end NLS.Articles.KdVPseudomeasures
