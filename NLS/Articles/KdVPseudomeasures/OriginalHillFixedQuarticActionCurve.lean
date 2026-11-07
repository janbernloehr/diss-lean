import NLS.Articles.KdVPseudomeasures.OriginalHillQuarticContourEnclosing
import NLS.Articles.KdVPseudomeasures.OriginalHillActionCurveGapSupport
import NLS.Articles.KdVPseudomeasures.OriginalHillH1ActionTangent

/-! One admissible exterior circle represents the ACTUAL physical
complex energy on a whole germ of the genuine finite-gap action curve.
Its radius may be chosen above any prescribed lower bound. -/
noncomputable section
open Set Metric Filter Topology Complex NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem exists_fixed_quarticEnergyContour_on_actionCurve
    (P : HillProductEquationPatch) {W : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n : ℕ+) (q : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus)
    (hq : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ P.momentSource C) (T : ℝ) :
    ∃ R : ℝ, 0 < R ∧ T ≤ R ∧
      sphere (0:ℂ) R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num)
        (P.sourcePsi (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))) ∧
      ∀ᶠ t : ℝ in 𝓝 0,
        P.quarticEnergyContour W 0 R
          (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillH1ActionCurve n q t)))=
          periodOneKdVHamiltonian (signedOneRealToScalarDomain (hillH1ActionCurve n q t)) := by
  let Q := hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)
  let γ : ℝ → PeriodOneHminusOne := fun t =>
    hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillH1ActionCurve n q t))
  have hlim : Tendsto γ (𝓝 0) (𝓝 Q) := by
    simpa only [γ,hillH1ActionCurve_zero] using (hasDerivAt_hillH1ActionCurve_rough_zero n q).continuousAt.tendsto
  let B := P.parent.parent.miuraBall.actionBall
  have hr : IsRealPeriodOneHminusOne Q := (hillIntegerSourceInclusion 1 q).property
  let u : PeriodOneRealL2 := ⟨B.lift Q,B.lift_real Q (P.parent.subset (P.subset hq.1)).1 hr⟩
  let φ : realTypeSourceSubmodule 2 := hillMiuraRealSource u
  obtain ⟨S,hsupport⟩ := exists_hillH1ActionCurve_signed_gap_support P n q hf
  obtain ⟨R,hR,hTR,hcircle,hseg⟩ := exists_sourceCanonicalRoot_circle_enclosing_finite_gaps
    (by simp) (by norm_num) φ.val S T
  have hψlim : Tendsto (fun t : ℝ => P.sourcePsi (γ t)) (𝓝 0) (𝓝 φ.val) :=
    (P.analytic_sourcePsi Q hq.1).continuousAt.tendsto.comp hlim
  have hsegments := hψlim.eventually
    (eventually_sourcePeriodicSegments_subset_ball (by simp) (by norm_num) φ S R hseg)
  have hsource := hlim.eventually ((P.momentSource_open C).mem_nhds hq)
  refine ⟨R,hR,hTR,hcircle,?_⟩
  filter_upwards [hsegments,hsource] with t ht hCt
  apply hillH1_quarticEnergyContour_eq_physical_of_enclosing P C (hillH1ActionCurve n q t)
    (hillH1ActionCurve_finiteGap n q hf t) hCt R hR
  intro k hk
  exact ht k (by_contra fun hnot => hk (hsupport t hCt.1 k hnot))

end NLS.Articles.KdVPseudomeasures
