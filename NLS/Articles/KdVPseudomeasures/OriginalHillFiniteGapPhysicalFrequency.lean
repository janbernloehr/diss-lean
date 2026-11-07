import NLS.Articles.KdVPseudomeasures.OriginalHillFixedQuarticActionCurve
import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalEnergyReality

/-! The GENUINE physical H1 KdV frequency at every open selected mode
of an actual finite-gap source equals its exact -12 moment series plus
the free cubic. A fixed-radius identity on a genuine action-curve germ
justifies differentiation of the physical energy. -/
noncomputable section
open Set Metric Filter Topology Complex NLS.KdV NLS.Poisson NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem exists_quarticEnergyContour_phase_bracket_eq_physical_frequency
    {P : HillProductEquationPatch} {W : Set (CoeffPair 2)} {n : ℕ+}
    (A : HillPhysicalOnIndexPhaseChart P n)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus)
    (hA : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ A.source)
    (hC : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ P.momentSource C) (T : ℝ) :
    ∃ R : ℝ, 0 < R ∧ T ≤ R ∧
      sphere (0:ℂ) R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num)
        (P.sourcePsi (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))) ∧
      hminusGardnerBracket (P.quarticEnergyContour W 0 R) A.completePhase
        (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))=
          (hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q):ℂ) := by
  let Q := hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)
  have hr : IsRealPeriodOneHminusOne Q := (hillIntegerSourceInclusion 1 q).property
  obtain ⟨R,hR,hTR,hcircle,hgerm⟩ := exists_fixed_quarticEnergyContour_on_actionCurve P C n q hf hC T
  have hH := P.analyticAt_quarticEnergyContour C 0 R hR.le Q hC hcircle
  have hγ := hasDerivAt_hillH1ActionCurve_rough_zero n q
  rw [hillH1ActionCurve_tangent_eq_phase_HamiltonianVector A q hA] at hγ
  have hd := (hH.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 hγ
    (by rw [hillH1ActionCurve_zero])
  change HasDerivAt (fun t : ℝ => P.quarticEnergyContour W 0 R
    (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillH1ActionCurve n q t))))
    ((fderiv ℂ (P.quarticEnergyContour W 0 R) Q) (gardnerHamiltonianVector A.completePhase Q)) 0 at hd
  rw [fderiv_apply_gardnerHamiltonianVector] at hd
  have hp := hd.congr_of_eventuallyEq (Filter.EventuallyEq.symm hgerm)
  have hphysical := hasDerivAt_hillH1ActionCurve_complex_energy n q (A.original_gap_ne_zero_of_real Q hA hr)
  exact ⟨R,hR,hTR,hcircle,hp.unique hphysical⟩

theorem hillH1_finiteGap_physical_frequency_eq_moment_series
    {P : HillProductEquationPatch} {W : Set (CoeffPair 2)} {n : ℕ+}
    (A : HillPhysicalOnIndexPhaseChart P n)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus)
    (hA : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ A.source)
    (hC : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ P.momentSource C) :
    (hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q):ℂ)=
      (2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries W n
        (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) := by
  let Q := hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)
  have hr : IsRealPeriodOneHminusOne Q := (hillIntegerSourceInclusion 1 q).property
  let B := P.parent.parent.miuraBall.actionBall
  have hqB := (P.parent.subset (P.subset hC.1)).1
  let u : PeriodOneRealL2 := ⟨B.lift Q,B.lift_real Q hqB hr⟩
  have hfu := hillMiuraRealSource_finiteGap_of_hillRealFiniteGap (hillIntegerSourceInclusion 1 q) hf
    u B.shift (B.image Q hqB)
  obtain ⟨T,_,hformula⟩ := A.exists_finiteGap_quarticEnergyContour_phase_moment_formula C Q hA hC hr hfu
  obtain ⟨R,_,hTR,hcircle,hphysical⟩ :=
    exists_quarticEnergyContour_phase_bracket_eq_physical_frequency A C q hf hA hC T
  exact hphysical.symm.trans (hformula R hTR hcircle)

theorem originalHill_exists_finiteGap_open_physical_frequency_formula
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus) :
    ∃ P : HillProductEquationPatch, ∃ W : Set (CoeffPair 2),
      ∃ C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W,
        hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ P.momentSource C ∧
        ∀ n : ℕ+, hillHminusCanonicalGapSquare n
          (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))≠0 →
          (hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q):ℂ)=
            (2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries W n
              (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) := by
  obtain ⟨P,W,C,hq,_,_⟩ := originalHill_exists_frequency_moment_neighborhood (hillIntegerSourceInclusion 1 q)
  let Q := hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)
  have hr : IsRealPeriodOneHminusOne Q := (hillIntegerSourceInclusion 1 q).property
  refine ⟨P,W,C,hq,fun n hn => ?_⟩
  obtain ⟨A,_,hA⟩ := exists_hillPhysicalOnIndexPhaseChart P n Q
    (P.real_mem_physicalDirichletSource Q hq.1 hr) hr hn
  exact hillH1_finiteGap_physical_frequency_eq_moment_series A C q hf hA hq

end NLS.Articles.KdVPseudomeasures
