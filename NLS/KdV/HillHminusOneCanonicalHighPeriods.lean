import NLS.KdV.HillHminusOneTailContourGeometry
import NLS.KdV.HillHminusOneAllRealPeriods
import NLS.KdV.HillHminusOneHighMoments
import NLS.ComplexAnalysis.AnalyticCutContour

/-! # Canonical H^-1 periods equal the common high source periods

Nested-circle deformation encloses the same actual gap cut and retains
the exact source primitive on the original circle. One complex H^-1
neighborhood precedes every high index and every polynomial moment.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusRealGap_cut_subset_inner_ball
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    segment ℝ (hillHminusRealLabels q hr (2*(n : ℕ)-1) : ℂ) (hillHminusRealLabels q hr (2*(n : ℕ)) : ℂ) ⊆
      ball (hillHminusRealGapCenter q hr (n : ℕ) : ℂ)
        (hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)) := by
  obtain ⟨hd,hη,hl,hu,_⟩ := hillHminusRealGapContour_geometry q hr (n : ℕ) n.property
  let c := hillHminusRealGapCenter q hr (n : ℕ)
  let d := hillHminusRealGapHalfLength q hr (n : ℕ)
  let η := hillHminusRealGapCollar q hr (n : ℕ)
  apply (convex_ball _ _).segment_subset
  · rw [← hl]
    simp only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    change |c-d-c| < d+η
    rw [show c-d-c = -d by ring,abs_neg,abs_of_nonneg hd]
    linarith
  · rw [← hu]
    simp only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    change |c+d-c| < d+η
    rw [show c+d-c = d by ring,abs_of_nonneg hd]
    linarith

theorem hillHminus_gap_circleIntegral_eq_freeCircle_of_nesting
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+)
    (hnest : closedBall (freeHillValue (n : ℕ) : ℂ) (n : ℝ) ⊆
      closedBall (hillHminusRealGapCenter q hr (n : ℕ) : ℂ)
        (hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)))
    (hcut : segment ℝ (hillHminusRealLabels q hr (2*(n : ℕ)-1) : ℂ) (hillHminusRealLabels q hr (2*(n : ℕ)) : ℂ) ⊆
      ball (freeHillValue (n : ℕ) : ℂ) (n : ℝ))
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (hillHminusRealCutDomain q hr)) :
    (∮ z in C((freeHillValue (n : ℕ) : ℂ),(n : ℝ)), f z) =
      ∮ z in C((hillHminusRealGapCenter q hr (n : ℕ) : ℂ),
        hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)), f z := by
  obtain ⟨_,hη,_,_,hsub⟩ := hillHminusRealGapContour_geometry q hr (n : ℕ) n.property
  exact circleIntegral_eq_of_analytic_cut_nestedCircles f _ _ (hf.mono hsub)
    (freeHillValue (n : ℕ) : ℂ) (hillHminusRealGapCenter q hr (n : ℕ) : ℂ)
    (n : ℝ) _ (by positivity) (hillHminusRealGapContourRadius_pos q hr n) hcut
    (hillHminusRealGap_cut_subset_inner_ball q hr n) hnest
    (closedBall_subset_ball (by linarith))

theorem hillHminus_high_periods_eq_canonical_of_nesting
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+)
    (hnest : closedBall (freeHillValue (n : ℕ) : ℂ) (n : ℝ) ⊆
      closedBall (hillHminusRealGapCenter q hr (n : ℕ) : ℂ)
        (hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)))
    (hcut : segment ℝ (hillHminusRealLabels q hr (2*(n : ℕ)-1) : ℂ) (hillHminusRealLabels q hr (2*(n : ℕ)) : ℂ) ⊆
      ball (freeHillValue (n : ℕ) : ℂ) (n : ℝ))
    (hsource : ∀ z ∈ sphere (freeHillValue (n : ℕ) : ℂ) (n : ℝ), (z,q) ∈ hillHminusContinuationDomain) :
    (∀ m : ℕ, hillHminusHighContourMoment (n : ℕ) m q = hillHminusRealGapContourMoment q hr n m) ∧
      hillHminusHighCubicContourMoment (n : ℕ) q = hillHminusRealGapCubicContourMoment q hr n := by
  constructor
  · intro m
    have hs : (∮ z in C((freeHillValue (n : ℕ) : ℂ),(n : ℝ)), z^m*hillHminusContinuedPrimitive (z,q)) =
        ∮ z in C((freeHillValue (n : ℕ) : ℂ),(n : ℝ)), z^m*hillHminusRealCutPrimitive q z := by
      apply circleIntegral.integral_congr (by positivity)
      intro z hz
      dsimp only
      rw [hillHminusRealCutPrimitive_eq_source q z (hsource z hz)]
    have hd := hillHminus_gap_circleIntegral_eq_freeCircle_of_nesting q hr n hnest hcut
      (fun z => z^m*hillHminusRealCutPrimitive q z)
      ((analyticOnNhd_id.pow m).mul (analyticOnNhd_hillHminusRealCutPrimitive q hr))
    change -(Real.pi : ℂ)⁻¹ * (∮ z in C((freeHillValue (n : ℕ) : ℂ),(n : ℝ)), z^m*hillHminusContinuedPrimitive (z,q)) = _
    rw [hs,hd]
    rfl
  · have hs : (∮ z in C((freeHillValue (n : ℕ) : ℂ),(n : ℝ)), (hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^3) =
        ∮ z in C((freeHillValue (n : ℕ) : ℂ),(n : ℝ)), (hillHminusRealCutPrimitive q z+I*(n : ℂ)*Real.pi)^3 := by
      apply circleIntegral.integral_congr (by positivity)
      intro z hz
      dsimp only
      rw [hillHminusRealCutPrimitive_eq_source q z (hsource z hz)]
    have hd := hillHminus_gap_circleIntegral_eq_freeCircle_of_nesting q hr n hnest hcut
      (fun z => (hillHminusRealCutPrimitive q z+I*(n : ℂ)*Real.pi)^3)
      (((analyticOnNhd_hillHminusRealCutPrimitive q hr).add analyticOnNhd_const).pow 3)
    unfold hillHminusHighCubicContourMoment hillHminusRealGapCubicContourMoment
    rw [hs,hd]

theorem exists_hillHminus_canonical_high_period_agreement (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ V, ∀ ha : IsRealPeriodOneHminusOne a,
        (∀ m : ℕ, hillHminusHighContourMoment (n : ℕ) m a = hillHminusRealGapContourMoment a ha n m) ∧
        hillHminusHighCubicContourMoment (n : ℕ) a = hillHminusRealGapCubicContourMoment a ha n := by
  obtain ⟨Nl,Vl,hNl,hVl,hql,hloc⟩ := exists_hillHminus_canonical_tail_small_localization q
  obtain ⟨Ns,Vs,_,hVs,hqs,hcover⟩ := exists_hillHminus_high_energy_annulus_neighborhood q 1 (by norm_num)
  let N := max (Nl+1) Ns
  refine ⟨N,Vl ∩ Vs,by omega,hVl.inter hVs,⟨hql,hqs⟩,?_⟩
  intro n hn a ha hreal
  have hln : Nl+1 ≤ (n : ℕ) := (le_max_left _ _).trans hn
  have hsn : Ns ≤ (n : ℕ) := (le_max_right _ _).trans hn
  have hg := hillHminus_tail_circle_nesting_of_localization a hreal Nl (n : ℕ) hNl hln (hloc a ha.1 hreal)
  apply hillHminus_high_periods_eq_canonical_of_nesting a hreal n hg.1 hg.2
  intro z hz
  apply hcover a ha.2 n hsn z (sphere_subset_closedBall hz)
  have he : ‖z-(freeHillValue (n : ℕ) : ℂ)‖ = (n : ℝ) := by
    simpa only [mem_sphere,dist_eq_norm] using hz
  rw [one_mul,he]

end NLS.KdV
