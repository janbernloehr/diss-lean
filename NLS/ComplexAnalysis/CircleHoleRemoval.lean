import NLS.ComplexAnalysis.CircleCauchyTransformPeriods

/-!
# Analytically filling one circular hole

Inside an isolating circle use its outer Cauchy transform; outside use
the original function plus the inner Cauchy transform. The annular
Cauchy formula identifies these expressions on their overlap. The
filled function is analytic across the hole, subtracts the hole's
period from an enclosing contour, and preserves disjoint periods.
-/

noncomputable section
open Set Complex Filter Topology Metric
open scoped Classical
namespace NLS.ComplexAnalysis

/-- The analytic filling obtained from two concentric isolating circles. -/
def circleHoleRemoval (f : ℂ → ℂ) (c : ℂ) (r R : ℝ) (z : ℂ) : ℂ :=
  if z ∈ ball c R then circleCauchyTransform f c R z
    else f z+circleCauchyTransform f c r z

/-- Outside the inner closed disc, the filling is the original function
plus its inner Cauchy transform, including on the outer circle. -/
theorem circleHoleRemoval_eq_on_exterior (f : ℂ → ℂ) (c : ℂ)
    (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R \ ball c r))
    (z : ℂ) (hz : z ∉ closedBall c r) :
    circleHoleRemoval f c r R z = f z+circleCauchyTransform f c r z := by
  by_cases hzR : z ∈ ball c R
  · simp only [circleHoleRemoval, if_pos hzR]
    have h := circleCauchyTransform_outer_sub_inner f c r R hr hrR.le hf z ⟨hzR,hz⟩
    linear_combination h
  · simp only [circleHoleRemoval, if_neg hzR]

private theorem circleHoleRemoval_density_analytic (f : ℂ → ℂ) (c : ℂ)
    (r R : ℝ) (hrR : r ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R \ ball c r)) :
    AnalyticOnNhd ℂ f (sphere c r) ∧ AnalyticOnNhd ℂ f (sphere c R) := by
  constructor
  · intro z hz
    apply hf z
    exact ⟨mem_closedBall.mpr ((mem_sphere.mp hz).le.trans hrR),
      fun h => sphere_disjoint_ball.le_bot ⟨hz,h⟩⟩
  · intro z hz
    apply hf z
    refine ⟨sphere_subset_closedBall hz, ?_⟩
    intro h
    have hd := mem_sphere.mp hz
    have hb := mem_ball.mp h
    linarith

/-- Filling one hole preserves analyticity on the rest of the source
domain and extends it across the entire removed disc. The surrounding
domain may itself have other holes. -/
theorem analyticOnNhd_circleHoleRemoval (f : ℂ → ℂ) (c : ℂ)
    (r R : ℝ) (hr : 0 < r) (hrR : r < R) (U : Set ℂ)
    (hf : AnalyticOnNhd ℂ f (U \ ball c r)) (hcover : closedBall c R ⊆ U) :
    AnalyticOnNhd ℂ (circleHoleRemoval f c r R) U := by
  have hR : 0 < R := hr.trans hrR
  have hAnn : AnalyticOnNhd ℂ f (closedBall c R \ ball c r) :=
    hf.mono (fun _ h => ⟨hcover h.1,h.2⟩)
  obtain ⟨hinner,houter⟩ := circleHoleRemoval_density_analytic f c r R hrR.le hAnn
  have hCi := analyticOnNhd_circleCauchyTransform f c r hr.le hinner
  have hCo := analyticOnNhd_circleCauchyTransform f c R hR.le houter
  intro z hzU
  by_cases hzR : z ∈ ball c R
  · have hzS : z ∉ sphere c R := fun h => sphere_disjoint_ball.le_bot ⟨h,hzR⟩
    apply (hCo z hzS).congr
    apply (eventually_of_mem (isOpen_ball.mem_nhds hzR) (fun w hw => ?_))
    simp only [circleHoleRemoval, if_pos hw]
  · have hzr : z ∉ closedBall c r := by
      intro h
      have hl := mem_closedBall.mp h
      have hh := not_lt.mp (by simpa only [mem_ball] using hzR)
      linarith
    have hzball : z ∉ ball c r := fun h => hzr (ball_subset_closedBall h)
    have hzS : z ∉ sphere c r := fun h => hzr (sphere_subset_closedBall h)
    apply ((hf z ⟨hzU,hzball⟩).add (hCi z hzS)).congr
    apply eventually_of_mem (isClosed_closedBall.isOpen_compl.mem_nhds hzr)
    intro w hw
    exact (circleHoleRemoval_eq_on_exterior f c r R hr hrR hAnn w hw).symm

/-- On an enclosing circle, filling one hole subtracts precisely its
inner-circle period from the original integral. -/
theorem circleIntegral_circleHoleRemoval_of_enclosed (f : ℂ → ℂ)
    (c d : ℂ) (r R S : ℝ) (hr : 0 < r) (hrR : r < R) (hS : 0 ≤ S)
    (hf : AnalyticOnNhd ℂ f (closedBall c R \ ball c r))
    (hfouter : ContinuousOn f (sphere d S)) (henclosed : closedBall c R ⊆ ball d S) :
    (∮ z in C(d,S), circleHoleRemoval f c r R z) =
      (∮ z in C(d,S), f z)-(∮ z in C(c,r), f z) := by
  have hinner := (circleHoleRemoval_density_analytic f c r R hrR.le hf).1
  have hnest : closedBall c r ⊆ closedBall c R := closedBall_subset_closedBall hrR.le
  have houtside (z : ℂ) (hz : z ∈ sphere d S) : z ∉ closedBall c r :=
    fun h => sphere_disjoint_ball.le_bot ⟨hz,henclosed (hnest h)⟩
  have hcont : ContinuousOn (circleCauchyTransform f c r) (sphere d S) :=
    (analyticOnNhd_circleCauchyTransform f c r hr.le hinner).continuousOn.mono
      (fun z hz h => houtside z hz (sphere_subset_closedBall h))
  calc
    _ = ∮ z in C(d,S), f z+circleCauchyTransform f c r z :=
      circleIntegral.integral_congr hS (fun z hz =>
        circleHoleRemoval_eq_on_exterior f c r R hr hrR hf z (houtside z hz))
    _ = _ := by
      rw [circleIntegral.integral_add (hfouter.circleIntegrable hS) (hcont.circleIntegrable hS),
        circleIntegral_circleCauchyTransform_of_enclosed f c d r S hr.le hS hinner.continuousOn
          (fun _ hz => henclosed (hnest (sphere_subset_closedBall hz)))]
      ring

/-- Filling a hole leaves the periods on all disjoint closed discs
unchanged. This supports induction over a finite hole family. -/
theorem circleIntegral_circleHoleRemoval_of_disjoint (f : ℂ → ℂ)
    (c d : ℂ) (r R S : ℝ) (hr : 0 < r) (hrR : r < R) (hS : 0 ≤ S)
    (hf : AnalyticOnNhd ℂ f (closedBall c R \ ball c r))
    (hfouter : ContinuousOn f (sphere d S)) (hdisj : Disjoint (closedBall c r) (closedBall d S)) :
    (∮ z in C(d,S), circleHoleRemoval f c r R z) = ∮ z in C(d,S), f z := by
  have hinner := (circleHoleRemoval_density_analytic f c r R hrR.le hf).1
  have houtside (z : ℂ) (hz : z ∈ sphere d S) : z ∉ closedBall c r :=
    fun h => hdisj.le_bot ⟨h,sphere_subset_closedBall hz⟩
  have hcont : ContinuousOn (circleCauchyTransform f c r) (sphere d S) :=
    (analyticOnNhd_circleCauchyTransform f c r hr.le hinner).continuousOn.mono
      (fun z hz h => houtside z hz (sphere_subset_closedBall h))
  calc
    _ = ∮ z in C(d,S), f z+circleCauchyTransform f c r z :=
      circleIntegral.integral_congr hS (fun z hz =>
        circleHoleRemoval_eq_on_exterior f c r R hr hrR hf z (houtside z hz))
    _ = _ := by
      rw [circleIntegral.integral_add (hfouter.circleIntegrable hS) (hcont.circleIntegrable hS),
        circleIntegral_circleCauchyTransform_of_exterior f c d r S hr.le hS hinner.continuousOn
          (fun _ hz h => hdisj.le_bot ⟨sphere_subset_closedBall hz,h⟩), add_zero]

end NLS.ComplexAnalysis
