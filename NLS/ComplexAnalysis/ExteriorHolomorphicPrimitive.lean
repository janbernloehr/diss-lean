import NLS.ComplexAnalysis.CircleHoleRemoval
import NLS.ComplexAnalysis.AnnularHolomorphicPrimitive

/-! # A primitive on the whole exterior of a disc

Filling the circular hole produces an entire function with an entire
primitive. The zero-period logarithmic Cauchy primitive subtracts the
filling correction throughout the exterior. No choice of a global
principal logarithm or upper bound on the exterior radius is needed.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

/-- Zero circle period is sufficient for a single-valued primitive on the
entire exterior domain, provided the function is analytic up to its boundary. -/
theorem exists_primitive_on_exterior_of_zero_period (f : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (ball c r)ᶜ)
    (hperiod : (∮ z in C(c,r), f z) = 0) :
    ∃ F : ℂ → ℂ, ∀ z ∉ closedBall c r, HasDerivAt F (f z) z := by
  let R := r + 1
  have hrR : r < R := by dsimp [R]; linarith
  let g := circleHoleRemoval f c r R
  have hg : AnalyticOnNhd ℂ g univ := by
    apply analyticOnNhd_circleHoleRemoval f c r R hr hrR univ
    · exact hf.mono (fun _ hz => hz.2)
    · exact subset_univ _
  obtain ⟨G, hG⟩ := exists_primitive_on_convex g univ convex_univ isOpen_univ hg.differentiableOn
  have hAnn : AnalyticOnNhd ℂ f (closedBall c R \ ball c r) :=
    hf.mono (fun _ hz => hz.2)
  have hsphere : AnalyticOnNhd ℂ f (sphere c r) :=
    hf.mono (fun _ hz hb => sphere_disjoint_ball.le_bot ⟨hz, hb⟩)
  refine ⟨fun z => G z + circleLogarithmicPrimitive f c r z, ?_⟩
  intro z hz
  have hd := (hG z (mem_univ z)).add
    (hasDerivAt_circleLogarithmicPrimitive f c r hr.le hsphere hperiod z hz)
  have he : g z = f z + circleCauchyTransform f c r z :=
    circleHoleRemoval_eq_on_exterior f c r R hr hrR hAnn z hz
  simpa only [he, add_neg_cancel_right] using! hd

end NLS.ComplexAnalysis
