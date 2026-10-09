import NLS.ComplexAnalysis.NearIdentityClosedSubspaceInverse
import NLS.ComplexAnalysis.AnalyticUnitDerivativeInverse

/-! # Local inverse preservation of a closed real subspace

Normalize an invertible derivative to the identity, then apply the closed
subspace fixed-point argument on a sufficiently small ball.
-/
noncomputable section
open Set Filter Topology Metric
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An analytic local inverse preserves a closed real subspace if the map
and the inverse derivative preserve it locally. -/
theorem eventually_mem_closedSubmodule_of_localInverse
    {F G : E → E} {x : E} (hF : AnalyticAt ℂ F x) (hu : IsUnit (fderiv ℂ F x))
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E)) (hx : x ∈ S)
    (hreal : ∀ᶠ y in 𝓝 x, y ∈ S → F y ∈ S)
    (hK : MapsTo ⇑(Ring.inverse (fderiv ℂ F x)) (S : Set E) (S : Set E))
    (hG : ContinuousAt G (F x)) (hGx : G (F x) = x)
    (hright : ∀ᶠ z in 𝓝 (F x), F (G z) = z) :
    ∀ᶠ z in 𝓝 (F x), z ∈ S → G z ∈ S := by
  let K := Ring.inverse (fderiv ℂ F x)
  let H : E → E := fun y => K (F y)
  have hH : AnalyticAt ℂ H x := (K.analyticAt (F x)).comp hF
  have hDH : fderiv ℂ H x = 1 := by
    have hh := (K.hasFDerivAt.comp x hF.differentiableAt.hasFDerivAt).fderiv
    change fderiv ℂ H x = K.comp (fderiv ℂ F x) at hh
    rw [hh]
    exact Ring.inverse_mul_cancel _ hu
  have hnear : ∀ᶠ y in 𝓝 x, ‖fderiv ℂ H y-1‖ < (1/2 : ℝ) := by
    filter_upwards [hH.fderiv.continuousAt
      (ball_mem_nhds (fderiv ℂ H x) (by norm_num : (0 : ℝ) < 1/2))] with y hy
    simpa only [mem_preimage,mem_ball,dist_eq_norm,hDH] using hy
  have hmap : ∀ᶠ y in 𝓝 x, y ∈ S → H y ∈ S := by
    filter_upwards [hreal] with y hy hyr
    exact hK (hy hyr)
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp ((hH.eventually_analyticAt.and hnear).and hmap)
  have hGy : ∀ᶠ y in 𝓝 (F x), G y ∈ ball x R := by
    apply hG
    rw [hGx]
    exact ball_mem_nhds x hR
  have hKy : ∀ᶠ y in 𝓝 (F x), ‖K y-H x‖ < (R/2)/2 := by
    filter_upwards [K.continuous.continuousAt
      (ball_mem_nhds (K (F x)) (by positivity : (0 : ℝ) < (R/2)/2))] with y hy
    simpa only [mem_preimage,mem_ball,dist_eq_norm] using hy
  filter_upwards [hGy,hKy,hright] with y hyG hyK hFG hyr
  exact mem_closedSubmodule_of_near_identity_inverse H x R (R/2)
    (by positivity) (by linarith) (fun z hz => (hball hz).1.1)
    (fun z hz => (hball hz).1.2.le) S hS hx (fun z hz => (hball hz).2)
    (K y) (hK hyr) hyK (G y) hyG (by change K (F (G y)) = K y; rw [hFG])

end NLS.ComplexAnalysis
