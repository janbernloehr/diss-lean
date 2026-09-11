import NLS.FunctionalAnalysis.CircleIntegral
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Circle integration as a bounded linear map

Continuous functions on a compact circle carry the uniform norm. Normalized
circle integration is a bounded complex-linear map, with norm at most the radius.
-/

noncomputable section
open Complex Metric Classical

namespace NLS.CircleIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private def circleExtension {c : ℂ} {r : ℝ} (f : C(sphere c r, E)) (z : ℂ) : E :=
  if hz : z ∈ sphere c r then f ⟨z, hz⟩ else 0

omit [NormedSpace ℂ E] [CompleteSpace E] in
private theorem circleExtension_integrable {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (f : C(sphere c r, E)) : CircleIntegrable (circleExtension f) c r := by
  apply ContinuousOn.circleIntegrable hr
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (sphere c r).domRestrict (circleExtension f) = f := by
    funext z
    exact dif_pos z.property
  rw [he]
  exact f.continuous

/-- Normalized circle integration on the Banach space of continuous functions. -/
def integrationCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (c : ℂ) (r : ℝ) (hr : 0 ≤ r) : C(sphere c r, E) →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun f => (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, r), circleExtension f z
      map_add' := by
        intro f g
        have he : circleExtension (f + g) = circleExtension f + circleExtension g := by
          funext z
          by_cases hz : z ∈ sphere c r <;>
            simp only [circleExtension, hz, ↓reduceDIte, ContinuousMap.add_apply,
              Pi.add_apply, add_zero]
        rw [he]
        dsimp only [Pi.add_apply]
        rw [circleIntegral.integral_add (circleExtension_integrable hr f)
          (circleExtension_integrable hr g), smul_add]
      map_smul' := by
        intro a f
        have he : circleExtension (a • f) = a • circleExtension f := by
          funext z
          by_cases hz : z ∈ sphere c r <;>
            simp only [circleExtension, hz, ↓reduceDIte, ContinuousMap.smul_apply,
              Pi.smul_apply, smul_zero]
        rw [he]
        dsimp only [Pi.smul_apply]
        rw [circleIntegral.integral_smul]
        exact smul_comm _ _ _ }
    r (fun f => circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr
      (fun z hz => by
        simpa only [circleExtension, dif_pos hz] using f.norm_coe_le_norm ⟨z, hz⟩))

/-- Agreement with a function defined on the whole plane requires only agreement
on the integration circle. -/
theorem integrationCLM_eq (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (f : C(sphere c r, E)) (g : ℂ → E) (h : ∀ z : sphere c r, f z = g z) :
    integrationCLM E c r hr f = (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, r), g z := by
  change (2 * Real.pi * I : ℂ)⁻¹ • (∮ z in C(c, r), circleExtension f z) = _
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  simpa only [circleExtension, dif_pos hz] using h ⟨z, hz⟩

/-- The normalized integral has operator norm at most the radius. -/
theorem norm_integrationCLM_le (c : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    ‖integrationCLM E c r hr‖ ≤ r :=
  LinearMap.mkContinuous_norm_le _ hr _

end NLS.CircleIntegral
