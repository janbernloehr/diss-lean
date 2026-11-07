import NLS.KdV.KdVClassicalApproximation
import NLS.KdV.HillLocallyUniformActionTails

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.KdV

theorem uniformContinuous_hillRealWeightedEmbedding (w : SpectralWeight) :
    UniformContinuous (hillRealWeightedEmbedding w) := by
  have h : UniformContinuous (fun p : RealHillWeightedPotential w =>
      hillPeriodOneUnitPotential w p.val) :=
    ((hillForgetWeight w 2).uniformContinuous.comp (hillPeriodOnePotential w).isometry.uniformContinuous).comp
      uniformContinuous_subtype_val
  exact h.subtype_mk _

/-- Locally uniform approximation in any original weighted Sobolev norm
implies the physical-L² approximation used for the conservation theorem. -/
theorem isKdVSolutionByClassicalApproximation_of_weighted (w : SpectralWeight)
    (u : ℝ → RealHillWeightedPotential w) (v : ℕ → ℝ → RealHillWeightedPotential w)
    (hv : ∀ N, IsClassicalKdVTrajectory (fun t => hillRealWeightedEmbedding w (v N t)))
    (hlim : ∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn v u atTop (Icc (-T) T)) :
    IsKdVSolutionByClassicalApproximation (fun t => hillRealWeightedEmbedding w (u t)) := by
  refine ⟨fun N t => hillRealWeightedEmbedding w (v N t),hv,?_⟩
  intro T hT
  exact (uniformContinuous_hillRealWeightedEmbedding w).comp_tendstoUniformlyOn (hlim T hT)

end NLS.KdV
