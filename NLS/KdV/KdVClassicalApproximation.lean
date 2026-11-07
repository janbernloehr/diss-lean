import NLS.KdV.ClassicalKdVConservation
import Mathlib.Topology.UniformSpace.UniformConvergence

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The classical-approximation solution concept: one sequence of actual
global classical PDE trajectories converges locally uniformly in physical L².
No action or discriminant invariant is a premise. This does not assert
existence of such approximations for arbitrary distributional solutions. -/
def IsKdVSolutionByClassicalApproximation (u : ℝ → RealPeriodOneHillPotential) : Prop :=
  ∃ v : ℕ → ℝ → RealPeriodOneHillPotential,
    (∀ N, IsClassicalKdVTrajectory (v N)) ∧
    ∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn v u atTop (Icc (-T) T)

theorem IsClassicalKdVTrajectory.byClassicalApproximation
    {u : ℝ → RealPeriodOneHillPotential} (hu : IsClassicalKdVTrajectory u) :
    IsKdVSolutionByClassicalApproximation u := by
  refine ⟨fun _ => u,fun _ => hu,?_⟩
  intro _ _ V hV
  exact Eventually.of_forall (fun _ _ _ => refl_mem_uniformity hV)

theorem IsKdVSolutionByClassicalApproximation.mean_conserved
    {u : ℝ → RealPeriodOneHillPotential} (hu : IsKdVSolutionByClassicalApproximation u) (s t : ℝ) :
    (u t).val.val 0 = (u s).val.val 0 := by
  obtain ⟨v,hv,hlim⟩ := hu
  have hC : Continuous (fun p : RealPeriodOneHillPotential => p.val.val 0) :=
    (WeightedCoeff.evalCLM SpectralWeight.one.toWeight 2 0).continuous.comp continuous_subtype_val
  have hlimt := (hlim |t| (abs_nonneg t)).tendsto_at (show t ∈ Icc (-|t|) |t| from ⟨neg_abs_le t,le_abs_self t⟩)
  have hlims := (hlim |s| (abs_nonneg s)).tendsto_at (show s ∈ Icc (-|s|) |s| from ⟨neg_abs_le s,le_abs_self s⟩)
  have ht := hC.continuousAt.tendsto.comp hlimt
  have hs := hC.continuousAt.tendsto.comp hlims
  have he : (fun N => (v N t).val.val 0) = (fun N => (v N s).val.val 0) :=
    funext (fun N => (hv N).mean_conserved s t)
  simp only [Function.comp_def] at ht hs
  rw [he] at ht
  exact tendsto_nhds_unique ht hs

/-- Physical actions are conserved by every pointwise physical-L² limit
of genuine classical KdV trajectories, including all collapsed gaps. -/
theorem IsKdVSolutionByClassicalApproximation.physical_actions_conserved
    {u : ℝ → RealPeriodOneHillPotential} (hu : IsKdVSolutionByClassicalApproximation u)
    (s t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    hillRealGapIntegral (u t).val (u t).property.1 (u t).property.2 n 0 =
      hillRealGapIntegral (u s).val (u s).property.1 (u s).property.2 n 0 := by
  obtain ⟨v,hv,hlim⟩ := hu
  have hlimt := (hlim |t| (abs_nonneg t)).tendsto_at (show t ∈ Icc (-|t|) |t| from ⟨neg_abs_le t,le_abs_self t⟩)
  have hlims := (hlim |s| (abs_nonneg s)).tendsto_at (show s ∈ Icc (-|s|) |s| from ⟨neg_abs_le s,le_abs_self s⟩)
  have ht := (continuous_hillRealGapIntegral n hn 0).continuousAt.tendsto.comp hlimt
  have hs := (continuous_hillRealGapIntegral n hn 0).continuousAt.tendsto.comp hlims
  have he : (fun N => hillRealGapIntegral (v N t).val (v N t).property.1 (v N t).property.2 n 0) =
      (fun N => hillRealGapIntegral (v N s).val (v N s).property.1 (v N s).property.2 n 0) :=
    funext (fun N => (hv N).physical_actions_conserved s t n)
  simp only [Function.comp_def] at ht hs
  rw [he] at ht
  exact tendsto_nhds_unique ht hs

end NLS.KdV
