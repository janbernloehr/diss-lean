import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Finite products of circles as finite-dimensional topological manifolds

The finite product circle charts are expressed in a Euclidean model with
exactly one real coordinate per circle. The ambient product topology is
retained, including the empty product and its zero-dimensional model.
-/
noncomputable section
open Manifold
namespace NLS.FunctionalAnalysis

/-- Finite products of one-dimensional Euclidean models form the ordinary N-dimensional model. -/
def finiteCircleProductModelHomeomorph (N : ℕ) :
    ModelPi (fun _ : Fin N => EuclideanSpace ℝ (Fin 1)) ≃ₜ EuclideanSpace ℝ (Fin N) := by
  let e : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
    (EuclideanSpace.equiv (Fin 1) ℝ).toHomeomorph.trans (Homeomorph.piUnique (fun _ : Fin 1 => ℝ))
  exact (Homeomorph.piCongrRight (fun _ : Fin N => e)).trans
    (EuclideanSpace.equiv (Fin N) ℝ).toHomeomorph.symm

/-- The standard product-circle atlas, expressed in an N-dimensional Euclidean model. -/
@[instance_reducible]
def finiteCircleProductChartedSpace (N : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin N)) (Fin N → Circle) := by
  let H := ModelPi (fun _ : Fin N => EuclideanSpace ℝ (Fin 1))
  letI : ChartedSpace (EuclideanSpace ℝ (Fin N)) H :=
    (finiteCircleProductModelHomeomorph N).symm.chartedSpace
  exact ChartedSpace.comp (EuclideanSpace ℝ (Fin N)) H (Fin N → Circle)

/-- The atlas makes the product a topological manifold without boundary. -/
theorem finiteCircleProduct_isManifold (N : ℕ) :
    letI := finiteCircleProductChartedSpace N
    IsManifold (𝓡 N) 0 (Fin N → Circle) := by
  let := finiteCircleProductChartedSpace N
  infer_instance

/-- The model dimension is exactly the number of circle factors, also when N=0. -/
theorem finiteCircleProduct_model_finrank (N : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin

end NLS.FunctionalAnalysis
