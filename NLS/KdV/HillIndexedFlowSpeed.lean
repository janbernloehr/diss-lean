import NLS.KdV.HillIndexedFlowNorm
import NLS.KdV.HillDiscriminantSourceBounds
import NLS.KdV.HillIndexedGapConservation
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Every genuine mean-zero indexed trajectory has a uniform actual
velocity bound on its full interval, derived from its conserved source
norm and fixed physical Dirichlet gap. -/
theorem exists_hillIndexedIntegralCurve_uniform_speed_bound
    (k : ℕ) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t∈Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u : ℝ) (hu : u∈Ioo a b) (hmean : (γ u).val.val 0=0) :
    ∃ A : ℝ, 0<A ∧ ∀ t∈Ioo a b, ‖deriv γ t‖≤A := by
  let B : ℝ := ‖(γ u).val‖
  let D : ℝ := |hillRealGapCenter (γ u).val (γ u).property.1 (γ u).property.2 k|+
    hillRealGapHalfLength (γ u).val (γ u).property.1 (γ u).property.2 k
  have hD : 0≤D := add_nonneg (abs_nonneg _)
    (hillRealGapContour_geometry (γ u).val (γ u).property.1 (γ u).property.2 k hk).1
  obtain ⟨A,hA,hbound⟩ := exists_hillEnergyHamiltonianSource_uniform_energy_bound B D (norm_nonneg _) hD
  refine ⟨A,hA,?_⟩
  intro t ht
  have hp : ‖SpectralWeight.one.toCoeff (γ t).val‖≤B :=
    (SpectralWeight.norm_toCoeff_le SpectralWeight.one (γ t).val).trans_eq
      (hillSource_norm_eq_on_indexed_integralCurve k hk γ a b hγ u t hu ht hmean).symm
  have hE := hillDirichletEnergy_bound_on_indexed_integralCurve k k hk hk γ a b hγ u hu t ht
  rw [(hγ t ht).deriv]
  change ‖hillEnergyHamiltonianSource (SpectralWeight.one.toCoeff (γ t).val)
    (hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 k hk : ℂ)‖≤A
  exact hbound _ hp _ hE

/-- Mean-zero indexed spectral trajectories are uniformly Lipschitz on
any full interval of definition; the bound is not restricted to compact
subintervals. -/
theorem exists_hillIndexedIntegralCurve_lipschitz_bound
    (k : ℕ) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t∈Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u : ℝ) (hu : u∈Ioo a b) (hmean : (γ u).val.val 0=0) :
    ∃ A : ℝ, 0<A ∧ ∀ v∈Ioo a b, ∀ w∈Ioo a b,
      ‖γ v-γ w‖≤A*|v-w| := by
  obtain ⟨A,hA,hbound⟩ := exists_hillIndexedIntegralCurve_uniform_speed_bound k hk γ a b hγ u hu hmean
  refine ⟨A,hA,?_⟩
  intro v hv w hw
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hγ t ht).differentiableAt) hbound (convex_Ioo a b) hw hv
  simpa only [Real.norm_eq_abs] using hh

end NLS.KdV
