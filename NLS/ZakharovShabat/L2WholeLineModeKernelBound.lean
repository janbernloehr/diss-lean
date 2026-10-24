import NLS.FunctionalAnalysis.FinTwoMatrixProductBound
import NLS.ZakharovShabat.L2WholeLineGreenIngredients

/-! # Uniform bounds for the original physical Floquet mode kernels -/
noncomputable section
set_option autoImplicit false
open Set Matrix Filter NLS.FunctionalAnalysis
open scoped Matrix.Norms.Elementwise Topology
namespace NLS.ZakharovShabat

/-- The projected full fundamental kernel in the original physical coordinates.
The stable and unstable branches of a Green formula use the two root orders. -/
def l2FloquetModeKernel (u : IntervalPairL2) (z μ ν : ℂ) (t s : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  l2WholeLineFundamentalMatrix u z t * floquetRootProjection (l2Monodromy u z) μ ν *
    (l2WholeLineFundamentalMatrix u z s)⁻¹

/-- The actual mode kernels are uniformly bounded on compact input/output
time sets near every parameter with distinct Floquet roots. This estimate
is uniform in either ordering of the reciprocal roots. -/
theorem eventually_norm_l2FloquetModeKernel_le (u : IntervalPairL2) (z₀ : ℂ)
    (hdisc : (l2Monodromy u z₀).trace^2-4 ≠ 0) (L : Set ℝ) (hL : IsCompact L) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 z₀, ∀ μ ν : ℂ,
      (l2Monodromy u z).trace = μ+ν → μ*ν = 1 →
      ∀ t ∈ L, ∀ s ∈ L, ‖l2FloquetModeKernel u z μ ν t s‖ ≤ C := by
  obtain ⟨A,hA,hF⟩ := bounded_l2WholeLineFundamentalMatrix_and_inverse_on_compact
    u (Metric.closedBall z₀ 1) L (isCompact_closedBall _ _) hL
  obtain ⟨D,hD,hP⟩ := eventually_norm_l2FloquetRootProjection_le u z₀ hdisc
  refine ⟨4*A^2*D,by positivity,?_⟩
  have hball : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.closedBall z₀ 1 :=
    Metric.closedBall_mem_nhds z₀ zero_lt_one
  filter_upwards [hball,hP] with z hz hp μ ν hsum hprod t ht s hs
  exact norm_finTwo_matrix_triple_le _ _ _ A D hA.le hD.le
    (hF z hz t ht).1 (hp μ ν hsum hprod) (hF z hz s hs).2

end NLS.ZakharovShabat
