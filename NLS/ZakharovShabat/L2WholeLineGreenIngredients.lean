import NLS.ZakharovShabat.L2WholeLineFundamentalJoint
import NLS.ZakharovShabat.FloquetLocalProjectionBound

/-! # Uniform physical ingredients for local Floquet Green estimates -/
noncomputable section
set_option autoImplicit false
open Set Matrix Filter
open scoped Matrix.Norms.Elementwise Topology
namespace NLS.ZakharovShabat

/-- On compact frequency and time sets both directions of the original
physical fundamental matrix are uniformly bounded. -/
theorem bounded_l2WholeLineFundamentalMatrix_and_inverse_on_compact
    (u : IntervalPairL2) (K : Set ℂ) (L : Set ℝ) (hK : IsCompact K) (hL : IsCompact L) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ t ∈ L,
      ‖l2WholeLineFundamentalMatrix u z t‖ ≤ C ∧
      ‖(l2WholeLineFundamentalMatrix u z t)⁻¹‖ ≤ C := by
  have hc : Continuous (fun q : ℂ × ℝ => ((q.1,u),q.2)) :=
    (continuous_fst.prodMk continuous_const).prodMk continuous_snd
  have hf := continuous_l2WholeLineFundamentalMatrix_joint.comp hc
  have hi := continuous_inv_l2WholeLineFundamentalMatrix_joint.comp hc
  obtain ⟨A,hA⟩ := (hK.prod hL).exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨B,hB⟩ := (hK.prod hL).exists_bound_of_continuousOn hi.continuousOn
  let C := max (max A B) 0+1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right (max A B) 0]
  have hAC : A ≤ C := (le_max_left A B).trans ((le_max_left (max A B) 0).trans (by dsimp [C]; linarith))
  have hBC : B ≤ C := (le_max_right A B).trans ((le_max_left (max A B) 0).trans (by dsimp [C]; linarith))
  refine ⟨C,hC,fun z hz t ht => ⟨?_,?_⟩⟩
  · exact (hA (z,t) ⟨hz,ht⟩).trans hAC
  · exact (hB (z,t) ⟨hz,ht⟩).trans hBC

/-- The actual physical algebraic mode projections are uniformly bounded
near every frequency where the two Floquet roots are distinct. -/
theorem eventually_norm_l2FloquetRootProjection_le (u : IntervalPairL2) (z₀ : ℂ)
    (hdisc : (l2Monodromy u z₀).trace^2-4 ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 z₀, ∀ μ ν : ℂ,
      (l2Monodromy u z).trace = μ+ν → μ*ν = 1 →
        ‖floquetRootProjection (l2Monodromy u z) μ ν‖ ≤ C := by
  apply eventually_norm_floquetRootProjection_le _ z₀ _ hdisc
  exact (continuous_l2Monodromy_joint.comp (continuous_id.prodMk continuous_const)).continuousAt

end NLS.ZakharovShabat
