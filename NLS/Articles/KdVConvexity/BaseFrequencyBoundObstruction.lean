import NLS.Articles.KdVConvexity.BaseFrequencyTaylor
import NLS.ComplexAnalysis.UniformScalarDerivativeBound

/-! # The locally uniform O(1) claim (1.7) is incompatible with the base action norm

The coordinatewise analytic frequency extension remains a meaningful target.
Its printed locally uniform bounded tail estimate cannot hold in the exact
ell^(-1,1) norm: physical normalization forces cotangent norms to grow at
least linearly. The contradiction below assumes only the source's claimed
tail bound on one neighborhood of zero, even after discarding finitely many
indices; it does not assume a sequence-valued analytic extension.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.Articles.KdVConvexity

theorem not_locally_uniformly_bounded_physical_base_frequency_tail
    (U0 : Set BaseActionSpace) (hU0 : IsOpen U0)
    (hcone : WeightedCoeff.nonnegativeLocus baseActionWeight 1 ⊆ U0)
    (ω : ℕ+ → BaseActionSpace → ℂ) (hω : ∀ n, AnalyticOnNhd ℂ (ω n) U0)
    (hphysical : ∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1, ∀ n : ℕ+,
      ω n (baseActionInclusion (originalActionInclusion b.val))=originalPhysicalFrequency b n) :
    ¬ ∃ (N : ℕ) (M : ℝ), ∀ᶠ a : BaseActionSpace in 𝓝 0, ∀ n : ℕ+, N ≤ (n : ℕ) →
      ‖ω n a-((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)‖ ≤ M := by
  rintro ⟨N,M,hb⟩
  let f : {n : ℕ+ // N ≤ (n : ℕ)} → BaseActionSpace → ℂ :=
    fun n a => ω n.val a-((8*(n.val : ℝ)^3*Real.pi^3 : ℝ) : ℂ)
  have h0U : (0 : BaseActionSpace) ∈ U0 := hcone (WeightedCoeff.zero_mem_nonnegativeLocus _ _)
  have hf (n : {n : ℕ+ // N ≤ (n : ℕ)}) : AnalyticOnNhd ℂ (f n) U0 := by
    intro a ha
    exact (hω n.val a ha).sub analyticAt_const
  have hb' : ∀ᶠ a : BaseActionSpace in 𝓝 0, ∀ n, ‖f n a‖ ≤ M := by
    filter_upwards [hb] with a ha n
    exact ha n.val n.property
  obtain ⟨K,hK⟩ := NLS.ComplexAnalysis.exists_uniform_fderiv_bound_of_local_bound f U0 hU0 h0U hf M hb'
  obtain ⟨m,hm⟩ := exists_nat_gt (K/6)
  let n : ℕ+ := ⟨m+N+1,by omega⟩
  have hn : N ≤ (n : ℕ) := by change N ≤ m+N+1; omega
  have hd : fderiv ℂ (f ⟨n,hn⟩) 0=fderiv ℂ (ω n) 0 :=
    ((hω n 0 h0U).differentiableAt.hasFDerivAt.sub_const
      (((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ))).fderiv
  have hu := hK ⟨n,hn⟩
  rw [hd] at hu
  have hl := physical_base_frequency_derivative_norm_lower_bound U0 hU0 hcone ω hω hphysical n
  have hnval : (n : ℝ)=(m : ℝ)+(N : ℝ)+1 := by simp only [n,Nat.cast_add,Nat.cast_one,PNat.mk_coe]
  rw [hnval] at hl
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

end NLS.Articles.KdVConvexity
