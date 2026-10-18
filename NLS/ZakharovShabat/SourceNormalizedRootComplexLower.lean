import NLS.ZakharovShabat.SourceNormalizedActionRootSequenceSpace
import NLS.ZakharovShabat.SourceNormalizedActionLowerBound

/-! # Uniform nonvanishing of all complex normalized roots

Near every real source, every actual normalized root has norm at least one half. The inverse bound holds on the same neighborhood for every signed index.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every real source has a complex neighborhood where all normalized roots stay uniformly away from zero. -/
theorem exists_local_sourceNormalizedActionRoot_uniform_lower
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ ∀ ψ ∈ U, ∀ n : ℤ,
      (1/2:ℝ) ≤ ‖sourceNormalizedActionRoot hp hp1 n ψ‖ ∧
        ‖(sourceNormalizedActionRoot hp hp1 n ψ)⁻¹‖ ≤ 2 := by
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨V,hV,hφV,M,F,hF,_,hcont,_⟩ :=
    exists_local_sourceNormalizedActionRootDeviation_continuousMap (q := p) hp hp1 hp1 hp hhalf φ.val φ.property
  have hFcont : ContinuousAt F φ.val := (hcont φ.val hφV).continuousAt (hV.mem_nhds hφV)
  have hnear : ∀ᶠ ψ in 𝓝 φ.val, ‖F ψ-F φ.val‖ < (1/2:ℝ) := by
    exact (hFcont.sub_const (F φ.val)).norm.eventually (gt_mem_nhds (by simp))
  obtain ⟨U,hUsub,hU,hφU⟩ := _root_.mem_nhds_iff.mp hnear
  refine ⟨U ∩ V,hU.inter hV,⟨hφU,hφV⟩,?_⟩
  intro ψ hψ n
  have hdiff : ‖sourceNormalizedActionRoot hp hp1 n ψ-sourceNormalizedActionRoot hp hp1 n φ.val‖ < (1/2:ℝ) := by
    have he : (F ψ-F φ.val) n = sourceNormalizedActionRoot hp hp1 n ψ-sourceNormalizedActionRoot hp hp1 n φ.val := by
      simp only [lp.coeFn_sub,Pi.sub_apply,hF ψ hψ.2 n,hF φ.val hφV n,sourceNormalizedActionRootDeviation]
      ring
    rw [← he]
    exact (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' (F ψ-F φ.val) n).trans_lt (hUsub hψ.1)
  have hbase : 1 ≤ ‖sourceNormalizedActionRoot hp hp1 n φ.val‖ :=
    (sourceNormalizedActionRoot_re_ge_one hp hp1 φ n).trans (Complex.re_le_norm _)
  have hlower : (1/2:ℝ) ≤ ‖sourceNormalizedActionRoot hp hp1 n ψ‖ := by
    have hn := norm_sub_norm_le (sourceNormalizedActionRoot hp hp1 n φ.val) (sourceNormalizedActionRoot hp hp1 n ψ)
    rw [norm_sub_rev] at hn
    linarith
  refine ⟨hlower,?_⟩
  rw [norm_inv]
  have hi := inv_anti₀ (by norm_num : (0:ℝ) < 1/2) hlower
  norm_num at hi
  exact hi

end NLS.ZakharovShabat
