import NLS.ZakharovShabat.SourceFiniteGapProfileIdentity

/-! # The global sharp cubic-action estimate

The finite-gap representation proves the cubic lower bound on finite-gap
sources. Continuity and density extend it to every real source at every
finite p>1; collapsed gaps are handled without dividing by their length.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)

/-- The sharp cubic-action lower bound holds for every actual real source at every finite p>1. -/
theorem real_action_sq_le_cubic (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (3/4:ℝ)*‖sourceComplexAction hp hp1 n φ.val‖^2 ≤ (A.moment n 3 φ.val).re := by
  apply (A.real_action_sq_le_cubic_iff_finiteGap n).mpr _ φ
  intro ψ hf
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n = 0
  · rw [← A.moment_one n (A.realType_subset_domain ψ.property),
      A.moment_of_collapsed ψ.val (A.realType_subset_domain ψ.property) n hg 1,
      A.moment_of_collapsed ψ.val (A.realType_subset_domain ψ.property) n hg 3]
    norm_num
  obtain ⟨V,_,_,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hcenter⟩ := hC ψ
  have hψ : ψ.val ∈ Metric.ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact Metric.mem_ball_self C.discs.sourceRadius_pos
  exact A.real_action_sq_le_cubic_of_actual_gap_identity ψ n (A.summable_actions_of_finiteGap ψ hf)
    (C.real_profile_eq_actual_correction_finiteGap n ψ hψ hf hg)

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas
