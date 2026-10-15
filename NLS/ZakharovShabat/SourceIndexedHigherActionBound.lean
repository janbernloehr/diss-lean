import NLS.ZakharovShabat.SourceIndexedHigherActionCauchy
import NLS.ZakharovShabat.SourceHigherActionPolynomialBound
import NLS.ZakharovShabat.SourceSection19Domain

/-! # Bounds on the full original complex higher-action domain

The same local constants control all indices and spectral powers around
every complex point of the retained Section 19 source domain.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W U : Set (CoeffPair p)}

/-- Uniform polynomial spectral localization on a whole Cauchy source ball. -/
theorem SourceFullAbelianUniformCauchyFamily.spectralRadius_bound
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) :
    ∃ D : ℝ, 0 < D ∧ ∀ ψ ∈ ball C.discs.source.val C.discs.sourceRadius, ∀ n : ℤ,
      sourceGapSpectralRadius hp hp1 ψ n ≤ D*(1+|(n:ℝ)|) := by
  obtain ⟨B,hB⟩ := C.discs.outer_bounded
  have hB0 : 0 ≤ B := ((C.discs.inner_pos 0).trans (C.discs.inner_lt 0)).le.trans (hB 0)
  let M := ‖sourcePeriodicMidpointDisplacement hp hp1 C.discs.source.val‖
  have hM : 0 ≤ M := norm_nonneg _
  refine ⟨Real.pi+M+3*B,by positivity,?_⟩
  intro ψ hψ n
  have hmid (χ : CoeffPair p) (hχ : χ ∈ ball C.discs.source.val C.discs.sourceRadius) :
      ‖sourceStandardRootMidpoint hp hp1 χ n-C.discs.center n‖ ≤ B := by
    exact (mem_ball_iff_norm.mp (C.segment_subset_outer n χ hχ
      (sourcePeriodicMidpoint_mem_segment hp hp1 χ n))).le.trans (hB n)
  have hbase := hmid C.discs.source.val (mem_ball_self C.discs.sourceRadius_pos)
  have hdis := lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne'
    (sourcePeriodicMidpointDisplacement hp hp1 C.discs.source.val) n
  rw [sourcePeriodicMidpointDisplacement_apply] at hdis
  change ‖sourceStandardRootMidpoint hp hp1 C.discs.source.val n-(Real.pi:ℂ)*n‖ ≤ M at hdis
  have hlat : ‖(Real.pi:ℂ)*n‖ = Real.pi*|(n:ℝ)| := by
    simp [abs_of_pos Real.pi_pos]
  have hc : ‖C.discs.center n‖ ≤ Real.pi*|(n:ℝ)|+M+B := by
    have h₁ := norm_sub_le_norm_sub_add_norm_sub (C.discs.center n) (sourceStandardRootMidpoint hp hp1 C.discs.source.val n) ((Real.pi:ℂ)*n)
    rw [norm_sub_rev (C.discs.center n) (sourceStandardRootMidpoint hp hp1 C.discs.source.val n)] at h₁
    have h₂ := norm_le_norm_sub_add (C.discs.center n) ((Real.pi:ℂ)*n)
    rw [hlat] at h₂
    linarith
  have hm : ‖sourceStandardRootMidpoint hp hp1 ψ n‖ ≤ Real.pi*|(n:ℝ)|+M+2*B := by
    have h := norm_le_norm_sub_add (sourceStandardRootMidpoint hp hp1 ψ n) (C.discs.center n)
    linarith [hmid ψ hψ]
  have hh : ‖sourceStandardRootHalfGap hp hp1 ψ n‖ ≤ B := by
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    have hl : ‖l-C.discs.center n‖ ≤ B :=
      (mem_ball_iff_norm.mp (C.segment_subset_outer n ψ hψ (left_mem_segment ℝ _ _))).le.trans (hB n)
    have hr : ‖r-C.discs.center n‖ ≤ B :=
      (mem_ball_iff_norm.mp (C.segment_subset_outer n ψ hψ (right_mem_segment ℝ _ _))).le.trans (hB n)
    have h := norm_sub_le_norm_sub_add_norm_sub r (C.discs.center n) l
    rw [norm_sub_rev (C.discs.center n)] at h
    change ‖(r-l)/2‖ ≤ B
    rw [norm_div,norm_ofNat]
    linarith
  unfold sourceGapSpectralRadius
  nlinarith [Real.pi_pos,mul_nonneg hM (abs_nonneg (n:ℝ)),mul_nonneg hB0 (abs_nonneg (n:ℝ))]

namespace SourceSection19Data
variable (Q : SourceSection19Data hp hp1 W U)
include Q

/-- Scalar analyticity on the unchanged Section 19 domain. -/
theorem analytic_indexedHigherAction (n : ℤ) (k : ℕ) :
    AnalyticOnNhd ℂ (sourceIndexedHigherAction hp hp1 n k) U := by
  intro ψ hψ
  obtain ⟨C,V,_,hψV,_,hVC,_⟩ := Q.local_models ψ hψ
  exact C.analytic_indexedHigherAction n k ψ (hVC hψV)

/-- Local polynomial bounds at every complex source, simultaneously in index and level. -/
theorem exists_local_indexedHigherAction_polynomial_bound (φ : CoeffPair p) (hφ : φ ∈ U) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ U ∧
      ∃ B D : ℝ, 0 < B ∧ 0 < D ∧ ∀ ψ ∈ V, ∀ (n : ℤ) (k : ℕ),
        ‖sourceIndexedHigherAction hp hp1 n k ψ‖ ≤
          B*D^k*(1+|(n:ℝ)|)^k*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := by
  obtain ⟨C,V,hV,hφV,hVU,hVC,M⟩ := Q.local_models φ hφ
  obtain ⟨B,hB,hb⟩ := M.uniform_boundary_bound
  obtain ⟨D,hD,hd⟩ := C.spectralRadius_bound
  refine ⟨V,hV,hφV,hVU,B,D,hB,hD,?_⟩
  intro ψ hψ n k
  rw [C.indexedHigherAction_eq_boundaryIntegral ψ (hVC hψ) n k]
  have h := C.norm_higherActionBoundaryIntegral_le ψ n k _ (fun θ hθ => hb ψ hψ n θ hθ true)
  rw [← sourcePeriodicGapDisplacement_apply hp hp1 ψ n] at h
  calc
    _ ≤ B*sourceGapSpectralRadius hp hp1 ψ n ^ k*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := h.trans_eq (by ring)
    _ ≤ B*(D*(1+|(n:ℝ)|))^k*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := by
      gcongr
      · exact add_nonneg (norm_nonneg _) (norm_nonneg _)
      · exact hd ψ (hVC hψ) n
    _ = _ := by rw [mul_pow]; ring
end SourceSection19Data
end NLS.ZakharovShabat
