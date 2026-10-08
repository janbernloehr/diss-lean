import NLS.ZakharovShabat.SourceHigherActionRegularity
import NLS.ZakharovShabat.SourcePrimitivePowerComplexCosine

/-! # The complex weighted gap-boundary formula for higher actions

Symmetric endpoint coordinates make the weighted cosine mean analytic
through collapsed gaps. Real-form uniqueness continues the actual contour
formula to complex source balls simultaneously at every index and level.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- Polynomial spectral weights preserve analyticity of the symmetric cosine mean. -/
theorem higherActionCosineMean_analytic (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (U : Set (CoeffPair p)) (hU : IsOpen U)
    (hUC : U ⊆ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (k : ℕ)
    (hτ : AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ n) U)
    (hγ : AnalyticOnNhd ℂ (fun ψ =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) U) :
    AnalyticOnNhd ℂ (sourceGapCosineMean hp hp1 n (fun t => t.1^k*C.powerNumerator n 0 t.2 t.1)) U := by
  intro ψ hψ
  have hhalf : AnalyticAt ℂ (fun χ => (sourceStandardRootHalfGap hp hp1 χ n)^2) ψ := by
    have he : (fun χ => (sourceStandardRootHalfGap hp hp1 χ n)^2) =
        fun χ => (canonicalPeriodicGap hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2/4 := by
      funext χ
      unfold sourceStandardRootHalfGap
      ring
    rw [he]
    exact (hγ ψ hψ).div_const
  apply analyticAt_parametricCosineMean_of_squared_gap_segment _ _ _ _ (isOpen_ball.prod hU)
    (fun t ht => (analyticAt_fst.pow k).mul (C.powerNumerator_joint_analytic U hUC n 0 hτ hγ t ht))
    ψ (hτ ψ hψ) hhalf
  intro θ _
  refine ⟨C.segment_subset_outer n ψ (hUC hψ) ?_,hψ⟩
  exact sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n (Real.cos θ)
    (Real.neg_one_le_cos θ) (Real.cos_le_one θ)

/-- The weighted analytic mean equals the literal complex boundary integral. -/
theorem higherActionCosineMean_eq_boundaryIntegral (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (n : ℤ) (k : ℕ) (ψ : CoeffPair p) :
    (2*I/Real.pi:ℂ)*sourceGapCosineMean hp hp1 n (fun t => t.1^k*C.powerNumerator n 0 t.2 t.1) ψ =
      (2/Real.pi:ℂ)*∫ θ in (0:ℝ)..Real.pi,
        (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))^k *
        ((sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))*C.gapBoundary n ψ θ true) := by
  unfold sourceGapCosineMean parametricCosineMean
  have he : (∫ θ in (0:ℝ)..Real.pi,
      (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))^k *
        C.powerNumerator n 0 ψ (sourceStandardRootMidpoint hp hp1 ψ n+
          sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))) =
      -I * ∫ θ in (0:ℝ)..Real.pi,
        (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))^k *
        ((sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))*C.gapBoundary n ψ θ true) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [C.powerNumerator_cosine]
    ring
  rw [he]
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring_nf
  simp only [I_sq]
  ring

end SourceFullAbelianUniformCauchyFamily
namespace SourceHigherActionAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourceHigherActionAtlas hp hp1)

/-- One complex source ball gives the boundary formula at every index and
level, including every collapsed complex gap. -/
theorem exists_ball_all_actions_eq_boundaryIntegral
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (φ : realTypeSourceSubmodule p) (hφC : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) :
    ∃ r : ℝ, 0 < r ∧ ball φ.val r ⊆ A.domain ∩ ball C.discs.source.val C.discs.sourceRadius ∧
      ∀ ψ ∈ ball φ.val r, ∀ (n : ℤ) (k : ℕ), A.action n k ψ =
        (2/Real.pi:ℂ)*∫ θ in (0:ℝ)..Real.pi,
          (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))^k *
          ((sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))*C.gapBoundary n ψ θ true) := by
  obtain ⟨M,hM,_,hrealM,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp
    ((A.isOpen_domain.inter (isOpen_ball.inter hM)).mem_nhds
      ⟨A.realType_subset_domain φ.property,hφC,hrealM φ.property⟩)
  let U := ball φ.val r
  have hUC : U ⊆ ball C.discs.source.val C.discs.sourceRadius := fun _ h => (hsub h).2.1
  refine ⟨r,hr,fun ψ hψ => ⟨(hsub hψ).1,hUC hψ⟩,?_⟩
  intro ψ hψ n k
  let G : CoeffPair p → ℂ := fun χ =>
    (2*I/Real.pi:ℂ)*sourceGapCosineMean hp hp1 n (fun t => t.1^k*C.powerNumerator n 0 t.2 t.1) χ
  have hG : AnalyticOnNhd ℂ G U := fun χ hχ => analyticAt_const.mul
    (C.higherActionCosineMean_analytic U isOpen_ball hUC n k
      (fun χ hχ => (hcoord χ (hsub hχ).2.2 n).1)
      (fun χ hχ => (hcoord χ (hsub hχ).2.2 n).2) χ hχ)
  have hid := eqOn_sourceRealCenteredBalls_of_real_agreement hp
    ⟨φ.val,φ.property⟩ ⟨φ.val,φ.property⟩ r r (A.action n k) G
    ((A.analytic_action n k).mono (fun _ h => (hsub h).1)).differentiableOn hG.differentiableOn (by
      intro χ hχ
      change A.action n k χ.val = (2*I/Real.pi:ℂ)*sourceGapCosineMean hp hp1 n _ χ.val
      rw [C.higherActionCosineMean_eq_boundaryIntegral]
      let R := (C.discs.inner n+C.discs.outer n)/2
      have hi : C.discs.inner n ≤ R := by dsimp [R]; linarith [C.discs.inner_lt n]
      have ho : R < C.discs.outer n := by dsimp [R]; linarith [C.discs.inner_lt n]
      rw [A.action_eq_real ⟨χ.val,χ.property⟩ n k,
        ← C.higherActionCircle_eq_real n k ⟨χ.val,χ.property⟩ (hUC hχ.1) R hi ho]
      by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential χ.val) (periodOnePotential_mem χ.val) n = 0
      · rw [C.higherActionCircle_eq_zero_of_collapsed n k ⟨χ.val,χ.property⟩ (hUC hχ.1) hgap R hi ho]
        simp only [C.gapBoundary_eq_zero_of_collapsed n χ.val hgap,mul_zero,intervalIntegral.integral_zero]
      · exact C.higherActionCircle_eq_boundaryIntegral n k ⟨χ.val,χ.property⟩ (hUC hχ.1) hgap R hi ho)
  exact (hid ⟨hψ,hψ⟩).trans (C.higherActionCosineMean_eq_boundaryIntegral n k ψ)

end SourceHigherActionAtlas
end NLS.ZakharovShabat
