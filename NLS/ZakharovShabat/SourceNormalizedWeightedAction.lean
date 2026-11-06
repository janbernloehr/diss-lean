import NLS.ComplexAnalysis.SineSquareCosineMeanSegment
import NLS.ZakharovShabat.SourceHigherActionComplexCosine

/-! # Analytic normalized higher actions without gap division

The actual filled primitive quotient supplies every polynomially weighted
action divided by the squared gap. The definition includes collapsed
complex gaps and uses only symmetric endpoint coordinates for regularity.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

def normalizedWeightedAction (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (n : ℤ) (k : ℕ) (ψ : CoeffPair p) : ℂ :=
  (-I/(2*Real.pi : ℂ))*parametricSineSquareCosineMean
    (fun t : ℂ × CoeffPair p => t.1^k*sourceFullAbelianCauchyQuotient hp hp1 W n
      (C.discs.center n) (C.discs.outer n) t)
    (fun χ => sourceStandardRootMidpoint hp hp1 χ n)
    (sourceStandardRootHalfGap hp hp1 ψ n,ψ)

theorem normalizedWeightedAction_analytic (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (U : Set (CoeffPair p)) (hU : IsOpen U)
    (hUC : U ⊆ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (k : ℕ)
    (hτ : AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ n) U)
    (hγ : AnalyticOnNhd ℂ (fun ψ =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) U) :
    AnalyticOnNhd ℂ (C.normalizedWeightedAction n k) U := by
  intro ψ hψ
  have hhalf : AnalyticAt ℂ (fun χ => (sourceStandardRootHalfGap hp hp1 χ n)^2) ψ := by
    have he : (fun χ => (sourceStandardRootHalfGap hp hp1 χ n)^2) =
        fun χ => (canonicalPeriodicGap hp hp1 (periodOnePotential χ)
          (periodOnePotential_mem χ) n)^2/4 := by
      funext χ
      unfold sourceStandardRootHalfGap
      ring
    rw [he]
    exact (hγ ψ hψ).div_const
  have hmean := analyticAt_parametricSineSquareCosineMean_of_squared_gap_segment
    (fun t : ℂ × CoeffPair p => t.1^k*sourceFullAbelianCauchyQuotient hp hp1 W n
      (C.discs.center n) (C.discs.outer n) t)
    (fun χ => sourceStandardRootMidpoint hp hp1 χ n)
    (fun χ => sourceStandardRootHalfGap hp hp1 χ n)
    (ball (C.discs.center n) (C.discs.outer n) ×ˢ U) (isOpen_ball.prod hU)
    (fun t ht => (analyticAt_fst.pow k).mul (C.quotient_analytic n t ⟨ht.1,hUC ht.2⟩))
    ψ (hτ ψ hψ) hhalf (by
      intro θ _
      exact ⟨C.segment_subset_outer n ψ (hUC hψ)
        (sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n (Real.cos θ)
          (Real.neg_one_le_cos θ) (Real.cos_le_one θ)),hψ⟩)
  exact analyticAt_const.mul hmean

theorem normalizedWeightedAction_boundary_factor
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (k : ℕ) (ψ : CoeffPair p) :
    (2/Real.pi : ℂ)*∫ θ in (0 : ℝ)..Real.pi,
      (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ : ℂ))^k *
      ((sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ : ℂ))*C.gapBoundary n ψ θ true) =
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 *
          C.normalizedWeightedAction n k ψ := by
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let f : ℝ → ℂ := fun θ => (Real.sin θ : ℂ)^2*
    ((sourceStandardRootMidpoint hp hp1 ψ n+δ*(Real.cos θ : ℂ))^k*
      sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n)
        (sourceStandardRootMidpoint hp hp1 ψ n+δ*(Real.cos θ : ℂ),ψ))
  have he : (fun θ : ℝ =>
      (sourceStandardRootMidpoint hp hp1 ψ n+δ*(Real.cos θ : ℂ))^k *
        ((δ*(Real.sin θ : ℂ))*C.gapBoundary n ψ θ true)) =
      fun θ => (-I*δ^2)*f θ := by
    funext θ
    dsimp only [f,δ,gapBoundary]
    simp only [ite_true]
    ring
  change (2/Real.pi : ℂ)*(∫ θ in (0 : ℝ)..Real.pi, _) = _
  rw [he,intervalIntegral.integral_const_mul]
  change (2/Real.pi : ℂ)*((-I*δ^2)*(∫ θ in (0 : ℝ)..Real.pi, f θ)) =
    _*((-I/(2*Real.pi : ℂ))*(∫ θ in (0 : ℝ)..Real.pi, f θ))
  dsimp only [δ,sourceStandardRootHalfGap]
  ring

theorem normalizedWeightedAction_collapsed
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (k : ℕ) (ψ : CoeffPair p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    C.normalizedWeightedAction n k ψ =
      sourceStandardRootMidpoint hp hp1 ψ n^k*C.normalizedWeightedAction n 0 ψ := by
  simp only [normalizedWeightedAction,parametricSineSquareCosineMean,
    sourceStandardRootHalfGap,hgap,zero_div,zero_mul,add_zero,pow_zero,one_mul]
  have he : (fun θ : ℝ => (Real.sin θ : ℂ)^2*
      (sourceStandardRootMidpoint hp hp1 ψ n^k*sourceFullAbelianCauchyQuotient hp hp1 W n
        (C.discs.center n) (C.discs.outer n) (sourceStandardRootMidpoint hp hp1 ψ n,ψ))) =
      fun θ => sourceStandardRootMidpoint hp hp1 ψ n^k*((Real.sin θ : ℂ)^2*
        sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n)
          (sourceStandardRootMidpoint hp hp1 ψ n,ψ)) := by funext θ; ring
  rw [he,intervalIntegral.integral_const_mul]
  ring

theorem exists_ball_normalizedWeightedActions
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (A : SourceHigherActionAtlas hp hp1)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) :
    ∃ r : ℝ, 0 < r ∧ ball φ.val r ⊆ A.domain ∩ ball C.discs.source.val C.discs.sourceRadius ∧
      ∀ (n : ℤ) (k : ℕ), AnalyticOnNhd ℂ (C.normalizedWeightedAction n k) (ball φ.val r) ∧
        ∀ ψ ∈ ball φ.val r, A.action n k ψ =
          (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 *
            C.normalizedWeightedAction n k ψ := by
  obtain ⟨s,hs,hsub,hformula⟩ := A.exists_ball_all_actions_eq_boundaryIntegral C φ hφ
  obtain ⟨M,hM,_,hrealM,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨t,ht,htsub⟩ := Metric.mem_nhds_iff.mp (hM.mem_nhds (hrealM φ.property))
  let r := min s t
  have hrs : ball φ.val r ⊆ ball φ.val s := ball_subset_ball (min_le_left _ _)
  have hrM : ball φ.val r ⊆ M := fun _ h => htsub (ball_subset_ball (min_le_right _ _) h)
  refine ⟨r,lt_min hs ht,fun ψ hψ => hsub (hrs hψ),?_⟩
  intro n k
  refine ⟨C.normalizedWeightedAction_analytic _ isOpen_ball (fun ψ hψ => (hsub (hrs hψ)).2)
    n k (fun ψ hψ => (hcoord ψ (hrM hψ) n).1) (fun ψ hψ => (hcoord ψ (hrM hψ) n).2),?_⟩
  intro ψ hψ
  rw [hformula ψ (hrs hψ) n k]
  exact C.normalizedWeightedAction_boundary_factor n k ψ

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
