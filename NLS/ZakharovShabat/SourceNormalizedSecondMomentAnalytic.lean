import NLS.ZakharovShabat.SourceNormalizedSecondMoment
import NLS.ComplexAnalysis.SineSquareCosineMeanSegment

/-! The actual second moment after extracting its squared gap is analytic
on common complex source neighborhoods, including every closed gap.
Only the symmetric squared gap is differentiated. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem normalizedSecondMoment_analytic
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    {V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiIsolatingComplexExtension hp hp1 V s)
    (U : Set (CoeffPair p)) (hU : IsOpen U) (hUV : U ⊆ V)
    (hUC : U ⊆ ball C.discs.source.val C.discs.sourceRadius) (n k : ℤ)
    (hO : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 k)
      (sourceStandardRootOmittedJointDomain hp hp1 U k))
    (hτ : AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ k) U)
    (hγ : AnalyticOnNhd ℂ (fun ψ =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2) U) :
    AnalyticOnNhd ℂ (C.normalizedSecondMoment s n k) U := by
  have hbranch : AnalyticOnNhd ℂ (fun ψ => (s n ψ : Coeff p)) U := by
    intro ψ hψ
    exact (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).analyticAt (s n ψ)).comp
      (hs.analytic n ψ (hUV hψ))
  have hR := sourceMomentRegularNumerator_joint_analytic hp hp1 U n k
    (fun ψ => (s n ψ : Coeff p)) hbranch hO
  let D := ball (C.discs.center k) (C.discs.outer k) ×ˢ U
  have hD : IsOpen D := isOpen_ball.prod hU
  have hsub : D ⊆ sourceStandardRootOmittedJointDomain hp hp1 U k := by
    intro t ht
    exact ⟨ht.2,C.discs.avoids_other t.2 (hUC ht.2) k (ball_subset_closedBall ht.1)⟩
  intro ψ hψ
  have hhalf : AnalyticAt ℂ (fun χ => (sourceStandardRootHalfGap hp hp1 χ k)^2) ψ := by
    have he : (fun χ : CoeffPair p => (sourceStandardRootHalfGap hp hp1 χ k)^2) =
        fun χ => (canonicalPeriodicGap hp hp1 (periodOnePotential χ)
          (periodOnePotential_mem χ) k)^2/4 := by
      funext χ
      unfold sourceStandardRootHalfGap
      ring
    rw [he]
    exact (hγ ψ hψ).div_const
  have hm := analyticAt_parametricSineSquareCosineMean_of_squared_gap_segment
    (fun t : ℂ × CoeffPair p =>
      (sourceFullAbelianCauchyQuotient hp hp1 W k (C.discs.center k) (C.discs.outer k) t)^2 *
        sourceMomentRegularNumerator hp hp1 n k (s n t.2 : Coeff p) t.2 t.1)
    (fun χ => sourceStandardRootMidpoint hp hp1 χ k)
    (fun χ => sourceStandardRootHalfGap hp hp1 χ k) D hD
    (fun t ht => ((C.quotient_analytic k t ⟨ht.1,hUC ht.2⟩).pow 2).mul (hR t (hsub ht)))
    ψ (hτ ψ hψ) hhalf (by
      intro θ _
      exact ⟨C.segment_subset_outer k ψ (hUC hψ)
        (sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ k (Real.cos θ)
          (Real.neg_one_le_cos θ) (Real.cos_le_one θ)),hψ⟩)
  exact analyticAt_const.mul hm

theorem exists_ball_normalizedSecondMoments
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    {V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiIsolatingComplexExtension hp hp1 V s) (hV : IsOpen V)
    (φ : realTypeSourceSubmodule p) (hφV : φ.val ∈ V)
    (hφC : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) :
    ∃ r : ℝ, 0 < r ∧ ball φ.val r ⊆ V ∩ ball C.discs.source.val C.discs.sourceRadius ∧
      ∀ n k : ℤ, AnalyticOnNhd ℂ (C.normalizedSecondMoment s n k) (ball φ.val r) := by
  obtain ⟨O,hO,_,hrealO,hprod⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  obtain ⟨M,hM,_,hrealM,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp
    (((hV.inter isOpen_ball).inter (hO.inter hM)).mem_nhds
      ⟨⟨hφV,hφC⟩,hrealO φ.property,hrealM φ.property⟩)
  refine ⟨r,hr,fun ψ hψ => (hsub hψ).1,?_⟩
  intro n k
  exact C.normalizedSecondMoment_analytic hs _ isOpen_ball
    (fun ψ hψ => (hsub hψ).1.1) (fun ψ hψ => (hsub hψ).1.2) n k
    ((hprod k).2.1.mono (fun t ht => ⟨(hsub ht.1).2.1,ht.2⟩))
    (fun ψ hψ => (hcoord ψ (hsub hψ).2.2 k).1)
    (fun ψ hψ => (hcoord ψ (hsub hψ).2.2 k).2)

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
