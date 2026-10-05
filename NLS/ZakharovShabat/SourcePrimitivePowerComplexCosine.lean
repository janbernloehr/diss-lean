import NLS.ZakharovShabat.SourcePrimitivePowerRealIntegral
import NLS.ZakharovShabat.SourceGapCosineMeanDomain

/-! # Complex-source boundary formulas for primitive-power moments

The analytic numerator depends only on symmetric endpoint coordinates.
Analytic cosine means and real-form uniqueness therefore continue every
odd-moment boundary formula on one source ball, through closed gaps.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem powerNumerator_joint_analytic (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (U : Set (CoeffPair p)) (hUC : U ⊆ ball C.discs.source.val C.discs.sourceRadius)
    (n : ℤ) (m : ℕ)
    (hτ : AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ n) U)
    (hγ : AnalyticOnNhd ℂ (fun ψ =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) U) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => C.powerNumerator n m t.2 t.1)
      (ball (C.discs.center n) (C.discs.outer n) ×ˢ U) := by
  intro t ht
  have hmid := (hτ t.2 ht.2).comp (f := fun t : ℂ × CoeffPair p => t.2) analyticAt_snd
  have hgap := (hγ t.2 ht.2).comp (f := fun t : ℂ × CoeffPair p => t.2) analyticAt_snd
  exact (((C.square_joint_analytic U hUC n hτ hγ t ht).pow m).mul
    (((analyticAt_fst.sub hmid).pow 2).sub hgap.div_const)).mul
      (C.quotient_analytic n t ⟨ht.1,hUC ht.2⟩)

/-- The cosine mean is analytic even when the individual endpoints
cannot be chosen analytically. -/
theorem powerCosineMean_analytic (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (U : Set (CoeffPair p)) (hU : IsOpen U)
    (hUC : U ⊆ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (m : ℕ)
    (hτ : AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ n) U)
    (hγ : AnalyticOnNhd ℂ (fun ψ =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) U) :
    AnalyticOnNhd ℂ (sourceGapCosineMean hp hp1 n (fun t => C.powerNumerator n m t.2 t.1)) U := by
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
    (C.powerNumerator_joint_analytic U hUC n m hτ hγ) ψ (hτ ψ hψ) hhalf
  intro θ _
  refine ⟨C.segment_subset_outer n ψ (hUC hψ) ?_,hψ⟩
  exact sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n (Real.cos θ)
    (Real.neg_one_le_cos θ) (Real.cos_le_one θ)

/-- The analytic mean is the literal boundary-power integral for
arbitrary complex sources, including collapsed gaps. -/
theorem powerCosineMean_eq_boundaryIntegral (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (n : ℤ) (m : ℕ) (ψ : CoeffPair p) :
    (2*I/Real.pi:ℂ)*sourceGapCosineMean hp hp1 n (fun t => C.powerNumerator n m t.2 t.1) ψ =
      (2/Real.pi:ℂ)*∫ θ in (0:ℝ)..Real.pi,
        (sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))*(C.gapBoundary n ψ θ true)^(2*m+1) := by
  unfold sourceGapCosineMean parametricCosineMean
  simp only [C.powerNumerator_cosine,mul_assoc,intervalIntegral.integral_const_mul]
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  simp only [I_sq]
  ring

end SourceFullAbelianUniformCauchyFamily
namespace SourcePrimitivePowerAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)

/-- A specified Cauchy family gives simultaneous boundary formulas
for every odd moment on a common complex neighborhood of a real source. -/
theorem exists_ball_all_odd_moments_eq_boundaryIntegral
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 V)
    (φ : realTypeSourceSubmodule p) (hφC : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) :
    ∃ r : ℝ, 0 < r ∧ ball φ.val r ⊆ A.domain ∩ ball C.discs.source.val C.discs.sourceRadius ∧
      ∀ ψ ∈ ball φ.val r, ∀ (n : ℤ) (m : ℕ), A.moment n (2*m+1) ψ =
        (2/Real.pi:ℂ)*∫ θ in (0:ℝ)..Real.pi,
          (sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))*(C.gapBoundary n ψ θ true)^(2*m+1) := by
  obtain ⟨M,hM,_,hrealM,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp
    ((A.isOpen_domain.inter (isOpen_ball.inter hM)).mem_nhds
      ⟨A.realType_subset_domain φ.property,hφC,hrealM φ.property⟩)
  let U := ball φ.val r
  have hUC : U ⊆ ball C.discs.source.val C.discs.sourceRadius := fun _ h => (hsub h).2.1
  refine ⟨r,hr,fun ψ hψ => ⟨(hsub hψ).1,hUC hψ⟩,?_⟩
  intro ψ hψ n m
  let G : CoeffPair p → ℂ := fun χ =>
    (2*I/Real.pi:ℂ)*sourceGapCosineMean hp hp1 n (fun t => C.powerNumerator n m t.2 t.1) χ
  have hG : AnalyticOnNhd ℂ G U := fun χ hχ => analyticAt_const.mul
    (C.powerCosineMean_analytic U isOpen_ball hUC n m
      (fun χ hχ => (hcoord χ (hsub hχ).2.2 n).1)
      (fun χ hχ => (hcoord χ (hsub hχ).2.2 n).2) χ hχ)
  have hid := eqOn_sourceRealCenteredBalls_of_real_agreement hp
    ⟨φ.val,φ.property⟩ ⟨φ.val,φ.property⟩ r r (A.moment n (2*m+1)) G
    ((A.analytic_moment n (2*m+1)).mono (fun _ h => (hsub h).1)).differentiableOn
    hG.differentiableOn (by
      intro χ hχ
      change A.moment n (2*m+1) χ.val = (2*I/Real.pi:ℂ)*sourceGapCosineMean hp hp1 n _ χ.val
      rw [C.powerCosineMean_eq_boundaryIntegral]
      by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential χ.val) (periodOnePotential_mem χ.val) n = 0
      · rw [A.moment_of_collapsed χ.val (A.realType_subset_domain χ.property) n hgap (2*m+1)]
        simp only [C.gapBoundary_eq_zero_of_collapsed n χ.val hgap,zero_pow (by omega : 2*m+1 ≠ 0),
          mul_zero,intervalIntegral.integral_zero]
      · let R := (C.discs.inner n+C.discs.outer n)/2
        have hi : C.discs.inner n ≤ R := by dsimp [R]; linarith [C.discs.inner_lt n]
        have ho : R < C.discs.outer n := by dsimp [R]; linarith [C.discs.inner_lt n]
        exact (A.real_moment_eq_cauchyCircle C ⟨χ.val,χ.property⟩ (hUC hχ.1) n (2*m+1) R hi ho).trans
          (C.powerCircle_odd_eq_boundaryIntegral n m ⟨χ.val,χ.property⟩ (hUC hχ.1) hgap R hi ho))
  exact (hid ⟨hψ,hψ⟩).trans (C.powerCosineMean_eq_boundaryIntegral n m ψ)

end SourcePrimitivePowerAtlas
end NLS.ZakharovShabat
