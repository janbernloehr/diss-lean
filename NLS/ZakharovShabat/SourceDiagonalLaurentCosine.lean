import NLS.ZakharovShabat.SourceHigherActionRegularity
import NLS.ZakharovShabat.SourceDiagonalLaurentAtlas
import NLS.ZakharovShabat.SourcePrimitivePowerComplexCosine

/-! # Integer-level Laurent action boundaries on common complex source balls

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

/-- Integer spectral powers preserve analytic symmetric means on zero-excluding discs. -/
theorem laurentActionCosineMean_analytic (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (U : Set (CoeffPair p)) (hU : IsOpen U)
    (hUC : U ⊆ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (k : ℤ)
    (hzero : (0 : ℂ) ∉ closedBall (C.discs.center n) (C.discs.outer n))
    (hτ : AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ n) U)
    (hγ : AnalyticOnNhd ℂ (fun ψ =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) U) :
    AnalyticOnNhd ℂ (sourceGapCosineMean hp hp1 n (fun t => t.1^(k-1)*C.powerNumerator n 0 t.2 t.1)) U := by
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
    (fun t ht => (analyticAt_fst.zpow (by intro hz; exact hzero (hz ▸ ball_subset_closedBall ht.1))).mul (C.powerNumerator_joint_analytic U hUC n 0 hτ hγ t ht))
    ψ (hτ ψ hψ) hhalf
  intro θ _
  refine ⟨C.segment_subset_outer n ψ (hUC hψ) ?_,hψ⟩
  exact sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n (Real.cos θ)
    (Real.neg_one_le_cos θ) (Real.cos_le_one θ)

/-- The weighted analytic mean equals the literal complex boundary integral. -/
theorem laurentActionCosineMean_eq_boundaryIntegral (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (n : ℤ) (k : ℤ) (ψ : CoeffPair p) :
    (2*I/Real.pi:ℂ)*sourceGapCosineMean hp hp1 n (fun t => t.1^(k-1)*C.powerNumerator n 0 t.2 t.1) ψ =
      (2/Real.pi:ℂ)*∫ θ in (0:ℝ)..Real.pi,
        (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))^(k-1) *
        ((sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))*C.gapBoundary n ψ θ true) := by
  unfold sourceGapCosineMean parametricCosineMean
  have he : (∫ θ in (0:ℝ)..Real.pi,
      (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))^(k-1) *
        C.powerNumerator n 0 ψ (sourceStandardRootMidpoint hp hp1 ψ n+
          sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))) =
      -I * ∫ θ in (0:ℝ)..Real.pi,
        (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))^(k-1) *
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

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem zero_not_mem_noncentral_disc_of_diagonal_point
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hdiag : φ.val.fst = φ.val.snd) (n : ℤ) (hn : n ≠ 0) :
    (0 : ℂ) ∉ closedBall (C.discs.center n) (C.discs.outer n) := by
  intro hz
  exact C.discs.avoids_other φ.val hφ n hz 0 hn.symm
    (zero_mem_central_segment_of_diagonal hp hp1 φ hdiag)

end SourceFullAbelianUniformCauchyFamily

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem laurentPrimitiveCircle_eq_boundaryIntegral
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n k : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n)
    (hzero : (0 : ℂ) ∉ closedBall (C.discs.center n) R) :
    sourceLaurentPrimitiveCircle hp hp1 W n k φ.val (C.discs.center n) R =
      (2/Real.pi : ℂ) * ∫ θ in (0 : ℝ)..Real.pi,
        (sourceStandardRootMidpoint hp hp1 φ.val n+sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ))^(k-1) *
        ((sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ))*C.gapBoundary n φ.val θ true) := by
  rw [C.laurentPrimitiveCircle_eq_realIntegral n k φ hφ R hinner houter hzero]
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
  · simp only [hgap,Complex.zero_re,zero_div,zero_mul,Complex.ofReal_zero,
      sourceStandardRootHalfGap,mul_zero,intervalIntegral.integral_zero]
  have he : (∫ θ in (0 : ℝ)..Real.pi,
      (sourceStandardRootMidpoint hp hp1 φ.val n+sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ))^(k-1) *
      ((sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ))*C.gapBoundary n φ.val θ true)) =
      sourceStandardRootHalfGap hp hp1 φ.val n *
        ∫ θ in (0 : ℝ)..Real.pi, (((realGapAffinePoint hp hp1 φ.val n (Real.cos θ))^(k-1) *
          (Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le Real.pi_pos.le] at hθ
    dsimp only
    rw [C.gapBoundary_eq_realCosineProfile n φ hφ hgap θ hθ]
    have hx := sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint hp hp1 φ.val φ.property n (Real.cos θ)
    change sourceStandardRootMidpoint hp hp1 φ.val n+sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ) = _ at hx
    rw [hx]
    simp only [ofReal_mul,ofReal_zpow]
    ring
  rw [he,intervalIntegral.integral_ofReal,sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 φ.val φ.property n]
  simp only [ofReal_mul,ofReal_div,ofReal_sub,ofReal_ofNat,canonicalPeriodicGap,sub_re]
  ring

end SourceFullAbelianUniformCauchyFamily

namespace SourceDiagonalLaurentAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem exists_ball_all_laurent_actions_eq_boundaryIntegral
    (A : SourceDiagonalLaurentAtlas hp hp1)
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (φ : realDiagonalSourceLocus p)
    (hφC : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) :
    ∃ r : ℝ, 0 < r ∧ ball φ.val r ⊆ A.domain ∩ ball C.discs.source.val C.discs.sourceRadius ∧
      ∀ ψ ∈ ball φ.val r, ∀ n : ℤ, n ≠ 0 → ∀ k : ℤ, A.action n k ψ =
        (2/Real.pi:ℂ)*∫ θ in (0:ℝ)..Real.pi,
          (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))^(k-1) *
          ((sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))*C.gapBoundary n ψ θ true) := by
  obtain ⟨M,hM,_,hrealM,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp
    ((A.isOpen_domain.inter (isOpen_ball.inter hM)).mem_nhds
      ⟨A.realDiagonal_subset_domain φ.property,hφC,hrealM φ.property.1⟩)
  let U := ball φ.val r
  have hUC : U ⊆ ball C.discs.source.val C.discs.sourceRadius := fun _ h => (hsub h).2.1
  refine ⟨r,hr,fun ψ hψ => ⟨(hsub hψ).1,hUC hψ⟩,?_⟩
  intro ψ hψ n hn k
  have hzero := C.zero_not_mem_noncentral_disc_of_diagonal_point ⟨φ.val,φ.property.1⟩ hφC φ.property.2 n hn
  let G : CoeffPair p → ℂ := fun χ =>
    (2*I/Real.pi:ℂ)*sourceGapCosineMean hp hp1 n (fun t => t.1^(k-1)*C.powerNumerator n 0 t.2 t.1) χ
  have hG : AnalyticOnNhd ℂ G U := fun χ hχ => analyticAt_const.mul
    (C.laurentActionCosineMean_analytic U isOpen_ball hUC n k hzero
      (fun χ hχ => (hcoord χ (hsub hχ).2.2 n).1)
      (fun χ hχ => (hcoord χ (hsub hχ).2.2 n).2) χ hχ)
  have hid := eqOn_sourceRealCenteredBalls_of_real_agreement hp
    ⟨φ.val,φ.property.1⟩ ⟨φ.val,φ.property.1⟩ r r (A.action n k) G
    ((A.analytic_action n k hn).mono (fun _ h => (hsub h).1)).differentiableOn hG.differentiableOn (by
      intro χ hχ
      change A.action n k χ.val = (2*I/Real.pi:ℂ)*sourceGapCosineMean hp hp1 n _ χ.val
      rw [C.laurentActionCosineMean_eq_boundaryIntegral]
      let R := (C.discs.inner n+C.discs.outer n)/2
      have hi : C.discs.inner n ≤ R := by dsimp [R]; linarith [C.discs.inner_lt n]
      have ho : R < C.discs.outer n := by dsimp [R]; linarith [C.discs.inner_lt n]
      have hz : (0 : ℂ) ∉ closedBall (C.discs.center n) R :=
        fun h => hzero (closedBall_subset_closedBall ho.le h)
      rw [A.action_eq_real ⟨χ.val,χ.property⟩ (hsub hχ.1).1 n k hn]
      calc
        _ = sourceLaurentPrimitiveCircle hp hp1 W n k χ.val (C.discs.center n) R := by
          exact (C.laurentPrimitiveCircle_eq_realIntegral n k ⟨χ.val,χ.property⟩ (hUC hχ.1) R hi ho hz).symm
        _ = _ := C.laurentPrimitiveCircle_eq_boundaryIntegral n k ⟨χ.val,χ.property⟩ (hUC hχ.1) R hi ho hz)
  exact (hid ⟨hψ,hψ⟩).trans (C.laurentActionCosineMean_eq_boundaryIntegral n k ψ)

end SourceDiagonalLaurentAtlas

end NLS.ZakharovShabat
