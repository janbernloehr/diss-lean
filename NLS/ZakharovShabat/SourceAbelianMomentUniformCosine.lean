import NLS.ZakharovShabat.SourceGapCosineMeanDomain
import NLS.ZakharovShabat.SourceAbelianMomentComplexCosine

/-! # One source ball for every cosine moment formula

The canonical all-gap Cauchy family supplies one regular source domain.
The segment-local analyticity theorem works there for every index and
numerator, so real-form continuation requires no index-dependent shrink.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- One positive source radius works simultaneously for every pair of
indices and every positive even order, including all collapsed gaps. -/
theorem exists_ball_all_even_moments_eq_cosineMean
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s) (hV : IsOpen V)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ V) :
    ∃ r : ℝ, 0 < r ∧ ball φ.val r ⊆ A.domain ∩ V ∧
      ∀ (n k : ℤ) (m : ℕ), ∀ ψ ∈ ball φ.val r,
        A.moment n k (2*(m+1)) ψ = -(2*Complex.I) *
          sourceGapCosineMean hp hp1 k (fun t : ℂ × CoeffPair p =>
            sourceAbelianMomentEvenNumerator hp hp1 W n k (m+1) (s n t.2 : Coeff p) t.2 t.1) ψ := by
  obtain ⟨W',_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hC⟩ := hfamilies φ
  have hφC : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨O,hO,_,hrealO,hproduct⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  obtain ⟨M,hM,_,hrealM,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨_,R,_,hR,_,hrealR,_,hrootR,_,_⟩ := exists_sourceFullAbelian_almostReal_jointAnalytic hp hp1
  let φ₀ : realTypeSourceLocus p := ⟨φ.val,φ.property⟩
  let U := ball C.discs.source.val C.discs.sourceRadius ∩ (V ∩ (O ∩ (M ∩ R)))
  have hU : IsOpen U := isOpen_ball.inter (hV.inter (hO.inter (hM.inter hR)))
  have hφU : φ.val ∈ U := ⟨hφC,hφ,hrealO φ.property,hrealM φ.property,hrealR φ.property⟩
  have hφA : φ.val ∈ A.sourceBall φ₀ := mem_ball_self (A.localChart φ₀).radius_pos
  have hnear : U ∩ A.sourceBall φ₀ ∈ 𝓝 φ.val :=
    (hU.inter isOpen_ball).mem_nhds ⟨hφU,hφA⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hAdomain : A.sourceBall φ₀ ⊆ A.domain := subset_iUnion A.sourceBall φ₀
  have hroot : IsOpen (sourceCanonicalRootJointDomain hp hp1 U) := by
    have he : sourceCanonicalRootJointDomain hp hp1 U =
        sourceCanonicalRootJointDomain hp hp1 R ∩ (Prod.snd ⁻¹' U) := by
      ext t
      exact ⟨fun ht => ⟨⟨ht.1.2.2.2.2,ht.2⟩,ht.1⟩,fun ht => ⟨ht.2,ht.1.2⟩⟩
    rw [he]
    exact hrootR.inter (hU.preimage continuous_snd)
  have hD (k : ℤ) : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 U k) := by
    have he : sourceStandardRootOmittedJointDomain hp hp1 U k =
        sourceStandardRootOmittedJointDomain hp hp1 O k ∩ (Prod.snd ⁻¹' U) := by
      ext t
      exact ⟨fun ht => ⟨⟨ht.1.2.2.1,ht.2⟩,ht.1⟩,fun ht => ⟨ht.2,ht.1.2⟩⟩
    rw [he]
    exact (hproduct k).1.inter (hU.preimage continuous_snd)
  have hτ (k : ℤ) : AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ k) U :=
    fun ψ hψ => (hcoord ψ hψ.2.2.2.1 k).1
  have hγ (k : ℤ) : AnalyticOnNhd ℂ (fun ψ =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2) U :=
    fun ψ hψ => (hcoord ψ hψ.2.2.2.1 k).2
  have hsegment (k : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ U) :
      sourcePeriodicSegment hp hp1 ψ k ⊆ sourceStandardRootOmittedDomain hp hp1 ψ k :=
    fun z hz => C.discs.avoids_other ψ hψ.1 k
      (ball_subset_closedBall (C.segment_subset_outer k ψ hψ.1 hz))
  refine ⟨r,hr,fun ψ hψ => ⟨hAdomain (hball hψ).2,(hball hψ).1.2.1⟩,?_⟩
  intro n k m
  let g : ℂ × CoeffPair p → ℂ := fun t =>
    sourceAbelianMomentEvenNumerator hp hp1 W' n k (m+1) (s n t.2 : Coeff p) t.2 t.1
  have hP := (hproduct k).2.1.mono
    (show sourceStandardRootOmittedJointDomain hp hp1 U k ⊆
      sourceStandardRootOmittedJointDomain hp hp1 O k from fun _ h => ⟨h.1.2.2.1,h.2⟩)
  have hS := C.fullSquare_joint_analytic U hU (fun _ h => h.1) hroot k (hτ k) (hγ k)
  have hg : AnalyticOnNhd ℂ g (sourceStandardRootOmittedJointDomain hp hp1 U k) :=
    hs.evenNumerator_joint_analytic W' U (fun _ h => h.2.1) n k (m+1) hP hS
  have hmean := analyticOnNhd_sourceGapCosineMean_of_segment hp hp1 k U g (hD k) hg (hτ k) (hγ k) (hsegment k)
  let G : CoeffPair p → ℂ := fun ψ => -(2*Complex.I) * sourceGapCosineMean hp hp1 k g ψ
  have hG : AnalyticOnNhd ℂ G (ball φ.val r) := fun ψ hψ =>
    analyticAt_const.mul (hmean ψ (hball hψ).1)
  have heq (ψ : CoeffPair p) (hψ : ψ ∈ ball φ.val r) : G ψ = -(2*Complex.I) *
      sourceGapCosineMean hp hp1 k (fun t : ℂ × CoeffPair p =>
        sourceAbelianMomentEvenNumerator hp hp1 W n k (m+1) (s n t.2 : Coeff p) t.2 t.1) ψ := by
    obtain ⟨D⟩ := (A.localChart φ₀).charts ψ (hball hψ).2
    obtain ⟨E⟩ := C.charts ψ (hball hψ).1.1
    unfold G sourceGapCosineMean parametricCosineMean
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only [g,sourceAbelianMomentEvenNumerator]
    rw [sourceFullAbelianSquare_independent_neighborhood E D]
  have hid := eqOn_sourceRealCenteredBalls_of_real_agreement hp φ₀ φ₀ r r
    (A.moment n k (2*(m+1))) G
    ((A.analytic_moment n k (2*(m+1))).mono (fun _ h => hAdomain (hball h).2)).differentiableOn
    hG.differentiableOn (by
      intro χ hχ
      rw [heq χ.val hχ.1]
      exact A.real_positive_even_moment_eq_cosineMean ⟨χ.val,χ.property⟩ n k m)
  intro ψ hψ
  exact (hid ⟨hψ,hψ⟩).trans (heq ψ hψ)

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
