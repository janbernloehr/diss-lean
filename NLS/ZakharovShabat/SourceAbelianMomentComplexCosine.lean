import NLS.ZakharovShabat.SourceAbelianMomentRealCosine
import NLS.ZakharovShabat.SourceFullAbelianSquareJointAnalytic
import NLS.ZakharovShabat.SourceHolomorphicRealGerm

/-! # Complex-source cosine formulas for positive even moments

Joint regularity is supplied locally from the canonical Cauchy family.
The real-form identity theorem then extends the exact cosine formula
through both open and closed real gaps to nearby complex sources.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual even-moment cosine mean is analytic at each real source
of the normalized psi extension. All needed spectral regularity is
constructed, rather than required as additional hypotheses. -/
theorem SourcePsiNormalizedComplexExtension.analyticAt_evenMomentCosineMean_of_mem
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s)
    (A : SourceAbelianMomentAtlas hp hp1 W s) (hV : IsOpen V)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ V) (n k : ℤ) (m : ℕ) :
    AnalyticAt ℂ (sourceGapCosineMean hp hp1 k (fun t : ℂ × CoeffPair p =>
      sourceAbelianMomentEvenNumerator hp hp1 W n k m (s n t.2 : Coeff p) t.2 t.1)) φ.val := by
  obtain ⟨W',_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hC⟩ := hfamilies φ
  have hφC : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨O,hO,_,hrealO,hproduct⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  obtain ⟨M,hM,_,hrealM,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨_,R,_,hR,_,hrealR,_,hrootR,_,_⟩ := exists_sourceFullAbelian_almostReal_jointAnalytic hp hp1
  let U := ball C.discs.source.val C.discs.sourceRadius ∩ (V ∩ (O ∩ (M ∩ R)))
  have hU : IsOpen U := isOpen_ball.inter (hV.inter (hO.inter (hM.inter hR)))
  have hφU : φ.val ∈ U := ⟨hφC,hφ,hrealO φ.property,hrealM φ.property,hrealR φ.property⟩
  have hroot : IsOpen (sourceCanonicalRootJointDomain hp hp1 U) := by
    have he : sourceCanonicalRootJointDomain hp hp1 U =
        sourceCanonicalRootJointDomain hp hp1 R ∩ (Prod.snd ⁻¹' U) := by
      ext t
      exact ⟨fun ht => ⟨⟨ht.1.2.2.2.2,ht.2⟩,ht.1⟩,fun ht => ⟨ht.2,ht.1.2⟩⟩
    rw [he]
    exact hrootR.inter (hU.preimage continuous_snd)
  have hD : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 U k) := by
    have he : sourceStandardRootOmittedJointDomain hp hp1 U k =
        sourceStandardRootOmittedJointDomain hp hp1 O k ∩ (Prod.snd ⁻¹' U) := by
      ext t
      exact ⟨fun ht => ⟨⟨ht.1.2.2.1,ht.2⟩,ht.1⟩,fun ht => ⟨ht.2,ht.1.2⟩⟩
    rw [he]
    exact (hproduct k).1.inter (hU.preimage continuous_snd)
  have hS := C.fullSquare_joint_analytic U hU (fun _ h => h.1) hroot k
    (fun ψ hψ => (hcoord ψ hψ.2.2.2.1 k).1)
    (fun ψ hψ => (hcoord ψ hψ.2.2.2.1 k).2)
  have hP := (hproduct k).2.1.mono
    (show sourceStandardRootOmittedJointDomain hp hp1 U k ⊆
      sourceStandardRootOmittedJointDomain hp hp1 O k from fun _ h => ⟨h.1.2.2.1,h.2⟩)
  let φ₀ : realTypeSourceLocus p := ⟨φ.val,φ.property⟩
  have hφA : φ.val ∈ A.sourceBall φ₀ := mem_ball_self (A.localChart φ₀).radius_pos
  have hfamily := (A.localChart φ₀).family φ.val hφA
  have hg := hs.evenNumerator_joint_analytic W' U (fun _ h => h.2.1) n k m hP hS
  have hmean := analyticAt_sourceGapCosineMean_of_realCenteredCircle hp hp1 k _ U hD hg φ hφU
    ((A.localChart φ₀).center k) ((A.localChart φ₀).contourRadius k)
    (hfamily.1 k) (hfamily.2 k).2.1 (hfamily.2 k).2.2.1
  apply hmean.congr
  filter_upwards [hU.mem_nhds hφU,isOpen_ball.mem_nhds hφA] with ψ hψU hψA
  obtain ⟨D⟩ := (A.localChart φ₀).charts ψ hψA
  obtain ⟨E⟩ := C.charts ψ hψU.1
  unfold sourceGapCosineMean parametricCosineMean
  apply intervalIntegral.integral_congr
  intro θ _
  unfold sourceAbelianMomentEvenNumerator
  dsimp only
  rw [sourceFullAbelianSquare_independent_neighborhood E D]

namespace SourceAbelianMomentAtlas

/-- Every positive even moment equals its actual cosine integral on a
complex neighborhood of each real source, including closed selected gaps.
The neighborhood here may depend on the two indices and the order. -/
theorem eventually_positive_even_moment_eq_cosineMean
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s) (hV : IsOpen V)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ V) (n k : ℤ) (m : ℕ) :
    A.moment n k (2*(m+1)) =ᶠ[𝓝 φ.val] fun ψ => -(2*Complex.I) *
      sourceGapCosineMean hp hp1 k (fun t : ℂ × CoeffPair p =>
        sourceAbelianMomentEvenNumerator hp hp1 W n k (m+1) (s n t.2 : Coeff p) t.2 t.1) ψ := by
  exact eventuallyEq_source_of_analyticAt_of_real_agreement hp ⟨φ.val,φ.property⟩ _ _
    (A.analytic_moment n k (2*(m+1)) φ.val (A.realType_subset_domain φ.property))
    (analyticAt_const.mul (hs.analyticAt_evenMomentCosineMean_of_mem A hV φ hφ n k (m+1)))
    (fun χ => A.real_positive_even_moment_eq_cosineMean ⟨χ.val,χ.property⟩ n k m)

/-- A positive source radius makes the second-moment identity directly
usable for complex gap estimates, with no analytic endpoint selection. -/
theorem exists_ball_second_moment_eq_cosineMean
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s) (hV : IsOpen V)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ V) (n k : ℤ) :
    ∃ r : ℝ, 0 < r ∧ ball φ.val r ⊆ A.domain ∩ V ∧ ∀ ψ ∈ ball φ.val r,
      A.moment n k 2 ψ = -(2*Complex.I) *
        sourceGapCosineMean hp hp1 k (fun t : ℂ × CoeffPair p =>
          sourceAbelianMomentEvenNumerator hp hp1 W n k 1 (s n t.2 : Coeff p) t.2 t.1) ψ := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((A.eventually_positive_even_moment_eq_cosineMean hs hV φ hφ n k 0).and
      ((A.isOpen_domain.inter hV).mem_nhds ⟨A.realType_subset_domain φ.property,hφ⟩))
  exact ⟨r,hr,fun _ h => (hball h).2,fun _ h => (hball h).1⟩

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
