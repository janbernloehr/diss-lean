import NLS.ZakharovShabat.SourcePsiIsolatingComplexNormalization

/-!
# Actual retained contour zeros on each assigned circle near a real source

Shrink a source ball to the joint analytic contour domain. The real
normalization identity then gives zero retained periods on its fixed
assigned boundaries for every omitted index. Nested enclosing circles
inside those assigned discs inherit the actual contour zero.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourcePsiIsolatingComplexRootAtlas.exists_local_assigned_contour_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}
    (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U) (φ : realTypeSourceLocus p) :
    ∃ r : ℝ, 0 < r ∧ r ≤ (A.localBranch φ).sourceRadius ∧
      ∀ ψ ∈ ball φ.val r, ∀ n m : ℤ, m ≠ n →
        sourcePsiContour hp hp1 n (A.toSourcePsiComplexRootAtlas.branch n ψ : Coeff p) ψ
          (sourceIsolatingCenter hp hp1 φ.val (A.cutoff φ) m)
          (sourceIsolatingRadius hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) m) = 0 := by
  obtain ⟨V,hV,_,hreal,hdata⟩ := exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  obtain ⟨η,hη,hballV⟩ := Metric.isOpen_iff.mp hV φ.val (hreal φ.property)
  let B := A.toSourcePsiComplexRootAtlas
  let r := min η (B.localBranch φ).sourceRadius
  have hr : 0 < r := lt_min hη (B.localBranch φ).sourceRadius_pos
  have hBall : ball φ.val r ⊆ B.sourceBall φ := ball_subset_ball (min_le_right _ _)
  have hgap ψ (hψ : ψ ∈ ball φ.val r) k : sourcePeriodicSegment hp hp1 ψ k ⊆
      sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) k :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val ψ (A.cutoff φ) (A.enlargement φ) k
      (A.clusters φ ψ (hBall hψ) k)
  refine ⟨r,hr,min_le_right _ _,?_⟩
  intro ψ hψ n m hmn
  have heq := sourcePsi_orthogonality_on_isolating_ball hp hp1 φ r
    (A.cutoff φ) (A.enlargement φ) (A.enlargement_pos φ) n (B.branch n)
    ((B.analytic n).mono (hBall.trans (subset_iUnion B.sourceBall φ)))
    (fun χ _ => B.eq_sourcePsiGapRoot_of_real n χ) hgap (A.disjoint φ)
    V ((ball_subset_ball (min_le_left _ _)).trans hballV) (hdata n).1 (hdata n).2 m hψ
  simpa only [if_neg hmn] using heq

end NLS.ZakharovShabat
