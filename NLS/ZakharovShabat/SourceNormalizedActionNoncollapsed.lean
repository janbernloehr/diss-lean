import NLS.ZakharovShabat.SourceComplexActionGradient
import NLS.ZakharovShabat.SourceComplexActionProperties
import NLS.ZakharovShabat.SourceSymmetricContour
import NLS.ComplexAnalysis.QuotientDerivative

/-!
# The normalized action away from collapsed gaps

The quotient `Iₙ / γₙ²` is initially defined where the selected
periodic gap is nonzero. At every real-type source in this locus,
the squared gap is analytic, so the quotient is complex Fréchet
differentiable and analytic along complex source lines. Extending
through a collapsed gap is a separate part of Theorem 11.2.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]


/-- The a priori quotient of the indexed complex action by the
squared periodic gap. Its analytic extension at collapsed gaps has
not yet been defined. -/
def sourceRawNormalizedAction
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) : ℂ :=
  sourceComplexAction hp hp1 n ψ /
    (sourcePeriodicGapDisplacement hp hp1 ψ n)^2

/-- The indexed squared periodic gap is analytic at every real-type
source. -/
theorem analyticAt_sourcePeriodicGapDisplacement_sq_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticAt ℂ (fun ψ : CoeffPair p =>
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2) φ := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hq := (hdata φ (hreal hφ) n).2
  exact hq.congr (Filter.Eventually.of_forall fun ψ => by
    simp only [sourcePeriodicGapDisplacement_apply])

/-- On a noncollapsed gap, the raw normalized action has a complex
Fréchet derivative at the real-type source. -/
theorem differentiableAt_sourceRawNormalizedAction_of_gap_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n ≠ 0) :
    DifferentiableAt ℂ (sourceRawNormalizedAction hp hp1 n) φ := by
  have hdom : φ ∈ sourceComplexActionDomain hp hp1 n :=
    realTypeSourceLocus_subset_sourceComplexActionDomain hp hp1 n hφ
  have hI : DifferentiableAt ℂ (sourceComplexAction hp hp1 n) φ :=
    (sourceComplexAction_differentiableOn hp hp1 n φ hdom).differentiableAt
      ((isOpen_sourceComplexActionDomain hp hp1 n).mem_nhds hdom)
  have hq := analyticAt_sourcePeriodicGapDisplacement_sq_realType hp hp1 n φ hφ
  have hqne : (sourcePeriodicGapDisplacement hp hp1 φ n)^2 ≠ 0 :=
    pow_ne_zero 2 hgap
  have hmul := hI.mul (hq.differentiableAt.inv hqne)
  have heq : (sourceRawNormalizedAction hp hp1 n) =
      (sourceComplexAction hp hp1 n) *
        (fun ψ : CoeffPair p =>
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2)⁻¹ := by
    funext ψ
    simp [sourceRawNormalizedAction, div_eq_mul_inv]
  rw [heq]
  exact hmul

/-- The noncollapsed normalized action is analytic along every
complex affine source line through a real-type source. -/
theorem sourceRawNormalizedAction_analyticAlongLine_of_gap_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n ≠ 0)
    (h : CoeffPair p) :
    AnalyticAt ℂ (fun t : ℂ =>
      sourceRawNormalizedAction hp hp1 n (φ+t•h)) 0 := by
  have hdom : φ ∈ sourceComplexActionDomain hp hp1 n :=
    realTypeSourceLocus_subset_sourceComplexActionDomain hp hp1 n hφ
  have hI := sourceComplexAction_analyticAlongLine_at hp hp1 n φ hdom h
  have hq := analyticAt_sourcePeriodicGapDisplacement_sq_realType hp hp1 n φ hφ
  have hline : AnalyticAt ℂ (fun t : ℂ => φ+t•h) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hq' : AnalyticAt ℂ (fun ψ : CoeffPair p =>
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2) (φ + (0:ℂ) • h) := by
    simpa using hq
  have hqline : AnalyticAt ℂ (fun t : ℂ =>
      (sourcePeriodicGapDisplacement hp hp1 (φ+t•h) n)^2) 0 := by
    exact hq'.comp (f := fun t : ℂ => φ+t•h) hline
  have hqne : (sourcePeriodicGapDisplacement hp hp1 φ n)^2 ≠ 0 :=
    pow_ne_zero 2 hgap
  have hquot := hI.div hqline (by simpa using hqne)
  have heq : (fun t : ℂ => sourceRawNormalizedAction hp hp1 n (φ+t•h)) =
      (fun t : ℂ => sourceComplexAction hp hp1 n (φ+t•h)) /
        (fun t : ℂ => (sourcePeriodicGapDisplacement hp hp1 (φ+t•h) n)^2) := by
    funext t
    simp [sourceRawNormalizedAction]
  rw [heq]
  exact hquot

/-- On the noncollapsed locus, one isolating circle gives the
directional derivative of the raw normalized action by the quotient
rule and the indexed-action contour gradient. -/
theorem exists_sourceRawNormalizedAction_gradient_circle_of_gap_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n ≠ 0) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      sourcePeriodicSegment hp hp1 φ n ⊆ ball c R ∧
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 φ n ∧
      ∀ h : CoeffPair p,
        (fderiv ℂ (sourceRawNormalizedAction hp hp1 n) φ) h =
          ((-(Real.pi : ℂ)⁻¹ *
              (∮ z in C(c,R),
                (fderiv ℂ (fun ψ : CoeffPair p =>
                  canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
                  sourceCanonicalRoot hp hp1 φ z)) *
              (sourcePeriodicGapDisplacement hp hp1 φ n)^2 -
            sourceComplexAction hp hp1 n φ *
              (fderiv ℂ (fun ψ : CoeffPair p =>
                (sourcePeriodicGapDisplacement hp hp1 ψ n)^2) φ) h) /
            ((sourcePeriodicGapDisplacement hp hp1 φ n)^2)^2 := by
  obtain ⟨c,R,hR,hseg,hother,hgradient⟩ :=
    exists_sourceComplexAction_gradient_circle hp hp1 n φ hφ
  refine ⟨c,R,hR,hseg,hother,?_⟩
  have hdom : φ ∈ sourceComplexActionDomain hp hp1 n :=
    realTypeSourceLocus_subset_sourceComplexActionDomain hp hp1 n hφ
  have hI : DifferentiableAt ℂ (sourceComplexAction hp hp1 n) φ :=
    (sourceComplexAction_differentiableOn hp hp1 n φ hdom).differentiableAt
      ((isOpen_sourceComplexActionDomain hp hp1 n).mem_nhds hdom)
  have hq : DifferentiableAt ℂ
      (fun ψ : CoeffPair p =>
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2) φ :=
    (analyticAt_sourcePeriodicGapDisplacement_sq_realType hp hp1 n φ hφ).differentiableAt
  have hqne : (sourcePeriodicGapDisplacement hp hp1 φ n)^2 ≠ 0 :=
    pow_ne_zero 2 hgap
  intro h
  change (fderiv ℂ (fun ψ : CoeffPair p =>
      sourceComplexAction hp hp1 n ψ /
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2) φ) h = _
  rw [NLS.ComplexAnalysis.fderiv_div_apply
    (sourceComplexAction hp hp1 n)
    (fun ψ : CoeffPair p =>
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2)
    φ hI hq hqne h]
  rw [hgradient h]

end NLS.ZakharovShabat
