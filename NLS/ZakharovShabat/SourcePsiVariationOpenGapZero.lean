import NLS.ZakharovShabat.SourceEntireGapContourZeros
import NLS.ZakharovShabat.SourcePsiSelectedJacobianKernelContour
import NLS.ZakharovShabat.SourcePsiCandidateVariationRealAxis
import NLS.ZakharovShabat.SourceStandardRootWeightedLocalRealMeanValue
import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic
import NLS.ZakharovShabat.SourceNormalizedActionCollapsedReal
import NLS.ZakharovShabat.SourceCanonicalRootProduct

/-!
# A zero of the psi variation in an open real gap

For real root data and a real direction, a zero variation contour
integral forces the entire numerator variation to vanish somewhere in
the enclosed open gap. This is the mean-value step of Lemma 12.7.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Vanishing of the variation contour integral yields a zero of the
entire numerator variation on the selected open real gap. -/
theorem exists_sourcePsiCandidateVariation_zero_on_openGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (a h : Coeff p)
    (hroots : ∀ j : ℤ, (displacedRoots a j).im = 0)
    (hreal : ∀ j : ℤ, (h j).im = 0)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (∮ z in C((x:ℂ),R),
      sourcePsiCandidateVariation n a h z /
        sourceCanonicalRoot hp hp1 ψ z) = 0) :
    ∃ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      sourcePsiCandidateVariation n a h μ = 0 := by
  exact exists_sourceEntireNumerator_zero_on_openGap hp hp1 ψ hψ m
    (sourcePsiCandidateVariation n a h)
    (analyticOnNhd_sourcePsiCandidateVariation hp hp1 n a h)
    (fun y => sourcePsiCandidateVariation_im_eq_zero_of_real_data
      hp hp1 n a h hroots hreal y)
    hopen x R hR hseg hdom hcircle hzero

/-- A real direction in the selected Jacobian kernel gives a zero of
its entire numerator variation in each retained open real gap. -/
theorem exists_sourcePsiSelectedJacobian_kernel_variation_zero_on_openGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0)
    (m : ℤ) (hmn : m ≠ n)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
    (x : ℝ) (hcenter : c m = (x:ℂ)) (hR : 0 < R m)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) (R m))
    (hdom : closedBall (x:ℂ) (R m) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (c m) (R m) ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (h : DeletedCoeff p n)
    (hreal : ∀ j : ℤ, ((h : Coeff p) j).im = 0)
    (hkernel : sourcePsiSelectedRootJacobian hp hp1 n c R a ψ h = 0) :
    ∃ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      sourcePsiCandidateVariation n (a : Coeff p)
        (h : Coeff p) μ = 0 := by
  have hzero := sourcePsiSelectedRootJacobian_kernel_variation_contour_zero
    hp hp1 n c R U hUopen hcoord hdiff a ψ hpair hψ
      m hmn hR.le hcircle h hkernel
  rw [hcenter] at hzero
  have hcircle' : sphere (x:ℂ) (R m) ⊆
      sourceCanonicalRootDomain hp hp1 ψ := by
    simpa only [hcenter] using hcircle
  exact exists_sourcePsiCandidateVariation_zero_on_openGap
    hp hp1 ψ hψ n m (a : Coeff p) (h : Coeff p)
      hroots hreal hopen x (R m) hR hseg hdom hcircle' hzero

end NLS.ZakharovShabat
