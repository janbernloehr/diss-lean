import NLS.ZakharovShabat.SourcePsiSelectedJacobianKernelRealImag
import NLS.ZakharovShabat.SourcePsiVariationOpenGapZero

/-!
# Open-gap zeros for a complex psi-Jacobian kernel direction

The selected Jacobian has real matrix entries at real data. Split a
complex kernel direction into real and imaginary deleted sequences,
apply the real open-gap mean-value theorem to each, and obtain a zero
for each corresponding entire numerator variation. The two zeros need
not be at the same point; interpolation is applied to each variation
separately in Lemma 12.7.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_sourcePsiSelectedJacobian_complexKernel_variation_zeros_on_openGap
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
    (hrealSeq : ∀ t ∈ U,
      IsRealType (CoeffPair.toMax p t.2) →
      (∀ j : ℤ, (displacedRoots (t.1 : Coeff p) j).im = 0) →
        ∀ m : ℤ,
          ((sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 :
            Coeff p) m).im = 0)
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
    (hkernel : sourcePsiSelectedRootJacobian hp hp1 n c R a ψ h = 0) :
    (∃ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      sourcePsiCandidateVariation n (a : Coeff p)
        (DeletedCoeff.realPart h : Coeff p) μ = 0) ∧
    (∃ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      sourcePsiCandidateVariation n (a : Coeff p)
        (DeletedCoeff.imagPart h : Coeff p) μ = 0) := by
  obtain ⟨hre,him⟩ := sourcePsiSelectedRootJacobian_kernel_realImag
    hp hp1 n c R U hUopen hdiff hrealSeq a ψ hpair hψ hroots
      h hkernel
  constructor
  · exact exists_sourcePsiSelectedJacobian_kernel_variation_zero_on_openGap
      hp hp1 n c R U hUopen hcoord hdiff a ψ hpair hψ hroots
        m hmn hopen x hcenter hR hseg hdom hcircle
        (DeletedCoeff.realPart h)
        (DeletedCoeff.realPart_im_eq_zero h) hre
  · exact exists_sourcePsiSelectedJacobian_kernel_variation_zero_on_openGap
      hp hp1 n c R U hUopen hcoord hdiff a ψ hpair hψ hroots
        m hmn hopen x hcenter hR hseg hdom hcircle
        (DeletedCoeff.imagPart h)
        (DeletedCoeff.imagPart_im_eq_zero h) him

end NLS.ZakharovShabat
