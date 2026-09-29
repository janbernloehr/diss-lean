import NLS.ZakharovShabat.SourceEntireGapContourZeros
import NLS.ZakharovShabat.SourcePsiSelectedJacobianKernelContour
import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic
import NLS.ZakharovShabat.SourceCanonicalRootProduct
import NLS.ZakharovShabat.SourcePsiNearFreeCollapsedGap

/-!
# A zero of the psi variation at a collapsed gap

At a collapsed periodic gap, the standard root is linear. Cauchy's
formula converts the zero variation contour integral into vanishing
of the entire numerator variation at the gap midpoint. This part of
the gap-zero argument does not require a real root direction.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Vanishing of the variation contour integral at a collapsed gap
forces the entire numerator variation to vanish at its midpoint. -/
theorem sourcePsiCandidateVariation_zero_at_collapsedGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (a h : Coeff p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (c₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball c₀ R)
    (hdom : closedBall c₀ R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere c₀ R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (∮ z in C(c₀,R),
      sourcePsiCandidateVariation n a h z /
        sourceCanonicalRoot hp hp1 ψ z) = 0) :
    sourcePsiCandidateVariation n a h
      (sourceStandardRootMidpoint hp hp1 ψ m) = 0 := by
  exact sourceEntireNumerator_zero_at_collapsedGap hp hp1 ψ hψ m
    (sourcePsiCandidateVariation n a h)
    (analyticOnNhd_sourcePsiCandidateVariation hp hp1 n a h)
    hgap c₀ R hR hmid hdom hcircle hzero

/-- A selected Jacobian kernel direction, including a complex one,
gives a zero of the entire variation at each collapsed gap midpoint. -/
theorem sourcePsiSelectedJacobian_kernel_variation_zero_at_collapsedGap
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
    (m : ℤ) (hmn : m ≠ n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (hR : 0 < R m)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball (c m) (R m))
    (hdom : closedBall (c m) (R m) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (c m) (R m) ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (h : DeletedCoeff p n)
    (hkernel : sourcePsiSelectedRootJacobian hp hp1 n c R a ψ h = 0) :
    sourcePsiCandidateVariation n (a : Coeff p) (h : Coeff p)
      (sourceStandardRootMidpoint hp hp1 ψ m) = 0 := by
  have hzero := sourcePsiSelectedRootJacobian_kernel_variation_contour_zero
    hp hp1 n c R U hUopen hcoord hdiff a ψ hpair hψ
      m hmn hR.le hcircle h hkernel
  exact sourcePsiCandidateVariation_zero_at_collapsedGap
    hp hp1 ψ hψ n m (a : Coeff p) (h : Coeff p)
      hgap (c m) (R m) hR hmid hdom hcircle hzero

end NLS.ZakharovShabat
