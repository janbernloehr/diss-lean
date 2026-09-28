import NLS.ZakharovShabat.SourcePsiGapFactorization
import NLS.ZakharovShabat.SourceNormalizedActionCollapsedReal
import NLS.ZakharovShabat.SourcePsiNearFreeRegularAnalytic

/-!
# Reality of the regular psi quotient on real spectral gaps

For real-type source data and a real critical-root input, the deleted
numerator and omitted-root denominator are both real at every real
spectral point outside the other gaps. Their quotient is real, and
the regular factor in the psi contour equation is purely imaginary.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The single-root quotient has zero imaginary part on the real axis
whenever the remaining periodic gaps are avoided and all displaced
roots are real. -/
theorem sourceSingleRootQuotientJointProduct_im_eq_zero_of_real_roots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (a : Coeff p) (hroots : ∀ k : ℤ, (displacedRoots a k).im = 0)
    (m : ℤ) (x : ℝ)
    (hx : (x:ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    (sourceSingleRootQuotientJointProduct hp hp1 m
      ((x:ℂ),(a,ψ))).im = 0 := by
  have hnum :
      (jointDeletedSingleSpectralProduct m ((x:ℂ),a)).im = 0 :=
    jointDeletedSingleSpectralProduct_im_eq_zero_of_real_roots
      hp hp1 m a x hroots
  have hden :
      (sourceStandardRootOmittedProduct hp hp1 m ψ (x:ℂ)).im = 0 :=
    sourceStandardRootOmittedProduct_im_eq_zero_on_realAxis
      hp hp1 ψ hreal m x hx
  change (jointDeletedSingleSpectralProduct m ((x:ℂ),a) /
    sourceStandardRootOmittedProduct hp hp1 m ψ (x:ℂ)).im = 0
  simp [Complex.div_im,hnum,hden]

/-- The weighted regular factor in equation (2.27) is imaginary on
the real spectral axis when the root input and source are real. -/
theorem sourcePsiGapRegularFactor_weighted_re_eq_zero_of_real_roots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (a : Coeff p) (hroots : ∀ k : ℤ, (displacedRoots a k).im = 0)
    (n m : ℤ) (x : ℝ)
    (hx : (x:ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    ((((n-m : ℤ) : ℂ) *
      sourcePsiGapRegularFactor hp hp1 n m a ψ (x:ℂ))).re = 0 := by
  have hQ := sourceSingleRootQuotientJointProduct_im_eq_zero_of_real_roots
    hp hp1 ψ hreal a hroots m x hx
  have hd : (displacedRoots a n-(x:ℂ)).im = 0 := by
    simp [Complex.sub_im,hroots n]
  unfold sourcePsiGapRegularFactor
  simp [Complex.mul_re,Complex.div_re,hQ,hd]

/-- Removing the explicit imaginary unit from the factorized psi
numerator produces a real value at every real spectral point outside
the other periodic gaps. -/
theorem sourcePsiGapNumerator_rotated_im_eq_zero_of_real_roots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (a : Coeff p) (hroots : ∀ k : ℤ, (displacedRoots a k).im = 0)
    (n m : ℤ) (x : ℝ)
    (hx : (x:ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    ((-I) * (displacedRoots a m-(x:ℂ)) *
      (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m a ψ (x:ℂ))).im = 0 := by
  have hroot : (displacedRoots a m-(x:ℂ)).im = 0 := by
    simp [Complex.sub_im,hroots m]
  have hreg := sourcePsiGapRegularFactor_weighted_re_eq_zero_of_real_roots
    hp hp1 ψ hreal a hroots n m x hx
  have hgRe : ((displacedRoots a m-(x:ℂ)) *
      (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m a ψ (x:ℂ))).re = 0 := by
    rw [Complex.mul_re,hroot,hreg]
    ring
  rw [mul_assoc]
  have hIre : (-I).re = 0 := by simp
  have hIim : (-I).im = -1 := by simp
  rw [Complex.mul_im,hIre,hIim,hgRe]
  ring

/-- The rotated factorized numerator is real on the selected gap
whenever that gap lies in a contour disc avoiding the other gaps. -/
theorem sourcePsiGapNumerator_rotated_im_eq_zero_on_selectedGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (a : Coeff p) (hroots : ∀ k : ℤ, (displacedRoots a k).im = 0)
    (n m : ℤ) (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hdom : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      ((-I) * (displacedRoots a m-z) *
        (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m a ψ z)).im = 0 := by
  intro z hz
  have hzPeriod : z ∈ sourcePeriodicSegment hp hp1 ψ m :=
    sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m hz
  have hzIm : z.im = 0 :=
    sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hreal m z hzPeriod
  have hzReal : (z.re:ℂ) = z := by
    apply Complex.ext
    · rfl
    · simpa using hzIm.symm
  have hzDom : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    hdom (ball_subset_closedBall (hseg hzPeriod))
  have hxDom : (z.re:ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    hzReal ▸ hzDom
  simpa only [hzReal] using
    sourcePsiGapNumerator_rotated_im_eq_zero_of_real_roots
      hp hp1 ψ hreal a hroots n m z.re hxDom

end NLS.ZakharovShabat
