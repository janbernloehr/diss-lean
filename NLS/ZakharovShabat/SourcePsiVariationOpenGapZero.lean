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
  let Φ : ℂ → ℂ := sourcePsiCandidateVariation n a h
  let P : ℂ → ℂ := sourceStandardRootOmittedProduct hp hp1 m ψ
  let g : ℂ → ℂ := fun z => Φ z / P z
  obtain ⟨W,_,_,hrealW,hdata⟩ :=
    exists_global_source_analytic_omittedJointProduct hp hp1
  have hψW : ψ ∈ W := hrealW hψ
  have hPanalytic : AnalyticOnNhd ℂ P
      (sourceStandardRootOmittedDomain hp hp1 ψ m) :=
    sourceStandardRootOmittedProduct_analyticOnNhd_spectral
      hp hp1 m W (hdata m).2.1 ψ hψW
  have hg : AnalyticOnNhd ℂ g (closedBall (x:ℂ) R) := by
    intro z hz
    exact ((analyticOnNhd_sourcePsiCandidateVariation hp hp1 n a h)
      z (mem_univ _)).div (hPanalytic z (hdom hz))
        (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m (hdom hz))
  have hgap : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m) ⊆ ball (x:ℂ) R :=
    (sourceStandardRoot_gapSegment_subset_periodicSegment
      hp hp1 ψ m).trans hseg
  have hgreal : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m), (g z).im = 0 := by
    intro z hz
    have hzPeriod : z ∈ sourcePeriodicSegment hp hp1 ψ m :=
      sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m hz
    have hzIm : z.im = 0 :=
      sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hψ m z hzPeriod
    have hzReal : (z.re:ℂ) = z := by
      apply Complex.ext
      · rfl
      · simpa using hzIm.symm
    have hzDom : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
      hdom (ball_subset_closedBall (hseg hzPeriod))
    have hΦreal : (Φ z).im = 0 := by
      simpa only [Φ,hzReal] using
        sourcePsiCandidateVariation_im_eq_zero_of_real_data
          hp hp1 n a h hroots hreal z.re
    have hPreal : (P z).im = 0 := by
      simpa only [P,hzReal] using
        sourceStandardRootOmittedProduct_im_eq_zero_on_realAxis
          hp hp1 ψ hψ m z.re (hzReal ▸ hzDom)
    simp [g,Complex.div_im,hΦreal,hPreal]
  have hpoint (z : ℂ) (hz : z ∈ sphere (x:ℂ) R) :
      g z / sourceStandardRoot hp hp1 ψ m z =
        (2*I) * (Φ z / sourceCanonicalRoot hp hp1 ψ z) := by
    have hzDom : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
      hdom (sphere_subset_closedBall hz)
    have hPz : P z ≠ 0 :=
      sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m hzDom
    have hCz : sourceCanonicalRoot hp hp1 ψ z ≠ 0 :=
      sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ z (hcircle hz)
    have hSz : sourceStandardRoot hp hp1 ψ m z ≠ 0 := by
      intro hs
      apply hCz
      rw [sourceCanonicalRoot_eq_omitted hp hp1 m ψ z,hs]
      simp
    dsimp [g,P]
    rw [sourceCanonicalRoot_eq_omitted hp hp1 m ψ z]
    field_simp [hPz,hSz,Complex.I_ne_zero]
  have hInt :
      (∮ z in C((x:ℂ),R),
        g z / sourceStandardRoot hp hp1 ψ m z) =
      (2*I) * (∮ z in C((x:ℂ),R),
        Φ z / sourceCanonicalRoot hp hp1 ψ z) := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    exact hpoint z hz
  have hIntZero :
      (∮ z in C((x:ℂ),R),
        g z / sourceStandardRoot hp hp1 ψ m z) = 0 := by
    rw [hInt]
    change (2*I) *
      (∮ z in C((x:ℂ),R),
        sourcePsiCandidateVariation n a h z /
          sourceCanonicalRoot hp hp1 ψ z) = 0
    rw [hzero,mul_zero]
  obtain ⟨μ,hμ,hvalue⟩ :=
    weighted_sourceStandardRoot_realCenteredCircle_real_mean_value
      hp hp1 ψ hψ m hopen g hgreal x R hR hseg hgap hg
  have hgzero : g μ = 0 := by
    rw [hIntZero] at hvalue
    simpa using hvalue.symm
  have hPμ : P μ ≠ 0 :=
    sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ μ m
      (hdom (ball_subset_closedBall (hgap hμ)))
  refine ⟨μ,hμ,?_⟩
  have hΦzero : Φ μ = 0 := by
    have := congrArg (fun z : ℂ => z * P μ) hgzero
    simpa [g,hPμ] using this
  exact hΦzero

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
