import NLS.ZakharovShabat.SourcePsiFullProductVariation
import NLS.ZakharovShabat.SourcePsiCandidateVariationRealAxis
import NLS.ZakharovShabat.SourceEntireGapContourZeros
import NLS.ZakharovShabat.SourcePsiSelectedKernelGapZeroSequence

/-!
# Full product variation zeros from vanishing gap contours

The entire variation of the undeleted product is real on the real
spectral axis for real root data and a real direction. Its vanishing
contours therefore give a zero in every open periodic gap. At a
collapsed gap, Cauchy's formula gives a zero at the midpoint for any
complex direction.
-/

noncomputable section
open Set Metric Complex ComplexConjugate
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reality of both restored-factor terms gives reality of the full
variation on the real spectral axis. -/
theorem sourcePsiFullProductVariation_im_eq_zero_of_real_data
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a h : Coeff p)
    (hroots : ∀ j : ℤ, (displacedRoots a j).im = 0)
    (hreal : ∀ j : ℤ, (h j).im = 0) (x : ℝ) :
    (sourcePsiFullProductVariation a h (x:ℂ)).im = 0 := by
  have hconj : conj (sourcePsiCandidate 0 ((x:ℂ),a)) =
      sourcePsiCandidate 0 ((x:ℂ),a) := by
    simpa using (sourcePsiCandidate_conj_of_real_roots hp hp1 0 a hroots (x:ℂ)).symm
  have hnum : (sourcePsiCandidate 0 ((x:ℂ),a)).im = 0 :=
    Complex.conj_eq_iff_im.mp hconj
  have hvar := sourcePsiCandidateVariation_im_eq_zero_of_real_data
    hp hp1 0 a h hroots hreal x
  rw [sourcePsiFullProductVariation_eq_deleted_variation hp hp1 0]
  simp [Complex.mul_im, hnum, hvar, hroots 0, hreal 0]

/-- A zero full-variation contour at a collapsed gap forces a zero
at its midpoint, also for complex root directions. -/
theorem sourcePsiFullProductVariation_zero_at_collapsedGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) (a h : Coeff p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball c R)
    (hdom : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (∮ z in C(c,R), sourcePsiFullProductVariation a h z /
      sourceCanonicalRoot hp hp1 ψ z) = 0) :
    sourcePsiFullProductVariation a h (sourceStandardRootMidpoint hp hp1 ψ m) = 0 :=
  sourceEntireNumerator_zero_at_collapsedGap hp hp1 ψ hψ m
    (sourcePsiFullProductVariation a h)
    (analyticOnNhd_sourcePsiFullProductVariation hp hp1 a h)
    hgap c R hR hmid hdom hcircle hzero

/-- Every vanishing full-variation contour at real data gives a zero
in its enclosed real periodic gap, whether open or collapsed. -/
theorem exists_sourcePsiFullProductVariation_zero_on_realGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) (a h : Coeff p)
    (hroots : ∀ j : ℤ, (displacedRoots a j).im = 0)
    (hreal : ∀ j : ℤ, (h j).im = 0)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (∮ z in C((x:ℂ),R), sourcePsiFullProductVariation a h z /
      sourceCanonicalRoot hp hp1 ψ z) = 0) :
    ∃ μ ∈ sourcePeriodicSegment hp hp1 ψ m, sourcePsiFullProductVariation a h μ = 0 := by
  rcases sourcePeriodicGap_eq_zero_or_open hp hp1 ψ hψ m with hcollapsed | hopen
  · have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 ψ m
    refine ⟨sourceStandardRootMidpoint hp hp1 ψ m,hmid,?_⟩
    exact sourcePsiFullProductVariation_zero_at_collapsedGap hp hp1 ψ hψ m a h
      hcollapsed (x:ℂ) R hR (hseg hmid) hdom hcircle hzero
  · obtain ⟨μ,hμ,hzeroμ⟩ := exists_sourceEntireNumerator_zero_on_openGap
      hp hp1 ψ hψ m (sourcePsiFullProductVariation a h)
      (analyticOnNhd_sourcePsiFullProductVariation hp hp1 a h)
      (sourcePsiFullProductVariation_im_eq_zero_of_real_data hp hp1 a h hroots hreal)
      hopen x R hR hseg hdom hcircle hzero
    exact ⟨μ,sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m hμ,hzeroμ⟩

end NLS.ZakharovShabat
