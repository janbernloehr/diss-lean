import NLS.Poisson.RegularSourceCotangentIntegral
import NLS.ZakharovShabat.SourceDiscriminantRegularPoisson

/-! # Hilbert coefficients of the actual action derivatives

The discriminant's regular cotangent divided by the canonical root is
integrable along each isolating circle in both the source dual norm and
the Hilbert coefficient norm. Its contour integral is the actual action
derivative. This constructs regular action cotangents at every real
source for the entire finite exponent range, including collapsed gaps.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceActionVariationRegularCotangent (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) : RegularSourceCotangent p :=
  (sourceDiscriminantRegularCotangent hp z φ).smul (sourceCanonicalRoot hp hp1 φ z)⁻¹

@[simp] theorem sourceActionVariationRegularCotangent_toCotangent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z : ℂ) :
    (sourceActionVariationRegularCotangent hp hp1 φ z).toCotangent =
      sourceActionVariationCotangent hp hp1 φ z := by
  simp only [sourceActionVariationRegularCotangent, RegularSourceCotangent.smul,
    sourceDiscriminantRegularCotangent_toCotangent, sourceActionVariationCotangent]

theorem analyticOnNhd_sourceActionVariationRegularCoefficients
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    AnalyticOnNhd ℂ (fun z => (sourceActionVariationRegularCotangent hp hp1 φ z).coefficients)
      (sourceCanonicalRootDomain hp hp1 φ) := by
  intro z hz
  have hC := (analyticOnNhd_sourceDiscriminantRegularCoefficients_joint hp hp1
    (z,φ) (mem_univ _)).comp (f := fun w : ℂ => (w,φ)) (analyticAt_id.prod analyticAt_const)
  exact ((sourceCanonicalRoot_analyticOnNhd hp hp1 φ z hz).inv
    (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ z hz)).smul hC

theorem circleIntegrable_sourceActionVariationRegularCoefficients
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    CircleIntegrable (fun z => (sourceActionVariationRegularCotangent hp hp1 φ z).coefficients) c R :=
  ((analyticOnNhd_sourceActionVariationRegularCoefficients hp hp1 φ).continuousOn.mono hc).circleIntegrable hR

/-- The contour construction uses the original indexed action chart. -/
def sourceActionRegularCotangentOnChart
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ch : SourceRealActionBallChart hp hp1 n)
    (φ : CoeffPair p) (hφ : φ ∈ ball ch.center ch.radius) : RegularSourceCotangent p := by
  have hg := ch.geometry φ hφ
  have hc := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n
    ch.spectralCenter ch.spectralRadius hg.1 hg.2
  exact (RegularSourceCotangent.contourIntegral (sourceActionVariationRegularCotangent hp hp1 φ)
    ch.spectralCenter ch.spectralRadius
    (by simpa only [sourceActionVariationRegularCotangent_toCotangent] using
      (circleIntegrable_sourceActionVariationCotangent hp hp1 φ
        ch.spectralCenter ch.spectralRadius ch.spectralRadius_pos.le hc))
    (circleIntegrable_sourceActionVariationRegularCoefficients hp hp1 φ
      ch.spectralCenter ch.spectralRadius ch.spectralRadius_pos.le hc)).smul (-(Real.pi : ℂ)⁻¹)

/-- The constructed regular cotangent is exactly the actual Fréchet
derivative, not merely a collection of formal coordinate derivatives. -/
@[simp] theorem sourceActionRegularCotangentOnChart_toCotangent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ch : SourceRealActionBallChart hp hp1 n)
    (φ : CoeffPair p) (hφ : φ ∈ ball ch.center ch.radius)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    (sourceActionRegularCotangentOnChart hp hp1 n ch φ hφ).toCotangent =
      fderiv ℂ (sourceComplexAction hp hp1 n) φ := by
  rw [fderiv_sourceComplexAction_eq_cotangent_circle_on_chart hp hp1 n ch φ hreal hφ]
  simp only [sourceActionRegularCotangentOnChart, RegularSourceCotangent.smul,
    RegularSourceCotangent.contourIntegral, sourceActionVariationRegularCotangent_toCotangent]

/-- A centered chart is proved to exist at every real source, so this
construction needs no supplied chart or open-gap hypothesis. -/
def sourceActionRegularCotangent (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (φ : realTypeSourceLocus p) : RegularSourceCotangent p :=
  let h := exists_sourceRealActionBallChart_centered hp hp1 n φ.val φ.property
  sourceActionRegularCotangentOnChart hp hp1 n h.choose φ.val
    (by rw [h.choose_spec]; exact mem_ball_self h.choose.radius_pos)

@[simp] theorem sourceActionRegularCotangent_toCotangent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : realTypeSourceLocus p) :
    (sourceActionRegularCotangent hp hp1 n φ).toCotangent =
      fderiv ℂ (sourceComplexAction hp hp1 n) φ.val := by
  unfold sourceActionRegularCotangent
  exact sourceActionRegularCotangentOnChart_toCotangent hp hp1 n _ φ.val _ φ.property

/-- Any admissible chart gives the same Hilbert coefficient pair. -/
theorem sourceActionRegularCotangent_coefficients_eq_on_chart
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : realTypeSourceLocus p)
    (ch : SourceRealActionBallChart hp hp1 n) (hφ : φ.val ∈ ball ch.center ch.radius) :
    (sourceActionRegularCotangent hp hp1 n φ).coefficients =
      (sourceActionRegularCotangentOnChart hp hp1 n ch φ.val hφ).coefficients := by
  apply RegularSourceCotangent.coefficients_eq_of_toCotangent_eq
  rw [sourceActionRegularCotangent_toCotangent,
    sourceActionRegularCotangentOnChart_toCotangent hp hp1 n ch φ.val hφ φ.property]

end NLS.ZakharovShabat
