import NLS.ComplexAnalysis.CircleIntegralIntegrationByParts
import NLS.ZakharovShabat.SourceCriticalRootRatioSourceFDeriv

/-!
# The source-discriminant variation on an action circle

For a fixed real-type source and a source direction, the quotient
`(D_source Δ) / Q` is analytic off the periodic cuts. Closed-circle
integration by parts therefore applies even when the circle encloses
a noncollapsed gap.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The discriminant's source variation is entire in the spectral
parameter for every source and direction. -/
theorem analyticOnNhd_sourceDiscriminantVariation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ h : CoeffPair p) :
    AnalyticOnNhd ℂ
      (fun z : ℂ =>
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h)
      univ := by
  let F : ℂ × CoeffPair p → ℂ := fun t =>
    canonicalDiscriminant hp (periodOnePotential t.2) t.1
  have hF : AnalyticOnNhd ℂ F univ :=
    analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
  let ev : ((ℂ × CoeffPair p) →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (0,h)
  have hjoint : AnalyticOnNhd ℂ
      (fun t : ℂ × CoeffPair p => (fderiv ℂ F t) (0,h)) univ :=
    ev.comp_analyticOnNhd hF.fderiv
  intro z _
  have hsection := (hjoint (z,φ) (mem_univ _)).comp
    (f := fun w : ℂ => (w,φ))
    (analyticAt_id.prod analyticAt_const)
  convert hsection using 1
  funext w
  rw [NLS.ComplexAnalysis.fderiv_source_section_eq_joint
    F w φ ((hF (w,φ) (mem_univ _)).differentiableAt)]
  simp [F]

/-- The source variation divided by the canonical root is analytic
on the full complement of the periodic cuts. -/
theorem analyticOnNhd_sourceDiscriminantVariation_div_root
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p)
    (h : CoeffPair p) :
    AnalyticOnNhd ℂ
      (fun z : ℂ =>
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
          sourceCanonicalRoot hp hp1 φ z)
      (sourceCanonicalRootDomain hp hp1 φ) := by
  intro z hz
  exact ((analyticOnNhd_sourceDiscriminantVariation hp hp1 φ h) z
    (mem_univ _)).div
    (sourceCanonicalRoot_analyticOnNhd hp hp1 φ z hz)
    (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ z hz)

/-- Weighted integration by parts for the actual source variation
on any circle avoiding the periodic cuts. -/
theorem circleIntegral_mul_deriv_sourceDiscriminantVariation_div_root_eq_neg
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p)
    (h : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    (∮ z in C(c,R), z * deriv (fun w : ℂ =>
      (fderiv ℂ (fun ψ : CoeffPair p =>
        canonicalDiscriminant hp (periodOnePotential ψ) w) φ) h /
        sourceCanonicalRoot hp hp1 φ w) z) =
      -(∮ z in C(c,R),
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
          sourceCanonicalRoot hp hp1 φ z) := by
  exact NLS.ComplexAnalysis.circleIntegral_mul_deriv_eq_neg_of_analyticOnNhd
    (fun z : ℂ =>
      (fderiv ℂ (fun ψ : CoeffPair p =>
        canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
        sourceCanonicalRoot hp hp1 φ z)
    (sourceCanonicalRootDomain hp hp1 φ)
    (analyticOnNhd_sourceDiscriminantVariation_div_root hp hp1 φ h)
    c R hR hcircle

end NLS.ZakharovShabat
