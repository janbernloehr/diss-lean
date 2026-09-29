import NLS.ZakharovShabat.SourcePsiFullProductVariation
import NLS.ZakharovShabat.SourcePsiContourAnalytic

/-!
# Contour functional for the full product variation

The canonical denominator is independent of the numerator roots.
Differentiating the full product contour therefore gives the integral
of its entire variation. The derivative is a continuous linear
functional, which will extend the limit matrix formula from basis
directions to all of `ℓᵖ`.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full numerator contour before the limit-operator normalization. -/
def sourcePsiFullProductContour (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p) (c : ℂ) (R : ℝ) : ℂ :=
  ∮ z in C(c,R), jointSingleSpectralProduct (z,a) /
    sourceCanonicalRoot hp hp1 φ z

/-- The continuous root derivative with the sign and `1/π`
normalization required by the limit operator `Q*`. -/
def sourcePsiFullProductContourDerivative (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p) (c : ℂ) (R : ℝ) : Coeff p →L[ℂ] ℂ :=
  (-(Real.pi : ℂ)⁻¹) •
    fderiv ℂ (fun b : Coeff p => sourcePsiFullProductContour hp hp1 b φ c R) a

/-- Differentiation of the raw contour commutes with integration on
every valid fixed circle at a real-type potential. -/
theorem fderiv_sourcePsiFullProductContour_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a h : Coeff p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    (fderiv ℂ (fun b : Coeff p => sourcePsiFullProductContour hp hp1 b φ c R) a) h =
      ∮ z in C(c,R), sourcePsiFullProductVariation a h z /
        sourceCanonicalRoot hp hp1 φ z := by
  obtain ⟨W,_,_,hreal,hDopen,hroot⟩ :=
    exists_global_source_analytic_canonicalRoot hp hp1
  let D : Set (ℂ × Coeff p) :=
    {t | (t.1,φ) ∈ sourceCanonicalRootJointDomain hp hp1 W}
  let F : ℂ × Coeff p → ℂ := fun t =>
    jointSingleSpectralProduct t / sourceCanonicalRoot hp hp1 φ t.1
  have hD : IsOpen D :=
    hDopen.preimage (continuous_fst.prodMk continuous_const)
  have hF : AnalyticOnNhd ℂ F D := by
    intro t ht
    have hden : AnalyticAt ℂ
        (fun q : ℂ × Coeff p => sourceCanonicalRoot hp hp1 φ q.1) t :=
      (hroot (t.1,φ) ht).comp
        (f := fun q : ℂ × Coeff p => (q.1,φ))
        (analyticAt_fst.prod analyticAt_const)
    exact (analyticOnNhd_jointSingleSpectralProduct hp hp1 t (mem_univ _)).div
      hden (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ t.1 ht.2)
  have hbase (z : ℂ) (hz : z ∈ sphere c R) : (z,a) ∈ D :=
    ⟨hreal hφ,hcircle hz⟩
  obtain ⟨V,hVopen,haV,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      F D hD hF c R a hbase
  have hdom : ∀ b ∈ V, ∀ θ : ℝ, (circleMap c R θ,b) ∈ D :=
    fun b hb θ => (hbound (circleMap c R θ)
      (circleMap_mem_sphere c hR θ) b hb).1
  have hdbound : ∀ b ∈ V, ∀ θ : ℝ,
      ‖fderiv ℂ F (circleMap c R θ,b)‖ ≤ M :=
    fun b hb θ => (hbound (circleMap c R θ)
      (circleMap_mem_sphere c hR θ) b hb).2
  have hformula := NLS.ComplexAnalysis.fderiv_circleIntegral_apply_of_jointAnalytic
    F D hD hF c R hR V hVopen a haV M hdom hdbound h
  change (fderiv ℂ (fun b : Coeff p => ∮ z in C(c,R), F (z,b)) a) h = _
  rw [hformula]
  apply circleIntegral.integral_congr hR
  intro z _
  have hnum : DifferentiableAt ℂ
      (fun b : Coeff p => jointSingleSpectralProduct (z,b)) a :=
    ((analyticOnNhd_jointSingleSpectralProduct hp hp1
      (z,a) (mem_univ _)).comp
        (f := fun b : Coeff p => (z,b))
        (analyticAt_const.prod analyticAt_id)).differentiableAt
  simp only [F, div_eq_mul_inv]
  rw [fderiv_mul_const hnum]
  simp [sourcePsiFullProductVariation, smul_eq_mul, mul_comm]

/-- The normalized continuous functional is the full variation contour. -/
theorem sourcePsiFullProductContourDerivative_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a h : Coeff p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    sourcePsiFullProductContourDerivative hp hp1 a φ c R h =
      -(∮ z in C(c,R), sourcePsiFullProductVariation a h z /
        sourceCanonicalRoot hp hp1 φ z) / (Real.pi : ℂ) := by
  unfold sourcePsiFullProductContourDerivative
  rw [smul_apply, fderiv_sourcePsiFullProductContour_apply
    hp hp1 a h φ hφ c R hR hcircle]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

end NLS.ZakharovShabat
