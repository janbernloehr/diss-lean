import NLS.ComplexAnalysis.SquareRootDerivative
import NLS.ZakharovShabat.SourceCanonicalRootJointAnalytic
import NLS.ZakharovShabat.SourceCriticalRootRatioContourHomotopy

/-!
# Source derivative of the canonical square root

The canonical root is a nonvanishing analytic square root of the
discriminant squared minus four away from the moving periodic gaps.
Its source Fréchet derivative follows by differentiating that square
identity.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source Fréchet derivative of the canonical root is the
discriminant-to-root quotient times the source derivative of the
discriminant, in every source direction. -/
theorem fderiv_sourceCanonicalRoot_eq_discriminant_div_root_mul_fderiv
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ)
    (h : CoeffPair p) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourceCanonicalRoot hp hp1 ψ z) φ) h =
      canonicalDiscriminant hp (periodOnePotential φ) z /
        sourceCanonicalRoot hp hp1 φ z *
          (fderiv ℂ (fun ψ : CoeffPair p =>
            canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h := by
  obtain ⟨W,_,_,hreal,hDopen,hroot⟩ :=
    exists_global_source_analytic_canonicalRoot hp hp1
  let D := sourceCanonicalRootJointDomain hp hp1 W
  have hpoint : (z,φ) ∈ D := ⟨hreal hφ,hz⟩
  let V : Set (CoeffPair p) := {ψ | (z,ψ) ∈ D}
  have hVopen : IsOpen V := hDopen.preimage
    (continuous_const.prodMk continuous_id)
  have hQ : DifferentiableAt ℂ
      (fun ψ : CoeffPair p => sourceCanonicalRoot hp hp1 ψ z) φ := by
    exact ((hroot (z,φ) hpoint).comp
      (f := fun ψ : CoeffPair p => (z,ψ))
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hΔ : DifferentiableAt ℂ
      (fun ψ : CoeffPair p =>
        canonicalDiscriminant hp (periodOnePotential ψ) z) φ := by
    have hdisc := analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
    exact ((hdisc (z,φ) (mem_univ _)).comp
      (f := fun ψ : CoeffPair p => (z,ψ))
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hsq (ψ : CoeffPair p) (hψ : ψ ∈ V) :
      (sourceCanonicalRoot hp hp1 ψ z)^2 =
        (canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4 :=
    sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 ψ z hψ.2
  exact NLS.ComplexAnalysis.fderiv_squareRoot_of_sq_eq_discriminant_sq_sub_four
    (fun ψ : CoeffPair p => sourceCanonicalRoot hp hp1 ψ z)
    (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z)
    V hVopen hsq φ hpoint hQ hΔ
    (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ z hz) h

/-- The same square identity determines the spectral derivative of
the canonical root away from its periodic cuts. -/
theorem deriv_sourceCanonicalRoot_eq_discriminant_div_root_mul_deriv
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    deriv (sourceCanonicalRoot hp hp1 φ) z =
      canonicalDiscriminant hp (periodOnePotential φ) z /
        sourceCanonicalRoot hp hp1 φ z *
          deriv (canonicalDiscriminant hp (periodOnePotential φ)) z := by
  obtain ⟨W,_,_,hreal,hDopen,hroot⟩ :=
    exists_global_source_analytic_canonicalRoot hp hp1
  let D := sourceCanonicalRootJointDomain hp hp1 W
  let Q := sourceCanonicalRootJointProduct hp hp1
  let Δ : ℂ × CoeffPair p → ℂ := fun t =>
    canonicalDiscriminant hp (periodOnePotential t.2) t.1
  have hpoint : (z,φ) ∈ D := ⟨hreal hφ,hz⟩
  have hQ : DifferentiableAt ℂ Q (z,φ) :=
    (hroot (z,φ) hpoint).differentiableAt
  have hdisc : AnalyticOnNhd ℂ Δ univ :=
    analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
  have hΔ : DifferentiableAt ℂ Δ (z,φ) :=
    (hdisc (z,φ) (mem_univ _)).differentiableAt
  have hsq (t : ℂ × CoeffPair p) (ht : t ∈ D) :
      Q t ^ 2 = Δ t ^ 2 - 4 :=
    sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 t.2 t.1 ht.2
  have hderiv := NLS.ComplexAnalysis.fderiv_squareRoot_of_sq_eq_discriminant_sq_sub_four
    Q Δ D hDopen hsq (z,φ) hpoint hQ hΔ
    (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ z hz) ((1,0) : ℂ × CoeffPair p)
  rw [← NLS.ComplexAnalysis.deriv_spectral_section_eq_fderiv Q z φ hQ,
    ← NLS.ComplexAnalysis.deriv_spectral_section_eq_fderiv Δ z φ hΔ] at hderiv
  exact hderiv

end NLS.ZakharovShabat
