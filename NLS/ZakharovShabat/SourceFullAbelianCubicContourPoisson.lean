import NLS.ZakharovShabat.SourceFullAbelianAnglePoisson
import NLS.ZakharovShabat.SourceFullAbelianCubicHamiltonianContour
import NLS.ZakharovShabat.SourceAbelianMomentCircle
import NLS.Poisson.SourceBracketCircleIntegral
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! # The angle derivative of the cubic Hamiltonian contour

Differentiating the actual full primitive under a fixed admissible
contour gives exactly `-4/(2*pi)` times its unshifted quadratic psi
contour. At real finite-gap sources, sufficiently large cubic contours
have the physical value `H_3 - 2*H_1^2`; the derivative identity is proved
on the open contour domain, without assuming the frequency formula.
-/
noncomputable section
open Set Metric Complex NLS.Poisson NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceFullAbelianCubicContour (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (c : ℂ) (R : ℝ) (ψ : CoeffPair p) : ℂ :=
  (8/(6*Real.pi) : ℂ)*(∮ z in C(c,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ))^3)

namespace SourceFullAbelianDifferentialData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W U : Set (CoeffPair p)}

/-- The scaled cubic contour is analytic near any source whose circle
avoids the moving gaps. Compactness supplies the common neighborhood. -/
theorem analyticAt_cubicContour (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (ψ : CoeffPair p) (hψ : ψ ∈ U)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    AnalyticAt ℂ (sourceFullAbelianCubicContour hp hp1 W c R) ψ := by
  let F : ℂ × CoeffPair p → ℂ := fun t => (sourceFullAbelianPrimitive hp hp1 W 0 t)^3
  have hF : AnalyticOnNhd ℂ F (sourceCanonicalRootJointDomain hp hp1 U) := fun t ht => (D.analytic 0 t ht).pow 3
  obtain ⟨V,hV,hψV,_,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle F _
    D.root_domain_open hF c R ψ (fun z hz => ⟨hψ,hcircle hz⟩)
  have hi := analyticOnNhd_circleIntegral_of_jointAnalytic F D.root_domain_open hF c R hR hV
    (fun χ hχ z hz => (hbound z hz χ hχ).1) ψ hψV
  exact analyticAt_const.mul hi

/-- The cubic contour's physical value on all sufficiently large
circles, using the same primitive as this differential domain. -/
theorem exists_cubicContour_eq_physical (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sourceFullAbelianCubicContour hp hp1 W 0 R φ.val =
        sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3-2*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)^2 := by
  obtain ⟨E⟩ := D.charts φ.val (D.real_subset φ.property)
  obtain ⟨T,hT,hc⟩ := exists_sourceFullAbelian_hamiltonian_cube_contour_of_chart φ hf E
  exact ⟨T,hT,fun R hR => (hc R hR).symm⟩

end SourceFullAbelianDifferentialData
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B V W U : Set (CoeffPair p)}
variable {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The angle bracket of a power contour is its actual weighted psi
moment, with the derivative's exact coefficient. -/
theorem theta_power_circle_eq
    (E : SourceAngularThetaCommonDomainData hp hp1 W₀ B V s)
    (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n j : ℤ) (m : ℕ) (φ : realTypeSourceLocus p)
    (hφ : φ.val ∈ U)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ.val) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s
      (fun ψ => ∮ z in C(c,R), (sourceFullAbelianPrimitive hp hp1 W j (z,ψ))^(m+1)) φ.val =
      -((m+1 : ℕ) : ℂ)/2*sourceAbelianMomentCircle hp hp1 W n j m (s n φ.val : Coeff p) φ.val c R := by
  let F : ℂ × CoeffPair p → ℂ := fun t => (sourceFullAbelianPrimitive hp hp1 W j t)^(m+1)
  have hF : AnalyticOnNhd ℂ F (sourceCanonicalRootJointDomain hp hp1 U) := fun t ht => (D.analytic j t ht).pow (m+1)
  rw [sourceAngularThetaFunctionalBracket,sourceBivector_circleIntegral_of_jointAnalytic h2p F _
    D.root_domain_open hF c R hR φ.val (fun z hz => ⟨hφ,hcircle hz⟩)]
  unfold sourceAbelianMomentCircle
  rw [← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr hR
  intro z hz
  have he := E.thetaFullPrimitive_pow_eq D h2p n j m φ hφ hgap z (hcircle hz)
  dsimp only [sourceAngularThetaFunctionalBracket,sourceAbelianMomentIntegrand] at *
  simpa only [mul_assoc] using he

/-- The exact coefficient and sign in the differentiated contour
formula of Lemma 20.2, before decomposing the large circle into gaps. -/
theorem theta_cubicContour_eq_quadratic
    (E : SourceAngularThetaCommonDomainData hp hp1 W₀ B V s)
    (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (φ : realTypeSourceLocus p)
    (hφ : φ.val ∈ U)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ.val) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s
      (sourceFullAbelianCubicContour hp hp1 W c R) φ.val =
      -(4/(2*Real.pi) : ℂ)*sourceAbelianMomentCircle hp hp1 W n 0 2 (s n φ.val : Coeff p) φ.val c R := by
  have hd := D.analyticAt_cubicContour c R hR φ.val hφ hcircle
  let F : CoeffPair p → ℂ := fun ψ => ∮ z in C(c,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ))^3
  have hcoef : (8/(6*Real.pi) : ℂ) ≠ 0 := by
    apply div_ne_zero (by norm_num)
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hF : DifferentiableAt ℂ F φ.val := by
    have he : F = fun ψ => (8/(6*Real.pi) : ℂ)⁻¹*sourceFullAbelianCubicContour hp hp1 W c R ψ := by
      funext ψ
      simp only [sourceFullAbelianCubicContour,← mul_assoc,inv_mul_cancel₀ hcoef,one_mul]
      rfl
    rw [he]
    exact hd.differentiableAt.const_mul _
  have hder := hF.hasFDerivAt.const_smul (8/(6*Real.pi) : ℂ)
  change sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s φ.val)
    (fderiv ℂ ((8/(6*Real.pi) : ℂ) • F) φ.val) = _
  rw [hder.fderiv]
  simp only [map_smul,smul_eq_mul]
  have he := E.theta_power_circle_eq D h2p n 0 2 φ hφ hgap c R hR hcircle
  change sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s φ.val) (fderiv ℂ F φ.val) = _ at he
  rw [he]
  norm_num
  ring

end SourceAngularThetaCommonDomainData
/-- The differentiated cubic contour formula for actual angle and
primitive data, with no supplied chart or differential hypothesis.
The Poisson bracket is available for every finite exponent at least two. -/
theorem exists_sourceFullAbelian_cubicContour_angle_formula
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W U V : Set (CoeffPair p), IsOpen W ∧ IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ W ∧
      IsOpen V ∧ realTypeSourceLocus p ⊆ V ∧
      ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
        SourcePsiNormalizedComplexExtension hp hp1 V s ∧
        (∀ (φ : realTypeSourceLocus p) (n : ℤ),
          canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0 →
          ∀ (c : ℂ) (R : ℝ), 0 ≤ R → sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ.val →
            AnalyticAt ℂ (sourceFullAbelianCubicContour hp hp1 W c R) φ.val ∧
            sourceAngularThetaFunctionalBracket hp hp1 h2p n s
              (sourceFullAbelianCubicContour hp hp1 W c R) φ.val =
              -(4/(2*Real.pi) : ℂ)*sourceAbelianMomentCircle hp hp1 W n 0 2 (s n φ.val : Coeff p) φ.val c R) ∧
        (∀ (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1),
          ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
            sourceFullAbelianCubicContour hp hp1 W 0 R φ.val =
              sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3-2*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)^2) := by
  obtain ⟨W,U,hW,D⟩ := exists_sourceFullAbelianDifferentialData hp hp1
  obtain ⟨V,B,Vθ,hV,_,hrealV,_,_,_,s,E⟩ := exists_sourceAngularTheta_theorem13_1_iv hp hp1
  refine ⟨W,U,V,hW,D.source_open,D.real_subset,D.source_subset,hV,hrealV,s,E.psi.toSourcePsiNormalizedComplexExtension,?_,?_⟩
  · intro φ n hgap c R hR hcircle
    exact ⟨D.analyticAt_cubicContour c R hR φ.val (D.real_subset φ.property) hcircle,
      E.theta_cubicContour_eq_quadratic D h2p n φ (D.real_subset φ.property) hgap c R hR hcircle⟩
  · exact D.exists_cubicContour_eq_physical

end NLS.ZakharovShabat
