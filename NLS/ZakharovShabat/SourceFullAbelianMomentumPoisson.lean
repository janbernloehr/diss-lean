import NLS.ZakharovShabat.SourceFullAbelianMomentumContour
import NLS.ZakharovShabat.SourceAbelianMomentLinearShift

/-! # The actual angle bracket of the physical momentum contour

Differentiation under a fixed admissible contour gives its linear psi
moment. Finite-gap contour decomposition evaluates this bracket as 2πn.
The primitive and moment atlas may use different ambient neighborhoods.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
open NLS.ComplexAnalysis NLS.Poisson
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B V W U Wa : Set (CoeffPair p)}
variable {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Differentiating the quadratic contour gives the linear moment through the original bivector. -/
theorem theta_momentumContour_eq_linear
    (E : SourceAngularThetaCommonDomainData hp hp1 W₀ B V s)
    (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (φ : realTypeSourceLocus p)
    (hφ : φ.val ∈ U)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ.val) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s
      (sourceFullAbelianMomentumContour hp hp1 W c R) φ.val =
      (I/Real.pi : ℂ)*sourceAbelianMomentCircle hp hp1 W n 0 1 (s n φ.val : Coeff p) φ.val c R := by
  have hd := D.analyticAt_momentumContour c R hR φ.val hφ hcircle
  let F : CoeffPair p → ℂ := fun ψ => ∮ z in C(c,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ))^2
  have hcoef : (-I/Real.pi : ℂ) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr I_ne_zero) (by exact_mod_cast Real.pi_ne_zero)
  have hF : DifferentiableAt ℂ F φ.val := by
    have he : F = fun ψ => (-I/Real.pi : ℂ)⁻¹*sourceFullAbelianMomentumContour hp hp1 W c R ψ := by
      funext ψ
      simp only [sourceFullAbelianMomentumContour,← mul_assoc,inv_mul_cancel₀ hcoef,one_mul]
      rfl
    rw [he]
    exact hd.differentiableAt.const_mul _
  have hder := hF.hasFDerivAt.const_smul (-I/Real.pi : ℂ)
  change sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s φ.val)
    (fderiv ℂ ((-I/Real.pi : ℂ) • F) φ.val) = _
  rw [hder.fderiv]
  simp only [map_smul,smul_eq_mul]
  have he := E.theta_power_circle_eq D h2p n 0 1 φ hφ hgap c R hR hcircle
  change sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s φ.val) (fderiv ℂ F φ.val) = _ at he
  rw [he]
  norm_num
  ring

/-- The contour bracket is 2πn even when the primitive and moment atlas use different neighborhoods. -/
theorem exists_finiteGap_momentumContour_bracket
    (E : SourceAngularThetaCommonDomainData hp hp1 W₀ B V s)
    (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (A : SourceAbelianMomentAtlas hp hp1 Wa s)
    (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sphere (0 : ℂ) R ⊆ sourceCanonicalRootDomain hp hp1 φ.val →
      ∀ n : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val) n ≠ 0 →
      sourceAngularThetaFunctionalBracket hp hp1 h2p n s
        (sourceFullAbelianMomentumContour hp hp1 W 0 R) φ.val = 2*(Real.pi : ℂ)*n := by
  obtain ⟨T,hT,hformula⟩ := A.exists_finiteGap_linear_contour_formula
    E.psi.toSourcePsiNormalizedComplexExtension φ hf
  refine ⟨T,hT,fun R hR hcircle n hn => ?_⟩
  rw [E.theta_momentumContour_eq_linear D h2p n φ (D.real_subset φ.property) hn 0 R
    (hT.trans_le hR).le hcircle]
  obtain ⟨C⟩ := D.charts φ.val (D.real_subset φ.property)
  obtain ⟨Ca⟩ := (A.localChart φ).charts φ.val (mem_ball_self (A.localChart φ).radius_pos)
  rw [sourceAbelianMomentCircle_independent_neighborhood hp hp1 W Wa n 0 1
    (s n φ.val) φ.val C Ca 0 R (hT.trans_le hR).le hcircle]
  exact hformula R hR hcircle n hn
end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
