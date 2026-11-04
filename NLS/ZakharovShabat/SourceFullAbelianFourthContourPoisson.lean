import NLS.ZakharovShabat.SourceFullAbelianCubicContourPoisson
import NLS.ZakharovShabat.SourceFullAbelianFourthHamiltonianContour

/-! # The angle derivative of the physical quartic contour

The verified joint power-contour formula gives the exact coefficient
−4i/π of the unshifted cubic psi moment. No frequency formula is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.Poisson NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual quartic contour has physical value H₄−6H₁H₂ at finite gaps. -/
def sourceFullAbelianFourthContour (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (c : ℂ) (R : ℝ) (ψ : CoeffPair p) : ℂ :=
  (2*I/Real.pi:ℂ)*(∮ z in C(c,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ))^4)

namespace SourceFullAbelianDifferentialData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W U : Set (CoeffPair p)}

/-- Moving-gap separation gives analyticity near every admissible source. -/
theorem analyticAt_fourthContour (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (ψ : CoeffPair p) (hψ : ψ ∈ U)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    AnalyticAt ℂ (sourceFullAbelianFourthContour hp hp1 W c R) ψ := by
  let F : ℂ × CoeffPair p → ℂ := fun t => (sourceFullAbelianPrimitive hp hp1 W 0 t)^4
  have hF : AnalyticOnNhd ℂ F (sourceCanonicalRootJointDomain hp hp1 U) := fun t ht => (D.analytic 0 t ht).pow 4
  obtain ⟨V,hV,hψV,_,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle F _
    D.root_domain_open hF c R ψ (fun z hz => ⟨hψ,hcircle hz⟩)
  have hi := analyticOnNhd_circleIntegral_of_jointAnalytic F D.root_domain_open hF c R hR hV
    (fun χ hχ z hz => (hbound z hz χ hχ).1) ψ hψV
  exact analyticAt_const.mul hi

/-- The actual physical Hamiltonian combination is recovered on large circles. -/
theorem exists_fourthContour_eq_physical (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sourceFullAbelianFourthContour hp hp1 W 0 R φ.val =
        sourceFiniteGapNLSHamiltonian hp hp1 φ hf 4-
          6*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2 := by
  obtain ⟨E⟩ := D.charts φ.val (D.real_subset φ.property)
  obtain ⟨T,hT,hc⟩ := exists_sourceFullAbelian_hamiltonian_fourth_contour_of_chart φ hf E
  exact ⟨T,hT,fun R hR => (hc R hR).symm⟩

end SourceFullAbelianDifferentialData
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B V W U : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The angle bracket has the exact cubic-moment factor required in Lemma 5.2. -/
theorem theta_fourthContour_eq_cubic
    (E : SourceAngularThetaCommonDomainData hp hp1 W₀ B V s)
    (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (h2p : (2:ℝ≥0∞) ≤ p) (n : ℤ) (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ.val) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s
      (sourceFullAbelianFourthContour hp hp1 W c R) φ.val =
      -(4*I/Real.pi:ℂ)*sourceAbelianMomentCircle hp hp1 W n 0 3 (s n φ.val : Coeff p) φ.val c R := by
  have hd := D.analyticAt_fourthContour c R hR φ.val hφ hcircle
  let F : CoeffPair p → ℂ := fun ψ => ∮ z in C(c,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ))^4
  have hcoef : (2*I/Real.pi:ℂ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hF : DifferentiableAt ℂ F φ.val := by
    have he : F = fun ψ => (2*I/Real.pi:ℂ)⁻¹*sourceFullAbelianFourthContour hp hp1 W c R ψ := by
      funext ψ
      simp only [sourceFullAbelianFourthContour,← mul_assoc,inv_mul_cancel₀ hcoef,one_mul]
      rfl
    rw [he]
    exact hd.differentiableAt.const_mul _
  have hder := hF.hasFDerivAt.const_smul (2*I/Real.pi:ℂ)
  change sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s φ.val)
    (fderiv ℂ ((2*I/Real.pi:ℂ) • F) φ.val) = _
  rw [hder.fderiv]
  simp only [map_smul,smul_eq_mul]
  have he := E.theta_power_circle_eq D h2p n 0 3 φ hφ hgap c R hR hcircle
  change sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s φ.val) (fderiv ℂ F φ.val) = _ at he
  rw [he]
  norm_num
  ring

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
