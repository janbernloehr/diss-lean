import NLS.ZakharovShabat.SourceBirkhoffOriginalJacobian
import NLS.ZakharovShabat.SourceDirichletSpectralVectorField

/-!
# The auxiliary quotient in the closed-gap differential

The positive literal quotient product divided by the actual psi numerator
equals minus the inverse of twice the omitted standard-root product.
This gives an analytic extension on the original angular domain. At every
real source its psi denominator is nonzero, so the literal quotient agrees.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Corrected auxiliary phi, extended without dividing by the psi numerator. -/
def sourceGapWeightedEtaAuxiliary (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) : ℂ :=
  -(2 * sourceStandardRootOmittedProduct hp hp1 n ψ
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))⁻¹

/-- Cancellation of the actual numerator identifies the positive product quotient. -/
theorem sourceGapWeightedEtaAuxiliary_eq_quotient (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (a : Coeff p)
    (ha : sourcePsiCandidate n
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n,a) ≠ 0) :
    sourceGapWeightedEtaAuxiliary hp hp1 n ψ =
      sourceSingleRootQuotientJointProduct hp hp1 n
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n,(a,ψ)) /
        sourcePsiCandidate n (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n,a) := by
  let A := jointDeletedSingleSpectralProduct n
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n,a)
  let P := sourceStandardRootOmittedProduct hp hp1 n ψ
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
  have hA : A ≠ 0 := by
    intro h
    apply ha
    change -2 * A = 0
    rw [h,mul_zero]
  change -(2*P)⁻¹ = (A/P)/(-2*A)
  by_cases hP : P = 0
  · simp [hP]
  · field_simp

/-- The corrected auxiliary has the signed free leading term at every real source. -/
theorem memlp_sourceGapWeightedEtaAuxiliary_sub_free (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) :
    Memℓp (fun n => 2*sourceGapWeightedEtaAuxiliary hp hp1 n φ.val+
      cos ((Real.pi : ℂ)*n)) p := by
  have h := (memlp_sourceStandardRootOmittedProduct_boundary_inv_sub_free
    hp hp1 .dirichlet φ.val φ.property).neg
  convert h using 1
  funext n
  simp only [sourceGapWeightedEtaAuxiliary,mul_inv_rev,Pi.neg_apply]
  ring

namespace SourceSection15OriginalData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The extended auxiliary is analytic throughout the original angular domain. -/
theorem auxiliary_analytic (D : SourceSection15OriginalData hp hp1 W₀ W V s) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceGapWeightedEtaAuxiliary hp hp1 n) W := by
  intro ψ hψ
  obtain ⟨U,c,T,r,R,z₀,hψU,E,_⟩ := D.previous.angular_original_annulus_chart ψ hψ n
  let μ := fun χ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet χ n
  let P := fun χ : CoeffPair p => sourceStandardRootOmittedProduct hp hp1 n χ (μ χ)
  have hμball := (E.disc_family ψ hψU).dirichlet_mem_ball n
  have hμ := D.previous.original_theta_common_domain.roots_analytic .dirichlet n ψ hψ
  have hPa : AnalyticAt ℂ P ψ := (E.omitted_analytic (μ ψ,ψ) ⟨hμball,hψU⟩).comp
    (f := fun χ : CoeffPair p => (μ χ,χ)) (hμ.prod analyticAt_id)
  have hPne : P ψ ≠ 0 := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ (μ ψ) n
    (((E.disc_family ψ hψU).contour_family.2 n).2.2.1 (ball_subset_closedBall hμball))
  exact ((analyticAt_const.mul hPa).inv (mul_ne_zero (by norm_num) hPne)).neg

/-- On all real sources the extension is the actual normalized-root quotient. -/
theorem auxiliary_eq_real_quotient (D : SourceSection15OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceGapWeightedEtaAuxiliary hp hp1 n φ.val =
      sourceSingleRootQuotientJointProduct hp hp1 n
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n,((s n φ.val : Coeff p),φ.val)) /
        sourcePsiCandidate n (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n,
          (s n φ.val : Coeff p)) :=
  sourceGapWeightedEtaAuxiliary_eq_quotient hp hp1 n φ.val _
    (D.previous.angular_extension.toSourcePsiIsolatingComplexExtension.numerator_at_own_dirichletRoot_ne_zero
      n ⟨φ.val,φ.property⟩)

/-- Equation (3.3) at real collapsed gaps, using the corrected auxiliary.
Both moving-terminal terms carry the same sign; the delta times dphi term vanishes. -/
theorem equation3_3 (D : SourceSection15OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0)
    (sign : ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n
    let dμ := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) φ.val
    let dτ := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ.val
    fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) φ.val =
      (2 : ℂ) • (dτ-dμ) + (sign*I) •
        ((2*sourceAntiDiscriminantCandidate hp hp1 φ.val μ) •
          fderiv ℂ (sourceGapWeightedEtaAuxiliary hp hp1 n) φ.val +
        (2*sourceGapWeightedEtaAuxiliary hp hp1 n φ.val) •
          (sourceAntiDiscriminantCotangent hp hp1 μ φ.val +
            deriv (sourceAntiDiscriminantCandidate hp hp1 φ.val) μ • dμ)) := by
  dsimp only
  rw [D.previous.original_theta_common_domain.toSourceAngularEtaLocalCommonDomainData.gapWeightedEta_fderiv_closed
    W D.previous.original_theta_common_domain.source_open Subset.rfl φ
    (D.previous.original_theta_common_domain.real_subset φ.property) n hgap sign]
  rw [sourceAntiDiscriminant_at_canonicalBoundaryRoot_eq_zero_of_collapsed_gap hp hp1
    .dirichlet φ.val φ.property n hgap]
  ext h
  simp only [sourceGapWeightedEtaClosedCotangent,sourceGapWeightedEtaAuxiliary,
    add_apply,sub_apply,smul_apply,
    smul_eq_mul,mul_zero,zero_mul,zero_add,div_eq_mul_inv]
  ring

end SourceSection15OriginalData
end NLS.ZakharovShabat
