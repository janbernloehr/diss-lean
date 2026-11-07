import NLS.ZakharovShabat.SourceDirichletTerminalSequence
import NLS.ZakharovShabat.SourceGapWeightedEtaFiniteGapDifferential
import NLS.SequenceSpaces.BoundedScalarProducts

/-! The derivative of the literal spectral terminal at every complex
source in the original domain. The inverse-product derivative is kept,
so this formula also applies at open gaps. -/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The full terminal cotangent equals the closed-gap expression plus
its actual inverse omitted-product correction, without dividing by a gap. -/
theorem gapWeightedEtaTerminalCoordinate_fderiv (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (n : ℤ) (sign : ℂ) :
    fderiv ℂ (sourceGapWeightedEtaTerminalCoordinate hp hp1 n sign) φ =
      sourceGapWeightedEtaClosedCotangent hp hp1 n sign φ-
        (sign*I*sourceAntiDiscriminantCandidate hp hp1 φ
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n)) •
          fderiv ℂ (fun ψ : CoeffPair p => (sourceStandardRootOmittedProduct hp hp1 n ψ
            (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))⁻¹) φ := by
  let D := H.original_theta_common_domain
  let μ := fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
  let τ := fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let O := fun ψ : CoeffPair p => sourceStandardRootOmittedProduct hp hp1 n ψ (μ ψ)
  let A := fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ (μ ψ)
  let B := fun ψ : CoeffPair p => (O ψ)⁻¹
  have hμ : DifferentiableAt ℂ μ φ :=
    (D.roots_analytic .dirichlet n φ (D.source_subset hφ)).differentiableAt
  have hτ : DifferentiableAt ℂ τ φ :=
    (D.symmetric_analytic φ (D.source_subset hφ) n).1.differentiableAt
  have hA : DifferentiableAt ℂ A φ :=
    ((analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1 _ (mem_univ _)).comp
      (f := fun ψ : CoeffPair p => (μ ψ,ψ))
      ((D.roots_analytic .dirichlet n φ (D.source_subset hφ)).prod analyticAt_id)).differentiableAt
  have hB : DifferentiableAt ℂ B φ :=
    (H.dirichlet_omitted_sample_data φ hφ n).2.differentiableAt.inv
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 φ (μ φ) n
        (H.dirichlet_omitted_sample_data φ hφ n).1)
  have hd := (((hμ.hasFDerivAt.sub hτ.hasFDerivAt).add
    ((hA.hasFDerivAt.fun_mul hB.hasFDerivAt).const_mul (sign*I/2))).const_mul (-2)).fderiv
  have heq : (fun ψ => -2*(μ ψ-τ ψ+(sign*I/2)*(A ψ*B ψ))) =
      sourceGapWeightedEtaTerminalCoordinate hp hp1 n sign := by
    funext ψ
    simp only [sourceGapWeightedEtaTerminalCoordinate,sourceDirichletEtaSineNumerator,
      μ,τ,A,B,O,div_eq_mul_inv,mul_inv_rev]
    ring
  simp only [Pi.add_apply,Pi.sub_apply] at hd
  rw [heq] at hd
  have hDA : fderiv ℂ A φ =
      sourceAntiDiscriminantCotangent hp hp1 (μ φ) φ+
        deriv (sourceAntiDiscriminantCandidate hp hp1 φ) (μ φ) • fderiv ℂ μ φ :=
    NLS.ComplexAnalysis.fderiv_moving_spectral_parameter
      (fun t : ℂ × CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 t.2 t.1)
      μ φ (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1 _ (mem_univ _)).differentiableAt hμ
  rw [hd,hDA]
  ext h
  simp only [sourceGapWeightedEtaClosedCotangent,μ,τ,A,B,O,add_apply,sub_apply,
    smul_apply,smul_eq_mul,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Evaluation of the actual sequence derivative gives the full scalar cotangent. -/
theorem gapWeightedEtaTerminalSequence_fderiv_apply (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ h : CoeffPair p) (hφ : φ ∈ W) (n : ℤ) (sign : ℂ) :
    (fderiv ℂ (sourceGapWeightedEtaTerminalSequence hp hp1 sign) φ) h n =
      (fderiv ℂ (sourceGapWeightedEtaTerminalCoordinate hp hp1 n sign) φ) h := by
  rw [Coeff.fderiv_apply_of_differentiableAt _ _ _ _
    (H.gapWeightedEtaTerminalSequence_analytic sign φ hφ).differentiableAt]
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [H.original_theta_common_domain.source_open.mem_nhds hφ] with ψ hψ
  exact H.gapWeightedEtaTerminalSequence_apply ψ hψ n sign

/-- Evaluation commutes with the full bounded-sequence derivative. -/
theorem dirichlet_omitted_inverse_symbol_fderiv_apply (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ h : CoeffPair p) (hφ : φ ∈ W) (n : ℤ) :
    (fderiv ℂ (sourceDirichletOmittedInverseSymbol hp hp1) φ) h n =
      (fderiv ℂ (fun ψ : CoeffPair p => (sourceStandardRootOmittedProduct hp hp1 n ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))⁻¹) φ) h := by
  rw [Coeff.fderiv_apply_of_differentiableAt _ _ _ _
    (H.dirichlet_omitted_inverse_symbol_analytic φ hφ).differentiableAt]
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [H.original_theta_common_domain.source_open.mem_nhds hφ] with ψ hψ
  exact H.dirichlet_omitted_inverse_symbol_apply ψ hψ n

/-- All inverse-product cotangents have one bound in the full original
source norm, including the central block. -/
theorem dirichlet_omitted_inverse_cotangents_bounded (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ,
      ‖fderiv ℂ (fun ψ : CoeffPair p => (sourceStandardRootOmittedProduct hp hp1 n ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))⁻¹) φ‖ ≤ C := by
  refine ⟨‖fderiv ℂ (sourceDirichletOmittedInverseSymbol hp hp1) φ‖,norm_nonneg _,?_⟩
  intro n
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro h
  rw [← H.dirichlet_omitted_inverse_symbol_fderiv_apply φ h hφ n]
  exact (lp.norm_apply_le_norm (by simp) _ n).trans
    ((fderiv ℂ (sourceDirichletOmittedInverseSymbol hp hp1) φ).le_opNorm h)

/-- The extra cotangent at open gaps has outer ℓp operator norms.
The actual anti-discriminant samples supply the summable factor. -/
theorem memlp_gapWeightedEtaTerminalCoordinate_fderiv_sub_closed
    (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (sign : ℂ) :
    Memℓp (fun n : ℤ =>
      fderiv ℂ (sourceGapWeightedEtaTerminalCoordinate hp hp1 n sign) φ-
        sourceGapWeightedEtaClosedCotangent hp hp1 n sign φ) p := by
  obtain ⟨C,_,hC⟩ := H.dirichlet_omitted_inverse_cotangents_bounded φ hφ
  have hm := (memlp_smul_of_bounded_vector
    (fun n => sourceAntiDiscriminantCandidate hp hp1 φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n))
    (fun n => fderiv ℂ (fun ψ : CoeffPair p => (sourceStandardRootOmittedProduct hp hp1 n ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))⁻¹) φ)
    (memℓp_sourceAntiDiscriminant_at_dirichletRoots hp hp1 φ).1 C hC).const_smul (-sign*I)
  convert hm using 1
  funext n
  rw [H.gapWeightedEtaTerminalCoordinate_fderiv φ hφ n sign]
  ext h
  simp only [sub_apply,smul_apply,smul_eq_mul,Pi.smul_apply]
  ring

end SourceLemma12_12Data
end NLS.ZakharovShabat
