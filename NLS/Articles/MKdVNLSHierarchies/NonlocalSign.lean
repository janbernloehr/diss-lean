import NLS.ZakharovShabat.L2PrintedNonlocalSign
import NLS.ZakharovShabat.L2NormalizedNonlocalGradient
import NLS.ZakharovShabat.SourceReflectionBoundaryConstant
import NLS.Articles.MKdVNLSHierarchies.FullSpectralSymmetries

/-! # The nonlocal sign correction in the paper's Section 2 convention

The operator is the literal Section 2 expression, the fundamental solution
has initial matrix identity, Delta is its trace, and the unconjugated gradient
is the actual Frechet derivative. With R=diag(i,-i), xi has a negative
nonlocal integral. A concrete original H0 source refutes the printed plus
sign even almost everywhere. The corrected residual uses a positive scalar
integral times J*phi. No claim about the still-unproved xi covariance or the
primitive-gradient source interface is bundled into these statements.
-/
noncomputable section
open Set Complex Matrix MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

/-- The literal operator displayed on page 8, with no spectral reflection,
component exchange or multiplier of the discriminant gradient. -/
theorem section2_operator_convention (φ f : ℝ → ℂ × ℂ) (x : ℝ) :
    physicalOperator φ f x =
      (I*deriv (fun t => (f t).1) x+(φ x).1*(f x).2,
       -I*deriv (fun t => (f t).2) x+(φ x).2*(f x).1) := rfl

/-- The gradient used in the sign test is the actual monodromy-trace derivative. -/
theorem nonlocal_sign_actual_gradient_normalization (Φ H : Curve (ℂ × ℂ)) (z : ℂ) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalDiscriminant Ψ z) Φ) H =
      ∫ x in (0:ℝ)..1, (classicalDiscriminantGradient Φ z x).1*(extend H x).1+
        (classicalDiscriminantGradient Φ z x).2*(extend H x).2 :=
  fderiv_classicalDiscriminant_eq_gradient_integral Φ H z

theorem theorem6_v_corrected_nonlocal_integral (u : IntervalPairL2) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantXi u z x = (l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1-
      2*I*∫ t in (0:ℝ)..x,
        (I*(l2WholeLinePotential u t).1)*(l2WholeLineDiscriminantGradient u z t).1+
        (-I*(l2WholeLinePotential u t).2)*(l2WholeLineDiscriminantGradient u z t).2 :=
  l2WholeLineDiscriminantXi_eq_R_integral u z x

theorem theorem6_v_printed_nonlocal_sign_false :
    ∃ φ : CoeffPair 2,
      ¬ (∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
        HasDerivAt (l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) 0)
          (l2WholeLinePrintedDiscriminantXi (sourcePhysicalL2 φ) 0 x*(l2WholeLinePotential (sourcePhysicalL2 φ) x).2,
           -l2WholeLinePrintedDiscriminantXi (sourcePhysicalL2 φ) 0 x*(l2WholeLinePotential (sourcePhysicalL2 φ) x).1) x) :=
  exists_original_source_printed_nonlocal_sign_false

/-- The exact monodromy of the elementary sign test. -/
theorem nonlocal_sign_test_monodromy :
    classicalMonodromy classicalRationalPotential 0 =
      !![2,1+(Real.pi:ℂ)/2;1,1+(Real.pi:ℂ)/4] := classicalMonodromy_rational

theorem nonlocal_sign_test_derivatives :
    HasDerivAt (classicalDiscriminantXi classicalRationalPotential 0) (2-(Real.pi:ℂ)) 0 ∧
    HasDerivAt (classicalPrintedDiscriminantXi classicalRationalPotential 0) ((Real.pi:ℂ)-2) 0 :=
  ⟨hasDerivAt_classicalDiscriminantXi_rational_zero,
    hasDerivAt_classicalPrintedDiscriminantXi_rational_zero⟩

/-- Corollary 9(ii)'s corrected typed identity for the normalized actual
physical discriminant gradients. The still-separate primitive F interface
must identify its gradient with these normalized fields on the cut complement. -/
theorem corollary9_ii_corrected_normalized_discriminant_gradients (φ : CoeffPair 2)
    (hT : sourceMidpointReflection φ = φ ∨ sourceMidpointReflection φ = -φ) (z : ℂ) :
    ∀ᵐ x : ℝ,
      l2NormalizedNonlocalResidual (sourcePhysicalL2 φ) z
        (sourceCanonicalRoot (by simp) (by norm_num) φ z) x =
      l2NormalizedNonlocalResidual (sourcePhysicalL2 φ) (-z)
        (sourceCanonicalRoot (by simp) (by norm_num) φ (-z)) x := by
  filter_upwards [ae_l2NormalizedNonlocalResidual_eq_boundary (sourcePhysicalL2 φ) z
      (sourceCanonicalRoot (by simp) (by norm_num) φ z),
    ae_l2NormalizedNonlocalResidual_eq_boundary (sourcePhysicalL2 φ) (-z)
      (sourceCanonicalRoot (by simp) (by norm_num) φ (-z))] with x hp hm
  rw [hp,hm]
  have he := source_reflection_normalized_boundary_even φ hT z
  change sourceDiscriminantBoundaryConstant φ (-z)/_ = sourceDiscriminantBoundaryConstant φ z/_ at he
  change (sourceDiscriminantBoundaryConstant φ z/_*(l2WholeLinePotential (sourcePhysicalL2 φ) x).2,
      -sourceDiscriminantBoundaryConstant φ z/_*(l2WholeLinePotential (sourcePhysicalL2 φ) x).1) =
    (sourceDiscriminantBoundaryConstant φ (-z)/_*(l2WholeLinePotential (sourcePhysicalL2 φ) x).2,
      -sourceDiscriminantBoundaryConstant φ (-z)/_*(l2WholeLinePotential (sourcePhysicalL2 φ) x).1)
  simp only [neg_div] at *
  rw [he]

end NLS.Articles.MKdVNLSHierarchies
