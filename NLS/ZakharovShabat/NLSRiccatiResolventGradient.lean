import NLS.ZakharovShabat.NLSRiccatiResolventVariation
import NLS.ZakharovShabat.ClassicalNLSHierarchyVariation
import NLS.DifferentialPolynomial.EulerScalar
import NLS.Fourier.PeriodicVariationalUniqueness

/-! # The constructed resolvent is the actual physical hierarchy gradient

The equality follows from arbitrary independent smooth periodic variations
and uniqueness of physical variational pairings. Every hierarchy order and
the existing Riccati normalization are retained.
-/
noncomputable section
open NLS.DifferentialPolynomial MvPolynomial NLS.Fourier Complex
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem evaluate_euler_nlsRiccati_density_fst (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (n : ℕ) :
    evaluate a b (eulerDerivative false (X (false,0)*nlsRiccatiPolynomial n)) =
      evaluate a b (nlsResolventCoefficientA n) := by
  apply eq_of_periodic_integral_mul_eq _ _
    (continuous_evaluate a b ha hb _) (continuous_evaluate a b ha hb _)
    (periodic_evaluate a b 1 hpa hpb _) (periodic_evaluate a b 1 hpa hpb _)
  intro h hh hph
  have he := integral_firstVariationDensity a b h 0 ha hb hh (by change ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℂ)); exact contDiff_const)
    hpa hpb hph (fun _ => rfl) (X (false,0)*nlsRiccatiPolynomial n)
  have hr := integral_firstVariationDensity_eq_resolvent a b h 0 ha hb hh (by change ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℂ)); exact contDiff_const)
    hpa hpb hph (fun _ => rfl) n
  simpa only [Pi.zero_apply, zero_mul, add_zero] using he.symm.trans hr

theorem evaluate_euler_nlsRiccati_density_snd (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (n : ℕ) :
    evaluate a b (eulerDerivative true (X (false,0)*nlsRiccatiPolynomial n)) =
      evaluate a b (nlsResolventCoefficientB n) := by
  apply eq_of_periodic_integral_mul_eq _ _
    (continuous_evaluate a b ha hb _) (continuous_evaluate a b ha hb _)
    (periodic_evaluate a b 1 hpa hpb _) (periodic_evaluate a b 1 hpa hpb _)
  intro h hh hph
  have he := integral_firstVariationDensity a b 0 h ha hb (by change ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℂ)); exact contDiff_const) hh
    hpa hpb (fun _ => rfl) hph (X (false,0)*nlsRiccatiPolynomial n)
  have hr := integral_firstVariationDensity_eq_resolvent a b 0 h ha hb (by change ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℂ)); exact contDiff_const) hh
    hpa hpb (fun _ => rfl) hph n
  simpa only [Pi.zero_apply, zero_mul, zero_add] using he.symm.trans hr

/-- Both components of the already certified physical gradient are exactly
the constructed resolvent coefficients, with the original powers of -i. -/
theorem classicalNLSHierarchyGradient_eq_resolvent (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (n : ℕ) (x : ℝ) :
    classicalNLSHierarchyGradient a b (n+1) x =
      ((-I)^(n+2)*evaluate a b (nlsResolventCoefficientA n) x,
        (-I)^(n+2)*evaluate a b (nlsResolventCoefficientB n) x) := by
  have hp : nlsHamiltonianPolynomial (n+1) =
      C ((-I)^(n+2))*(X (false,0)*nlsRiccatiPolynomial n) := by
    rw [nlsHamiltonianPolynomial, mul_assoc]
  simp only [classicalNLSHierarchyGradient, hp, eulerDerivative_C_mul,
    evaluate_mul, evaluate_C, Pi.mul_apply,
    evaluate_euler_nlsRiccati_density_fst a b ha hb hpa hpb,
    evaluate_euler_nlsRiccati_density_snd a b ha hb hpa hpb]

end NLS.ZakharovShabat
