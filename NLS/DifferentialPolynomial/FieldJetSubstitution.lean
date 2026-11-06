import NLS.DifferentialPolynomial.EulerLagrange
import NLS.DifferentialPolynomial.RiccatiResolventNaturality

/-! # Differential polynomial substitution of complete physical jet fields

Substituting a field substitutes all of its spatial derivatives as well.
The resulting algebra map commutes with the original spatial derivation
and agrees with actual smooth physical evaluation.
-/
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped ContDiff
namespace NLS.DifferentialPolynomial

/-- Substitute both fields together with every spatial jet. -/
def fieldJetSubstitution (V : Bool → Polynomial) : Polynomial →ₐ[ℂ] Polynomial :=
  MvPolynomial.aeval (fun v : Jet => ((spatialDerivative : Polynomial → Polynomial)^[v.2]) (V v.1))

@[simp] theorem fieldJetSubstitution_X (V : Bool → Polynomial) (v : Jet) :
    fieldJetSubstitution V (X v) = ((spatialDerivative : Polynomial → Polynomial)^[v.2]) (V v.1) := by
  simp [fieldJetSubstitution]

/-- Actual jet substitution commutes with spatial differentiation. -/
theorem fieldJetSubstitution_spatialDerivative (V : Bool → Polynomial) (P : Polynomial) :
    fieldJetSubstitution V (spatialDerivative P) = spatialDerivative (fieldJetSubstitution V P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [fieldJetSubstitution]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P v hP =>
    simp only [Derivation.leibniz,smul_eq_mul,map_add,map_mul,spatialDerivative_X,
      fieldJetSubstitution_X,hP,nextJet,Function.iterate_succ_apply']

/-- Substitution evaluates to the literal substituted smooth physical fields. -/
theorem evaluate_fieldJetSubstitution (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (V : Bool → Polynomial) (P : Polynomial) :
    evaluate a b (fieldJetSubstitution V P) =
      evaluate (evaluate a b (V false)) (evaluate a b (V true)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [fieldJetSubstitution]
  | add P Q hP hQ => simp only [map_add,evaluate_add,hP,hQ]
  | mul_X P v hP =>
    rw [map_mul,fieldJetSubstitution_X,evaluate_mul,evaluate_mul,hP,
      evaluate_X,evaluate_iterate_spatialDerivative a b ha hb]
    cases v with
    | mk field k => cases field <;> rfl

/-- The independent scalar recurrence is natural under substitution of a
potential polynomial and all its original spatial derivatives. -/
theorem fieldJetSubstitution_scalarRiccati (V : Bool → Polynomial) (n : ℕ) :
    fieldJetSubstitution V (differentialRiccatiSequence spatialDerivative 1 (X (false,0)) n) =
      differentialRiccatiSequence spatialDerivative 1 (V false) n := by
  have he := map_differentialRiccatiSequence spatialDerivative spatialDerivative
    (fieldJetSubstitution V).toRingHom (fieldJetSubstitution_spatialDerivative V) 1 (X (false,0)) n
  change fieldJetSubstitution V _ = differentialRiccatiSequence spatialDerivative
    (fieldJetSubstitution V 1) (fieldJetSubstitution V (X (false,0))) n at he
  simpa only [map_one,fieldJetSubstitution_X,Function.iterate_zero,Function.id_def] using he

end NLS.DifferentialPolynomial
