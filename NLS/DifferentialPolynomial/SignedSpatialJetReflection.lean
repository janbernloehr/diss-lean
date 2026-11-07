import NLS.DifferentialPolynomial.JetAlgebra
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # The exact signed spatial reflection of every physical jet -/
noncomputable section
open MvPolynomial
namespace NLS.DifferentialPolynomial

def signedSpatialJetReflection (ε : ℂ) : Polynomial →ₐ[ℂ] Polynomial :=
  MvPolynomial.aeval (fun v : Jet => C (ε*(-1:ℂ)^v.2)*X v)

@[simp] theorem signedSpatialJetReflection_C (ε c : ℂ) :
    signedSpatialJetReflection ε (C c) = C c := by simp [signedSpatialJetReflection]

@[simp] theorem signedSpatialJetReflection_X (ε : ℂ) (v : Jet) :
    signedSpatialJetReflection ε (X v) = C (ε*(-1:ℂ)^v.2)*X v := by
  simp [signedSpatialJetReflection]

theorem signedSpatialJetReflection_spatialDerivative (ε : ℂ) (p : Polynomial) :
    signedSpatialJetReflection ε (spatialDerivative p) =
      (-spatialDerivative) (signedSpatialJetReflection ε p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p v hp =>
    simp only [Derivation.leibniz,smul_eq_mul,map_add,map_mul,spatialDerivative_X,
      signedSpatialJetReflection_X,Derivation.neg_apply,MvPolynomial.derivation_C,
      nextJet,pow_succ] at hp ⊢
    rw [hp]
    simp only [map_neg,map_one]
    ring

theorem evaluate_signedSpatialJetReflection (ε : ℂ) (a b : ℝ → ℂ) (p : Polynomial) (x : ℝ) :
    evaluate (fun y => ε*a (1-y)) (fun y => ε*b (1-y)) p x =
      evaluate a b (signedSpatialJetReflection ε p) (1-x) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,evaluate_add,Pi.add_apply,hp,hq]
  | mul_X p v hp =>
    simp only [map_mul,evaluate_mul,Pi.mul_apply,signedSpatialJetReflection_X,
      evaluate_C,evaluate_X,hp]
    cases h : v.1 <;>
      simp only [Bool.false_eq_true,↓reduceIte,iteratedDeriv_const_mul_field,
        iteratedDeriv_comp_const_sub,Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_neg,
        Complex.ofReal_one] <;> ring

end NLS.DifferentialPolynomial
