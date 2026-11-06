import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # First variations of multivariate polynomials in a normed algebra

The variable set may be infinite. Every formula is a finite sum over the
variables actually used by the polynomial. These rules apply in particular to
Banach algebras of continuous physical fields, so a bounded integral can be
applied after differentiation without a dominated-differentiation assumption.
-/
noncomputable section
open MvPolynomial
namespace NLS.DifferentialPolynomial

/-- A derivation is the finite sum of its generator values times the partial
derivatives, over any finite set containing all variables of the input. -/
theorem mkDerivation_eq_sum_pderiv {σ R : Type*} [CommSemiring R]
    (V : σ → MvPolynomial σ R) (p : MvPolynomial σ R) (S : Finset σ)
    (hp : p.vars ⊆ S) :
    MvPolynomial.mkDerivation R V p = ∑ i ∈ S, V i * pderiv i p := by
  classical
  have hsum (s : Finset σ) (q : MvPolynomial σ R) :
      (∑ i ∈ s, V i • pderiv i) q = ∑ i ∈ s, V i * pderiv i q := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply,
        Derivation.smul_apply, smul_eq_mul, ih]
  let D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
    ∑ i ∈ S, V i • pderiv i
  have he : MvPolynomial.mkDerivation R V p = D p := by
    apply MvPolynomial.derivation_eq_of_forall_mem_vars
    intro i hi
    rw [MvPolynomial.mkDerivation_X]
    change V i = (∑ j ∈ S, V j • pderiv j) (X i)
    rw [hsum]
    simp [MvPolynomial.pderiv_X, Pi.single_apply, hp hi]
  simpa only [D, hsum] using he

/-- Differentiate algebra evaluation using a formal derivation with constant
generator values. No finite-dimensional coordinate space is introduced. -/
theorem hasDerivAt_eval_mvPolynomial {σ B : Type*} [NormedCommRing B] [NormedAlgebra ℂ B]
    (f : ℂ → σ → B) (V : σ → B) (z : ℂ)
    (hf : ∀ i, HasDerivAt (fun w => f w i) (V i) z) (p : MvPolynomial σ B) :
    HasDerivAt (fun w => MvPolynomial.eval (f w) p)
      (MvPolynomial.eval (f z) (MvPolynomial.mkDerivation B (fun i => C (V i)) p)) z := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const z c
  | add p q hp hq => simpa only [map_add] using! HasDerivAt.fun_add hp hq
  | mul_X p i hp =>
    have h := hp.mul (hf i)
    convert! h using 1
    · simp only [map_mul, MvPolynomial.eval_X, Pi.mul_def]
    · simp only [Derivation.leibniz, MvPolynomial.mkDerivation_X,
        smul_eq_mul, map_add, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
      ring

/-- The explicit partial-derivative first variation in an arbitrary normed
complex algebra, with the polynomial's original complex coefficients. -/
theorem hasDerivAt_aeval_mvPolynomial {σ B : Type*} [NormedCommRing B] [NormedAlgebra ℂ B]
    (f : ℂ → σ → B) (V : σ → B) (z : ℂ)
    (hf : ∀ i, HasDerivAt (fun w => f w i) (V i) z) (p : MvPolynomial σ ℂ) :
    HasDerivAt (fun w => MvPolynomial.aeval (f w) p)
      (∑ i ∈ p.vars, V i * MvPolynomial.aeval (f z) (pderiv i p)) z := by
  classical
  have h := hasDerivAt_eval_mvPolynomial f V z hf (MvPolynomial.map (algebraMap ℂ B) p)
  rw [mkDerivation_eq_sum_pderiv _ _ p.vars (MvPolynomial.vars_map _ _)] at h
  simpa only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map,
    map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.pderiv_map] using h

end NLS.DifferentialPolynomial
