import NLS.DifferentialPolynomial.PolynomialVariation

/-! # An algebraic chain rule for coefficient derivations -/
noncomputable section
open MvPolynomial
namespace NLS.DifferentialPolynomial

theorem derivation_aeval_mvPolynomial {σ A : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (f : σ → A) (p : MvPolynomial σ ℂ) :
    D (MvPolynomial.aeval f p) =
      ∑ i ∈ p.vars, D (f i) * MvPolynomial.aeval f (pderiv i p) := by
  classical
  have h (q : MvPolynomial σ ℂ) :
      D (MvPolynomial.aeval f q) = MvPolynomial.eval f
        (MvPolynomial.mkDerivation A (fun i => C (D (f i)))
          (q.map (algebraMap ℂ A))) := by
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.map_X, Derivation.leibniz,
        MvPolynomial.mkDerivation_X, smul_eq_mul, map_add, MvPolynomial.eval_X,
        MvPolynomial.eval_C, hp]
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  have he := h p
  rw [mkDerivation_eq_sum_pderiv _ _ p.vars (MvPolynomial.vars_map _ _)] at he
  simpa only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map, map_sum, map_mul,
    MvPolynomial.eval_C, MvPolynomial.pderiv_map] using he

end NLS.DifferentialPolynomial
