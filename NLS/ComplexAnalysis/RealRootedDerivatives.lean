import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Derivatives of polynomials with real roots

Gauss–Lucas confines derivative roots to the real axis whenever every root of
a nonconstant polynomial is real. Finite products may include repeated roots.
-/

noncomputable section
open Complex Polynomial
namespace NLS.ComplexAnalysis

/-- Every critical point of a nonconstant polynomial with real roots is real. -/
theorem polynomial_derivative_im_eq_zero {P : Polynomial ℂ} (hP : 0 < P.degree)
    (hreal : ∀ w : ℂ, P.eval w = 0 → w.im = 0) {z : ℂ}
    (hz : P.derivative.eval z = 0) : z.im = 0 := by
  classical
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  rw [Polynomial.eq_centerMass_of_eval_derivative_eq_zero hP hz]
  simp only [Finset.centerMass, Complex.smul_im, Complex.im_sum, id_eq]
  have hs : ∑ w ∈ P.roots.toFinset, P.derivRootWeight z w • w.im = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [hreal w ((Polynomial.mem_roots hP0).mp (Multiset.mem_toFinset.mp hw)), smul_zero]
  rw [hs, smul_zero]

/-- A finite product of real linear factors with positive total degree has no nonreal critical points. -/
theorem deriv_prod_real_factors_ne_zero (s : Finset ℂ) (m : ℂ → ℕ)
    (hreal : ∀ a ∈ s, a.im = 0) (hpos : ∃ a ∈ s, 0 < m a)
    {z : ℂ} (hz : z.im ≠ 0) : deriv (fun w => ∏ a ∈ s, (a-w)^(m a)) z ≠ 0 := by
  classical
  let P : Polynomial ℂ := ∏ a ∈ s, (Polynomial.C a-Polynomial.X)^(m a)
  have he (w : ℂ) : P.eval w = ∏ a ∈ s, (a-w)^(m a) := by simp [P, Polynomial.eval_prod]
  have hP0 : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    apply pow_ne_zero
    exact sub_ne_zero.mpr (Ne.symm (Polynomial.X_ne_C a))
  obtain ⟨a, ha, hma⟩ := hpos
  have hPa : P.eval a = 0 := by
    rw [he]
    apply Finset.prod_eq_zero ha
    simp [Nat.ne_of_gt hma]
  have hdeg := Polynomial.degree_pos_of_root hP0 hPa
  have hroots (w : ℂ) (hw : P.eval w = 0) : w.im = 0 := by
    rw [he] at hw
    obtain ⟨b, hb, hb0⟩ := Finset.prod_eq_zero_iff.mp hw
    have hbw : b = w := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hb0)
    exact hbw ▸ hreal b hb
  have hefun : (fun w => ∏ a ∈ s, (a-w)^(m a)) = P.eval := (funext he).symm
  rw [hefun, P.deriv]
  exact fun h => hz (polynomial_derivative_im_eq_zero hdeg hroots h)

end NLS.ComplexAnalysis
