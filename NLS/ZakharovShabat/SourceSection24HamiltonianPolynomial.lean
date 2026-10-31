import NLS.ZakharovShabat.ClassicalNLSHamiltonians
import NLS.ZakharovShabat.NLSRiccatiPolynomialRemainder
import NLS.DifferentialPolynomial.JetOrderBounds

/-! # The literal leading-term Hamiltonian display in Section 24 -/
noncomputable section
open MvPolynomial NLS.DifferentialPolynomial MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The canonical nonlinear Hamiltonian polynomial uses only the printed lower jets. -/
theorem section24HamiltonianRemainder_jetOrder (k : ℕ) :
    JetOrderLE (-(X (false,0)*nlsRiccatiRemainder k)) (k-1) := by
  apply JetOrderLE.of_derivativeOrder
    (nlsRiccatiRemainder_hamiltonian_grades k).2.2.neg
  omega

/-- The exact leading derivative, phase and canonical lower-order polynomial. -/
theorem classicalNLSHamiltonian_leading_polynomial (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (k : ℕ) :
    classicalNLSHamiltonian a b (k+1) = (-Complex.I)^k *
      ∫ x in (0 : ℝ)..1, a x*iteratedDeriv k b x+
        evaluate a b (-(X (false,0)*nlsRiccatiRemainder k)) x := by
  rw [classicalNLSHamiltonian,nlsRiccatiDensity_eq_leading_add_remainder a b ha hb]
  have he : (fun x => a x*(-iteratedDeriv k b+evaluate a b (nlsRiccatiRemainder k)) x) =
      (fun x => -(a x*iteratedDeriv k b x+
        evaluate a b (-(X (false,0)*nlsRiccatiRemainder k)) x)) := by
    funext x
    simp
    ring
  rw [he,intervalIntegral.integral_neg,pow_add]
  norm_num [Complex.I_sq]

/-- One source-independent polynomial gives the printed formula at every smooth pair. -/
theorem exists_classicalNLSHamiltonian_leading_polynomial (k : ℕ) :
    ∃ q : DifferentialPolynomial.Polynomial, JetOrderLE q (k-1) ∧
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
        classicalNLSHamiltonian a b (k+1) = (-Complex.I)^k *
          ∫ x in (0 : ℝ)..1, a x*iteratedDeriv k b x+evaluate a b q x :=
  ⟨_,section24HamiltonianRemainder_jetOrder k,
    fun a b ha hb => classicalNLSHamiltonian_leading_polynomial a b ha hb k⟩

end NLS.ZakharovShabat
