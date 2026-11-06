import NLS.ZakharovShabat.SobolevHierarchyGradient

/-! # Even Hamiltonian densities at their sharp Sobolev jet order

Integration by parts lowers the density of H_(2m) to jets through m while
retaining its strict bound of 2m-1 on total derivatives. Consequently each
monomial has at most one top-order factor.
-/
noncomputable section
open MvPolynomial Complex NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem nlsHamiltonianPolynomial_totalWeight (n : ℕ) :
    (nlsHamiltonianPolynomial (n+1)).IsWeightedHomogeneous totalWeight ((n : ℤ)+2) := by
  have he := ((isWeightedHomogeneous_X (R := ℂ) totalWeight (false,0)).mul
    (nlsRiccatiPolynomial_totalWeight n)).C_mul ((-I)^(n+2))
  convert he using 1 <;> simp [nlsHamiltonianPolynomial, mul_assoc, totalWeight]
  ring

theorem nlsHamiltonianPolynomial_fieldCharge (n : ℕ) :
    (nlsHamiltonianPolynomial (n+1)).IsWeightedHomogeneous fieldCharge 0 := by
  have he := ((isWeightedHomogeneous_X (R := ℂ) fieldCharge (false,0)).mul
    (nlsRiccatiPolynomial_fieldCharge n)).C_mul ((-I)^(n+2))
  simpa [nlsHamiltonianPolynomial, mul_assoc, fieldCharge] using he

theorem exists_nlsEvenHamiltonian_jet_reduction (m : ℕ) (hm : 1 ≤ m) :
    HasJetReduction (m+1) (2*(m : ℤ)+1) 0 (2*(m : ℤ)-1)
      (nlsHamiltonianPolynomial (2*m)) := by
  obtain ⟨k,hk⟩ := exists_jetOrderLE (nlsHamiltonianPolynomial (2*m))
  apply hasJetReduction_of_jetOrder (m+1) (by omega) _ _ _ (by push_cast; omega)
    k _ hk
  · have hidx : 2*m-1+1 = 2*m := by omega
    have hdeg : ((2*m-1 : ℕ) : ℤ)+2 = 2*(m : ℤ)+1 := by omega
    simpa only [hidx, hdeg] using nlsHamiltonianPolynomial_totalWeight (2*m-1)
  · have hidx : 2*m-1+1 = 2*m := by omega
    simpa only [hidx] using nlsHamiltonianPolynomial_fieldCharge (2*m-1)
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using nlsHamiltonianPolynomial_derivativeOrder (2*m)

/-- A single reduced density, chosen before any fields, has the endpoint
jet bounds and the actual integral of the original physical Hamiltonian. -/
theorem exists_classicalNLSHamiltonian_even_reduced_polynomial (m : ℕ) (hm : 1 ≤ m) :
    ∃ q : DifferentialPolynomial.Polynomial, JetOrderLE q m ∧
      DerivativeOrderLE q (2*(m : ℤ)-1) ∧
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
        Function.Periodic a 1 → Function.Periodic b 1 →
        classicalNLSHamiltonian a b (2*m) = ∫ x in (0 : ℝ)..1, evaluate a b q x := by
  obtain ⟨q,r,he,hq,_,_,hd⟩ := exists_nlsEvenHamiltonian_jet_reduction m hm
  refine ⟨q, by simpa using hq, hd, ?_⟩
  intro a b ha hb hpa hpb
  rw [← integral_evaluate_nlsHamiltonianPolynomial a b ha hb]
  exact integral_evaluate_eq_of_total_derivative a b ha hb hpa hpb _ q r he

end NLS.ZakharovShabat
