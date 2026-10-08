import NLS.ZakharovShabat.NLSRiccatiPolynomials

/-! # The nonlinear remainder in Appendix H, Lemma H.1

The leading jet is separated at every order. The remaining polynomial has
homogeneous total weight, the required field balance, and at most n-2 spatial
derivatives in each monomial. Evaluation gives the actual classical density.
-/
noncomputable section
open MvPolynomial NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The nonlinear remainder after removing the leading term -b^(n). -/
def nlsRiccatiRemainder (n : ℕ) : DifferentialPolynomial.Polynomial :=
  nlsRiccatiPolynomial n + X (true,n)

@[simp] theorem nlsRiccatiRemainder_zero : nlsRiccatiRemainder 0 = 0 := by
  simp [nlsRiccatiRemainder]

@[simp] theorem nlsRiccatiRemainder_one : nlsRiccatiRemainder 1 = 0 := by
  simp [nlsRiccatiRemainder]

theorem nlsRiccatiRemainder_succ_succ (n : ℕ) :
    nlsRiccatiRemainder (n+2) = spatialDerivative (nlsRiccatiRemainder (n+1)) + X (false,0) *
      ∑ ij ∈ (Finset.antidiagonal n).attach,
        nlsRiccatiPolynomial ij.val.1*nlsRiccatiPolynomial ij.val.2 := by
  simp only [nlsRiccatiRemainder,nlsRiccatiPolynomial_succ_succ,map_add,spatialDerivative_X,nextJet]
  ring

/-- Appendix H's leading derivative and nonlinear polynomial identity. -/
theorem nlsRiccatiDensity_eq_leading_add_remainder (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (n : ℕ) :
    nlsRiccatiDensity a b n = -iteratedDeriv n b + evaluate a b (nlsRiccatiRemainder n) := by
  rw [nlsRiccatiRemainder,evaluate_add,evaluate_X,evaluate_nlsRiccatiPolynomial a b ha hb]
  simp

theorem nlsRiccatiRemainder_totalWeight (n : ℕ) :
    (nlsRiccatiRemainder n).IsWeightedHomogeneous totalWeight (n+1) :=
  (nlsRiccatiPolynomial_totalWeight n).add
    (by simpa [totalWeight] using isWeightedHomogeneous_X (R := ℂ) totalWeight (true,n))

theorem nlsRiccatiRemainder_fieldCharge (n : ℕ) :
    (nlsRiccatiRemainder n).IsWeightedHomogeneous fieldCharge 1 :=
  (nlsRiccatiPolynomial_fieldCharge n).add
    (by simpa [fieldCharge] using isWeightedHomogeneous_X (R := ℂ) fieldCharge (true,n))

/-- The total derivative order of every nonlinear monomial is at most n-2.
The negative bounds at n=0 and n=1 correctly describe the zero remainder. -/
theorem nlsRiccatiRemainder_derivativeOrder (n : ℕ) :
    DerivativeOrderLE (nlsRiccatiRemainder n) ((n:ℤ)-2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [nlsRiccatiRemainder_zero]
      exact DerivativeOrderLE.zero _
    · rw [nlsRiccatiRemainder_one]
      exact DerivativeOrderLE.zero _
    · rw [nlsRiccatiRemainder_succ_succ]
      apply DerivativeOrderLE.add
      · convert (ih (n+1) (by omega)).spatialDerivative using 1
        push_cast
        ring
      · have hs : DerivativeOrderLE (∑ ij ∈ (Finset.antidiagonal n).attach,
            nlsRiccatiPolynomial ij.val.1*nlsRiccatiPolynomial ij.val.2) n := by
          apply DerivativeOrderLE.sum
          intro ij _
          have hij := Finset.mem_antidiagonal.mp ij.property
          convert (nlsRiccatiPolynomial_derivativeOrder ij.val.1).mul
            (nlsRiccatiPolynomial_derivativeOrder ij.val.2) using 1
          omega
        convert (DerivativeOrderLE.X (false,0)).mul hs using 1
        push_cast
        ring

/-- Multiplication by the first field gives precisely the balanced nonlinear
Hamiltonian density described in Lemma H.1. -/
theorem nlsRiccatiRemainder_hamiltonian_grades (n : ℕ) :
    (X (false,0)*nlsRiccatiRemainder n).IsWeightedHomogeneous totalWeight (n+2) ∧
    (X (false,0)*nlsRiccatiRemainder n).IsWeightedHomogeneous fieldCharge 0 ∧
    DerivativeOrderLE (X (false,0)*nlsRiccatiRemainder n) ((n:ℤ)-2) := by
  refine ⟨?_,?_,?_⟩
  · convert (isWeightedHomogeneous_X (R := ℂ) totalWeight (false,0)).mul
      (nlsRiccatiRemainder_totalWeight n) using 1
    simp only [totalWeight]
    ring
  · simpa [fieldCharge] using (isWeightedHomogeneous_X (R := ℂ) fieldCharge (false,0)).mul
      (nlsRiccatiRemainder_fieldCharge n)
  · simpa using (DerivativeOrderLE.X (false,0)).mul (nlsRiccatiRemainder_derivativeOrder n)

/-- No individual derivative in the nonlinear remainder exceeds order n-2. -/
theorem nlsRiccatiRemainder_jet_order (n : ℕ) (m : DifferentialPolynomial.Monomial)
    (hm : m ∈ (nlsRiccatiRemainder n).support) (v : Jet) (hv : v ∈ m.support) :
    (v.2 : ℤ) ≤ (n:ℤ)-2 :=
  (nlsRiccatiRemainder_derivativeOrder n).jet_order m hm v hv

/-- The remainder polynomial uses only jets through order n-2. -/
theorem nlsRiccatiRemainder_vars (n : ℕ) (v : Jet)
    (hv : v ∈ (nlsRiccatiRemainder n).vars) : (v.2 : ℤ) ≤ (n:ℤ)-2 := by
  obtain ⟨m,hm,hvm⟩ := (MvPolynomial.mem_vars_iff_mem_support v).mp hv
  exact nlsRiccatiRemainder_jet_order n m hm v hvm

/-- All three structural restrictions apply to every nonzero monomial,
including at arbitrarily high Hamiltonian order. -/
theorem nlsRiccatiRemainder_hamiltonian_monomial (n : ℕ) (m : DifferentialPolynomial.Monomial)
    (hm : (X (false,0)*nlsRiccatiRemainder n).coeff m ≠ 0) :
    Finsupp.weight totalWeight m = (n:ℤ)+2 ∧
    Finsupp.weight fieldCharge m = 0 ∧
    Finsupp.weight derivativeWeight m ≤ (n:ℤ)-2 := by
  obtain ⟨hw,hc,hd⟩ := nlsRiccatiRemainder_hamiltonian_grades n
  exact ⟨hw hm,hc hm,hd m (MvPolynomial.mem_support_iff.mpr hm)⟩

end NLS.ZakharovShabat
