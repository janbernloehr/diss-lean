import NLS.MKdV.SobolevMiuraHillHamiltonian

/-! # Removing the linear total derivative from the scalar Hill densities

The Riccati coefficient of index n has linear term -u^(n+1). Removing this
total derivative lowers its total-derivative bound from n+1 to n. This is
the endpoint gain needed to construct K_(s+1) on H^s.
-/
noncomputable section
open MvPolynomial Complex NLS.DifferentialPolynomial NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.MKdV

def miuraHillRiccatiRemainder (n : ℕ) : DifferentialPolynomial.Polynomial :=
  miuraHillRiccatiPolynomial n+X (false,n+1)

theorem miuraHillRiccatiRemainder_zero :
    miuraHillRiccatiRemainder 0 = -X (false,0)^2 := by
  simp [miuraHillRiccatiRemainder,miuraHillRiccatiPolynomial,miuraHillPotentialPolynomial]

theorem miuraHillRiccatiRemainder_one :
    miuraHillRiccatiRemainder 1 = spatialDerivative (miuraHillRiccatiRemainder 0) := by
  simp only [miuraHillRiccatiRemainder,miuraHillRiccatiPolynomial,
    differentialRiccatiSequence_one,differentialRiccatiSequence_zero,
    map_add,spatialDerivative_X,nextJet]

theorem miuraHillRiccatiRemainder_recurrence (n : ℕ) :
    miuraHillRiccatiRemainder (n+2) = spatialDerivative (miuraHillRiccatiRemainder (n+1)) +
      ∑ ij ∈ Finset.antidiagonal n, miuraHillRiccatiPolynomial ij.1*miuraHillRiccatiPolynomial ij.2 := by
  simp only [miuraHillRiccatiRemainder,miuraHillRiccatiPolynomial,
    differentialRiccatiSequence_recurrence,one_mul,map_add,spatialDerivative_X,nextJet]
  ring

theorem miuraHillRiccatiRemainder_derivativeOrder (n : ℕ) :
    DerivativeOrderLE (miuraHillRiccatiRemainder n) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [miuraHillRiccatiRemainder_zero,pow_two]
      exact ((DerivativeOrderLE.X (false,0)).mul (DerivativeOrderLE.X (false,0))).neg
    · rw [miuraHillRiccatiRemainder_one]
      exact (ih 0 (by omega)).spatialDerivative
    · rw [miuraHillRiccatiRemainder_recurrence]
      apply DerivativeOrderLE.add
      · exact ((ih (n+1) (by omega)).spatialDerivative).mono (by push_cast; omega)
      · apply DerivativeOrderLE.sum
        intro ij hij
        have he := Finset.mem_antidiagonal.mp hij
        exact ((miuraHillRiccatiPolynomial_derivativeOrder ij.1).mul
          (miuraHillRiccatiPolynomial_derivativeOrder ij.2)).mono (by push_cast; omega)

def miuraHillNativeDensity (s : ℕ) : DifferentialPolynomial.Polynomial :=
  C ((-1 : ℂ)^(s+1)/2)*miuraHillRiccatiRemainder (2*s)

theorem miuraHillNativeDensity_derivativeOrder (s : ℕ) :
    DerivativeOrderLE (miuraHillNativeDensity s) (2*(s : ℤ)) := by
  simpa only [miuraHillNativeDensity,zero_add,Nat.cast_mul,Nat.cast_ofNat] using
    (DerivativeOrderLE.C ((-1 : ℂ)^(s+1)/2)).mul (miuraHillRiccatiRemainder_derivativeOrder (2*s))

theorem miuraHillNativeDensity_eq (s : ℕ) :
    miuraHillNativeDensity s = miuraHillHamiltonianPolynomial (s+1) +
      spatialDerivative (C ((-1 : ℂ)^(s+1)/2)*X (false,2*s)) := by
  simp [miuraHillNativeDensity,miuraHillRiccatiRemainder,miuraHillHamiltonianPolynomial,
    Derivation.leibniz,smul_eq_mul,nextJet,mul_add]

theorem integral_miuraHillNativeDensity (s : ℕ) (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1, evaluate u u (miuraHillNativeDensity s) x) =
      classicalMiuraHillHamiltonian u (s+1) := by
  rw [integral_evaluate_eq_of_total_derivative u u hu hu hp hp _ _ _ (miuraHillNativeDensity_eq s)]
  exact integral_evaluate_miuraHillHamiltonianPolynomial u (s+1)

theorem exists_miuraHillNativePolynomial (s : ℕ) :
    ∃ q : DifferentialPolynomial.Polynomial, JetOrderLE q s ∧ DerivativeOrderLE q (2*(s : ℤ)) ∧
      ∀ u : ℝ → ℂ, ContDiff ℝ ∞ u → Function.Periodic u 1 →
        classicalMiuraHillHamiltonian u (s+1) = ∫ x in (0 : ℝ)..1, evaluate u u q x := by
  obtain ⟨q,r,he,hq,hd⟩ := exists_jet_reduction_of_derivativeOrder (s+1) (by omega)
    (miuraHillNativeDensity s) (2*(s : ℤ)) (by push_cast; omega)
    (miuraHillNativeDensity_derivativeOrder s)
  refine ⟨q,by simpa using hq,hd,?_⟩
  intro u hu hp
  rw [← integral_miuraHillNativeDensity s u hu hp]
  exact integral_evaluate_eq_of_total_derivative u u hu hu hp hp _ q r he

end NLS.MKdV
