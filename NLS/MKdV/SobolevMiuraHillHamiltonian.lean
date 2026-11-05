import NLS.DifferentialPolynomial.UngradedIntegrationByParts
import NLS.MKdV.MiuraHierarchyFlowRestriction
import NLS.ZakharovShabat.SobolevPolynomialVariation
import NLS.ZakharovShabat.SobolevSourceCotangent
import NLS.ZakharovShabat.SobolevSmoothFirstVariation

/-! # Independent scalar Hill Hamiltonians on complex H^m

The densities come from the scalar Hill recurrence at u'+u². Integration by
parts is applied directly to those scalar densities, without defining the
scalar Hamiltonian as a restriction of an NLS Hamiltonian.
-/
noncomputable section
open MvPolynomial Complex NLS.DifferentialPolynomial NLS.ZakharovShabat NLS.Fourier
open scoped ContDiff
namespace NLS.MKdV

theorem miuraHillRiccatiPolynomial_derivativeOrder (n : ℕ) :
    DerivativeOrderLE (miuraHillRiccatiPolynomial n) ((n : ℤ)+1) := by
  have hq : DerivativeOrderLE miuraHillPotentialPolynomial 1 :=
    (DerivativeOrderLE.X (false,1)).add
      (by simpa [pow_two] using ((DerivativeOrderLE.X (false,0)).mul
        (DerivativeOrderLE.X (false,0))).mono (by norm_num))
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simpa [miuraHillRiccatiPolynomial] using hq.neg
    · simpa [miuraHillRiccatiPolynomial] using hq.neg.spatialDerivative
    · rw [miuraHillRiccatiPolynomial, differentialRiccatiSequence_recurrence, one_mul]
      apply DerivativeOrderLE.add
      · exact ((ih (n+1) (by omega)).spatialDerivative).mono (by push_cast; omega)
      · apply DerivativeOrderLE.sum
        intro ij hij
        have he := Finset.mem_antidiagonal.mp hij
        exact ((ih ij.1 (by omega)).mul (ih ij.2 (by omega))).mono (by push_cast; omega)

theorem miuraHillHamiltonianPolynomial_derivativeOrder (m : ℕ) (hm : 1 ≤ m) :
    DerivativeOrderLE (miuraHillHamiltonianPolynomial m) (2*(m : ℤ)-1) := by
  obtain ⟨r,rfl⟩ : ∃ r, m = r+1 := ⟨m-1, by omega⟩
  change DerivativeOrderLE (C ((-1 : ℂ)^(r+1)/2)*miuraHillRiccatiPolynomial (2*r)) _
  exact ((DerivativeOrderLE.C _).mul (miuraHillRiccatiPolynomial_derivativeOrder (2*r))).mono
    (by push_cast; omega)

theorem exists_miuraHillHamiltonian_reduced_polynomial (m : ℕ) (hm : 1 ≤ m) :
    ∃ q : DifferentialPolynomial.Polynomial, JetOrderLE q m ∧
      DerivativeOrderLE q (2*(m : ℤ)-1) ∧
      ∀ u : ℝ → ℂ, ContDiff ℝ ∞ u → Function.Periodic u 1 →
        classicalMiuraHillHamiltonian u m = ∫ x in (0 : ℝ)..1, evaluate u u q x := by
  obtain ⟨q,r,he,hq,hd⟩ := exists_jet_reduction_of_derivativeOrder (m+1) (by omega)
    (miuraHillHamiltonianPolynomial m) (2*(m : ℤ)-1) (by push_cast; omega)
    (miuraHillHamiltonianPolynomial_derivativeOrder m hm)
  refine ⟨q, by simpa using hq, hd, ?_⟩
  intro u hu hp
  rw [← integral_evaluate_miuraHillHamiltonianPolynomial u m]
  exact integral_evaluate_eq_of_total_derivative u u hu hu hp hp _ q r he

def miuraHillReducedPolynomial (m : ℕ) (hm : 1 ≤ m) : DifferentialPolynomial.Polynomial :=
  Classical.choose (exists_miuraHillHamiltonian_reduced_polynomial m hm)

theorem miuraHillReducedPolynomial_order (m : ℕ) (hm : 1 ≤ m) :
    JetOrderLE (miuraHillReducedPolynomial m hm) m :=
  (Classical.choose_spec (exists_miuraHillHamiltonian_reduced_polynomial m hm)).1

theorem miuraHillReducedPolynomial_derivativeOrder (m : ℕ) (hm : 1 ≤ m) :
    DerivativeOrderLE (miuraHillReducedPolynomial m hm) (2*(m : ℤ)-1) :=
  (Classical.choose_spec (exists_miuraHillHamiltonian_reduced_polynomial m hm)).2.1

def sobolevMiuraHillHamiltonian (m : ℕ) (hm : 1 ≤ m) (u : ScalarSobolev m) : ℂ :=
  sobolevPolynomialL2Mean m (miuraHillReducedPolynomial m hm) (u,u)

theorem analyticAt_sobolevMiuraHillHamiltonian (m : ℕ) (hm : 1 ≤ m) (u : ScalarSobolev m) :
    AnalyticAt ℂ (sobolevMiuraHillHamiltonian m hm) u :=
  (analyticAt_sobolevPolynomialL2Mean m (miuraHillReducedPolynomial m hm) (u,u)).comp
    (f := hierarchyDiagonal m) ((hierarchyDiagonal m).analyticAt u)

theorem sobolevMiuraHillHamiltonian_eq_classical (m : ℕ) (hm : 1 ≤ m)
    (u : ScalarSobolev m) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ j, u.val j = periodOneCoefficient f j) :
    sobolevMiuraHillHamiltonian m hm u = classicalMiuraHillHamiltonian f m := by
  rw [(Classical.choose_spec (exists_miuraHillHamiltonian_reduced_polynomial m hm)).2.2 f hf hp]
  exact sobolevPolynomialL2Mean_eq_classical m hm _
    (miuraHillReducedPolynomial_derivativeOrder m hm) (miuraHillReducedPolynomial_order m hm)
    (u,u) f f hf hf hp hp hc hc

/-- The actual scalar derivative represented in the opposite Sobolev space. -/
def sobolevMiuraHillGradient (m : ℕ) (hm : 1 ≤ m) (u : ScalarSobolev m) : NegativeScalarSobolev m :=
  WeightedCoeff.sobolevCotangentCLM (p := 2) (q := 2) (m : ℝ) (by norm_num)
    (fderiv ℂ (sobolevMiuraHillHamiltonian m hm) u)

theorem analyticAt_sobolevMiuraHillGradient (m : ℕ) (hm : 1 ≤ m) (u : ScalarSobolev m) :
    AnalyticAt ℂ (sobolevMiuraHillGradient m hm) u :=
  ((WeightedCoeff.sobolevCotangentCLM (p := 2) (q := 2) (m : ℝ) (by norm_num)).analyticAt _).comp
    (analyticAt_sobolevMiuraHillHamiltonian m hm u).fderiv

/-- The gradient represents the complete actual scalar differential. -/
theorem sobolevMiuraHillGradient_represents (m : ℕ) (hm : 1 ≤ m) (u h : ScalarSobolev m) :
    WeightedCoeff.sobolevBilinearPairing (m : ℝ) h (sobolevMiuraHillGradient m hm u) =
      fderiv ℂ (sobolevMiuraHillHamiltonian m hm) u h := by
  rw [sobolevMiuraHillGradient, WeightedCoeff.sobolevCotangentCLM_apply,
    WeightedCoeff.sobolevBilinearPairing_sobolevCotangent]

theorem sobolevMiuraHillGradient_eq_classical (m : ℕ) (hm : 1 ≤ m)
    (u : ScalarSobolev m) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ j, u.val j = periodOneCoefficient f j) (n : ℤ) :
    (sobolevMiuraHillGradient m hm u).val n = periodOneCoefficient (classicalMiuraHillGradient f m) n := by
  apply scalarCotangent_eq_classical
  intro h g hg hpg hgc
  exact fderiv_scalarSobolev_eq_smooth_variation m _ (fun v => classicalMiuraHillHamiltonian v m)
    u h f g (analyticAt_sobolevMiuraHillHamiltonian m hm u)
    (fun a v hv hpv hvc => sobolevMiuraHillHamiltonian_eq_classical m hm a v hv hpv hvc)
    hf hg hp hpg hc hgc _ (hasDerivAt_classicalMiuraHillHamiltonian f g hf hg hp hpg m)

end NLS.MKdV
