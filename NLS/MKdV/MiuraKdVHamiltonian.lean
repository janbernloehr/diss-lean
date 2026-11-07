import NLS.DifferentialPolynomial.ScalarHillLowRiccati
import NLS.MKdV.MiuraHierarchyHamiltonians
import NLS.MKdV.MiuraClassicalSolution
import NLS.KdV.ClassicalHamiltonian

/-! Exact normalized physical scalar Hill Hamiltonians of the actual
Miura potential. Order three is precisely the ORIGINAL KdV energy. -/
noncomputable section
open MvPolynomial Complex NLS.DifferentialPolynomial NLS.KdV
open scoped ContDiff
namespace NLS.MKdV

theorem evaluate_miuraHillPotentialPolynomial (u : ℝ → ℂ) :
    evaluate u u miuraHillPotentialPolynomial=miuraPotential u := by
  funext x
  simp [miuraHillPotentialPolynomial,evaluate,miuraPotential,iteratedDeriv_one]

theorem classicalMiuraHillHamiltonian_three_eq_KdV (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) :
    classicalMiuraHillHamiltonian u 3=classicalKdVHamiltonian (miuraPotential u) := by
  let R := miuraHillPotentialPolynomial
  let P := (spatialDerivative R)^2+2*R^3
  let Q := spatialDerivative (spatialDerivative (spatialDerivative R))-6*R*spatialDerivative R
  have hid : -(miuraHillRiccatiPolynomial 4)=P+spatialDerivative Q :=
    differentialRiccatiSequence_scalar_four_KdV spatialDerivative R
  have he := integral_evaluate_eq_of_total_derivative u u hu hu hp hp
    (-(miuraHillRiccatiPolynomial 4)) P Q hid
  simp only [evaluate_neg,Pi.neg_apply,intervalIntegral.integral_neg] at he
  have hP (x : ℝ) : evaluate u u P x=
      (deriv (miuraPotential u) x)^2+2*(miuraPotential u x)^3 := by
    change MvPolynomial.eval _ ((spatialDerivative R)^2+2*R^3)=_
    rw [map_add,map_pow,map_mul,map_ofNat,map_pow]
    change (evaluate u u (spatialDerivative R) x)^2+2*(evaluate u u R x)^3=_
    rw [evaluate_spatialDerivative u u hu hu,evaluate_miuraHillPotentialPolynomial]
  change ((-1:ℂ)^3/2)*(∫ x in (0:ℝ)..1, evaluate u u (miuraHillRiccatiPolynomial 4) x)=_
  norm_num only [neg_pow,one_pow,neg_one_mul]
  calc
    _ = (1/2:ℂ)*(∫ x in (0:ℝ)..1, evaluate u u P x) := by rw [← he]; ring
    _ = ∫ x in (0:ℝ)..1, (1/2:ℂ)*evaluate u u P x :=
      (intervalIntegral.integral_const_mul _ _).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [hP]
      ring

theorem classicalMiuraHillHamiltonian_two_eq_square_miura (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) :
    classicalMiuraHillHamiltonian u 2=(1/2:ℂ)*∫ x in (0:ℝ)..1, (miuraPotential u x)^2 := by
  let R := miuraHillPotentialPolynomial
  have hid : miuraHillRiccatiPolynomial 2=R^2+spatialDerivative (-spatialDerivative R) := by
    rw [miuraHillRiccatiPolynomial,differentialRiccatiSequence_scalar_two,map_neg]
    ring
  have he := integral_evaluate_eq_of_total_derivative u u hu hu hp hp
    (miuraHillRiccatiPolynomial 2) (R^2) (-spatialDerivative R) hid
  change ((-1:ℂ)^2/2)*(∫ x in (0:ℝ)..1, evaluate u u (miuraHillRiccatiPolynomial 2) x)=_
  rw [he]
  norm_num only [neg_one_sq]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  change MvPolynomial.eval _ (R^2)=_
  rw [map_pow]
  change (evaluate u u R x)^2=_
  rw [evaluate_miuraHillPotentialPolynomial]

end NLS.MKdV
