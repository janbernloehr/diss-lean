import NLS.KdV.HillRiccatiHierarchy
import NLS.DifferentialPolynomial.ScalarRiccatiConstantVariation
import NLS.DifferentialPolynomial.MultiJet
import NLS.DifferentialPolynomial.SmoothVariation
import NLS.DifferentialPolynomial.AlgebraicPolynomialVariation

/-! # The exact constant-shift derivative of every physical KdV Hamiltonian

The formal constant-potential variation is evaluated on actual smooth
physical fields and integrated over the original unit period.
-/
noncomputable section
set_option autoImplicit false
open MvPolynomial Set Complex MeasureTheory
open NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.KdV

/-- Add the same physical constant to both copies of the scalar field. -/
def constantPotentialVariation : Derivation ℂ DifferentialPolynomial.Polynomial DifferentialPolynomial.Polynomial :=
  evolutionaryDerivative (fun _ : Bool => (1 : DifferentialPolynomial.Polynomial))

theorem constantPotentialVariation_commute (P : DifferentialPolynomial.Polynomial) :
    constantPotentialVariation (spatialDerivative P) = spatialDerivative (constantPotentialVariation P) :=
  evolutionaryDerivative_commute _ P

theorem constantPotentialVariation_field : constantPotentialVariation (X (false,0)) = 1 := by
  simp [constantPotentialVariation]

/-- Exact all-order variation, with a literal complex coefficient. -/
theorem hillRiccatiPolynomial_constantVariation (n : ℕ) :
    constantPotentialVariation (hillRiccatiPolynomial (n+2)) =
      C (-2*((n+1 : ℕ) : ℂ))*hillRiccatiPolynomial n := by
  have he := scalarRiccati_constant_variation spatialDerivative constantPotentialVariation
    constantPotentialVariation_commute (X (false,0)) constantPotentialVariation_field n
  simpa only [hillRiccatiPolynomial,map_mul,map_neg,map_ofNat,map_natCast] using he

/-- The formal perturbation agrees with the actual physical first variation. -/
theorem firstVariationDensity_constant (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (P : DifferentialPolynomial.Polynomial) :
    firstVariationDensity q q (fun _ => 1) (fun _ => 1) P =
      evaluate q q (constantPotentialVariation P) := by
  classical
  have hD : multiSpatialDerivative Bool = spatialDerivative := rfl
  funext x
  rw [constantPotentialVariation,evolutionaryDerivative,
    mkDerivation_eq_sum_pderiv _ P P.vars (fun _ h => h)]
  simp only [firstVariationDensity,ite_self,evaluate,map_sum,map_mul,hD]
  apply Finset.sum_congr rfl
  intro v _
  have he := congrFun (evaluate_iterate_spatialDerivative q q hq hq
    (1 : DifferentialPolynomial.Polynomial) v.2) x
  have h1 : evaluate q q 1 = fun _ => (1 : ℂ) := by funext y; simp [evaluate]
  rw [h1] at he
  simpa only [evaluate,ite_self] using congrArg (fun a : ℂ => a*evaluate q q (pderiv v P) x) he.symm

/-- The physical hierarchy has derivative d/dc H_(m+1)(q+c)=
2*(2m+3)*H_m(q) at c=0, with all original constants fixed. -/
theorem hasDerivAt_classicalHillHierarchyHamiltonian_shift_zero (m : ℕ) (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) :
    HasDerivAt (fun c : ℂ => classicalHillHierarchyHamiltonian (fun x => q x+c) (m+1))
      (2*((2*m+3 : ℕ) : ℂ)*classicalHillHierarchyHamiltonian q m) 0 := by
  have hd := (hasDerivAt_integral_evaluate q q (fun _ => 1) (fun _ => 1) hq hq
    contDiff_const contDiff_const (hillRiccatiPolynomial (2*(m+1)+2))).const_mul
      ((-1 : ℂ)^(m+1+2)/2)
  simp only [mul_one] at hd
  change HasDerivAt (fun c : ℂ => classicalHillHierarchyHamiltonian (fun x => q x+c) (m+1)) _ 0 at hd
  rw [firstVariationDensity_constant q hq,show 2*(m+1)+2=(2*m+2)+2 by omega,
    hillRiccatiPolynomial_constantVariation] at hd
  have he : (∫ x in (0 : ℝ)..1,
      evaluate q q (C (-2*((2*m+2+1 : ℕ) : ℂ))*hillRiccatiPolynomial (2*m+2)) x) =
      (-2*((2*m+3 : ℕ) : ℂ))*(∫ x in (0 : ℝ)..1, evaluate q q (hillRiccatiPolynomial (2*m+2)) x) := by
    simp only [evaluate_mul,evaluate_C,Pi.mul_apply]
    rw [intervalIntegral.integral_const_mul]
  rw [he] at hd
  convert hd using 1
  rw [classicalHillHierarchyHamiltonian,show m+1+2=m+2+1 by omega,pow_succ]
  ring

end NLS.KdV
