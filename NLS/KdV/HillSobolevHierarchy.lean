import NLS.KdV.HillHamiltonianReduction
import NLS.ZakharovShabat.SobolevOddHamiltonian

/-! # The independent physical source Hamiltonians on the full sharp complex Sobolev domains. -/

noncomputable section
set_option autoImplicit false
open Complex MeasureTheory NLS.Fourier NLS.DifferentialPolynomial NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

/-- One scalar polynomial is fixed independently of every source. -/
def hillReducedPolynomial (m : ℕ) (hm : 1 ≤ m) : DifferentialPolynomial.Polynomial :=
  Classical.choose (exists_classicalKdVHierarchyHamiltonian_reduced_polynomial m hm)

theorem hillReducedPolynomial_order (m : ℕ) (hm : 1 ≤ m) :
    JetOrderLE (hillReducedPolynomial m hm) (m-1) :=
  (Classical.choose_spec (exists_classicalKdVHierarchyHamiltonian_reduced_polynomial m hm)).1

theorem hillReducedPolynomial_homogeneous (m : ℕ) (hm : 1 ≤ m) :
    (hillReducedPolynomial m hm).IsWeightedHomogeneous hillJetWeight (2*(m : ℤ)+4) :=
  (Classical.choose_spec (exists_classicalKdVHierarchyHamiltonian_reduced_polynomial m hm)).2.1

theorem hillReducedPolynomial_classical (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1) :
    classicalKdVHierarchyHamiltonian q m = (1/2 : ℂ)*∫ x in (0 : ℝ)..1,
      (iteratedDeriv m q x)^2+evaluate q 0 (hillReducedPolynomial m hm) x :=
  (Classical.choose_spec (exists_classicalKdVHierarchyHamiltonian_reduced_polynomial m hm)).2.2
    q hq hp

/-- The physical source hierarchy on the complete complex sharp Sobolev domain. -/
def hillSobolevHamiltonian (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) : ℂ :=
  (1/2 : ℂ)*(sobolevOddKinetic m (a,a)+
    sobolevPolynomialMean m (hillReducedPolynomial m hm) (a,0))

theorem analyticAt_hillSobolevHamiltonian (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) :
    AnalyticAt ℂ (hillSobolevHamiltonian m hm) a := by
  have hk : AnalyticAt ℂ (fun b : ScalarSobolev m => sobolevOddKinetic m (b,b)) a :=
    (analyticAt_sobolevOddKinetic m (a,a)).comp (f := fun b : ScalarSobolev m => (b,b))
      (analyticAt_id.prod analyticAt_id)
  have hp : AnalyticAt ℂ (fun b : ScalarSobolev m =>
      sobolevPolynomialMean m (hillReducedPolynomial m hm) (b,0)) a :=
    (analyticAt_sobolevPolynomialMean m (hillReducedPolynomial m hm) (a,0)).comp
      (f := fun b : ScalarSobolev m => (b,0)) (analyticAt_id.prod analyticAt_const)
  exact analyticAt_const.mul (hk.add hp)

theorem continuous_hillSobolevHamiltonian (m : ℕ) (hm : 1 ≤ m) :
    Continuous (hillSobolevHamiltonian m hm) :=
  continuous_iff_continuousAt.mpr fun a => (analyticAt_hillSobolevHamiltonian m hm a).continuousAt

theorem hillSobolevHamiltonian_eq_classical (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m)
    (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1)
    (ha : ∀ j, a.val j = periodOneCoefficient q j) :
    hillSobolevHamiltonian m hm a = classicalKdVHierarchyHamiltonian q m := by
  rw [hillSobolevHamiltonian, hillReducedPolynomial_classical m hm q hq hp,
    sobolevOddKinetic_eq_integral m (a,a) q q hq hq hp hp ha ha,
    sobolevPolynomialMean_eq_integral m hm _ (hillReducedPolynomial_order m hm)
      (a,0) q 0 hq contDiff_const hp (fun _ => rfl) ha
      (fun j => by simp [periodOneCoefficient, fourierCoeffOn_eq_integral])]
  rw [intervalIntegral.integral_add]
  · simp only [pow_two]
  · exact ((contDiff_iteratedDeriv_of_smooth q hq m).continuous.pow 2).intervalIntegrable 0 1
  · exact (continuous_evaluate q 0 hq contDiff_const _).intervalIntegrable 0 1

end NLS.KdV
