import NLS.MKdV.MiuraHierarchyHamiltonians
import NLS.MKdV.HierarchyGradientRecurrence
import NLS.DifferentialPolynomial.SmoothVariation
import NLS.Fourier.PeriodicVariationalUniqueness

/-! # All-order smooth Miura hierarchy flow restriction

The scalar gradient below is the Euler gradient of the independent scalar
Hill density. Its actual first variation is proved before its comparison
with the NLS gradient. Gardner's spatial derivative then yields the flow.
-/
noncomputable section
open MvPolynomial Complex NLS.DifferentialPolynomial NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.MKdV

def miuraHillHamiltonianPolynomial : ℕ → DifferentialPolynomial.Polynomial
  | 0 => 0
  | m+1 => C ((-1 : ℂ)^(m+1)/2)*miuraHillRiccatiPolynomial (2*m)

theorem integral_evaluate_miuraHillHamiltonianPolynomial (u : ℝ → ℂ) (m : ℕ) :
    (∫ x in (0 : ℝ)..1, evaluate u u (miuraHillHamiltonianPolynomial m) x) =
      classicalMiuraHillHamiltonian u m := by
  cases m with
  | zero => simp [miuraHillHamiltonianPolynomial, classicalMiuraHillHamiltonian, evaluate]
  | succ m =>
    simp only [miuraHillHamiltonianPolynomial, classicalMiuraHillHamiltonian,
      evaluate_mul, evaluate_C, Pi.mul_apply]
    exact intervalIntegral.integral_const_mul _ _

/-- The actual scalar Euler gradient after diagonal evaluation of the
independently constructed Hill density. Both field slots vary with u. -/
def classicalMiuraHillGradient (u : ℝ → ℂ) (m : ℕ) : ℝ → ℂ :=
  evaluate u u (eulerDerivative false (miuraHillHamiltonianPolynomial m) +
    eulerDerivative true (miuraHillHamiltonianPolynomial m))

theorem contDiff_classicalMiuraHillGradient (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (m : ℕ) :
    ContDiff ℝ ∞ (classicalMiuraHillGradient u m) := contDiff_evaluate u u hu hu _

theorem periodic_classicalMiuraHillGradient (u : ℝ → ℂ)
    (hp : Function.Periodic u 1) (m : ℕ) :
    Function.Periodic (classicalMiuraHillGradient u m) 1 := periodic_evaluate u u 1 hp hp _

theorem hasDerivAt_classicalMiuraHillHamiltonian (u h : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hh : ContDiff ℝ ∞ h)
    (hp : Function.Periodic u 1) (hph : Function.Periodic h 1) (m : ℕ) :
    HasDerivAt (fun z : ℂ => classicalMiuraHillHamiltonian (fun x => u x+z*h x) m)
      (∫ x in (0 : ℝ)..1, h x*classicalMiuraHillGradient u m x) 0 := by
  have he := hasDerivAt_integral_evaluate_euler u u h h hu hu hh hh hp hp hph hph
    (miuraHillHamiltonianPolynomial m)
  simp_rw [integral_evaluate_miuraHillHamiltonianPolynomial] at he
  convert he using 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only [classicalMiuraHillGradient, evaluate_add, Pi.add_apply, mul_add]

/-- The independent scalar Hill gradient is the actual odd NLS gradient
component, certified by uniqueness of smooth periodic first variations. -/
theorem classicalMiuraHillGradient_eq_oddNLS (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) (m : ℕ) :
    classicalMiuraHillGradient u (m+1) =
      fun x => (classicalNLSHierarchyGradient u u (2*m+1) x).1 := by
  apply NLS.Fourier.eq_of_periodic_integral_mul_eq _ _
    (contDiff_classicalMiuraHillGradient u hu _).continuous
    ((contDiff_classicalNLSHierarchyGradient u u hu hu _).fst.continuous)
    (periodic_classicalMiuraHillGradient u hp _)
    (fun x => congrArg Prod.fst (periodic_classicalNLSHierarchyGradient u u hp hp _ x))
  intro h hh hph
  have hnorm (z : ℂ) : classicalMiuraHillHamiltonian (fun x => u x+z*h x) (m+1) =
      (1/2 : ℂ)*classicalNLSHamiltonian (fun x => u x+z*h x) (fun x => u x+z*h x) (2*m+1) := by
    have he := classicalNLSHamiltonian_odd_diagonal_eq_miuraHill (fun x => u x+z*h x)
      (hu.add (contDiff_const.mul hh)) (fun x => by dsimp only; rw [hp x, hph x]) m
    linear_combination -(1/2 : ℂ)*he
  have hK := hasDerivAt_classicalMiuraHillHamiltonian u h hu hh hp hph (m+1)
  simp_rw [hnorm] at hK
  have hN := (hasDerivAt_classicalNLSHamiltonian u u h h hu hu hh hh hp hp hph hph (2*m+1)).const_mul
    (1/2 : ℂ)
  have he := hK.unique hN
  rw [← intervalIntegral.integral_const_mul] at he
  rw [he]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [classicalHierarchyGradient_odd_diagonal_components u hu hp m x]
  ring

/-- NLS's actual physical Poisson structure -iJ at every Hamiltonian order. -/
def classicalNLSHierarchyVectorField (a b : ℝ → ℂ) (k : ℕ) (x : ℝ) : ℂ × ℂ :=
  (-I*(classicalNLSHierarchyGradient a b k x).2,
    I*(classicalNLSHierarchyGradient a b k x).1)

/-- Gardner's derivative of the independently certified scalar gradient. -/
def classicalMiuraHillVectorField (u : ℝ → ℂ) (m : ℕ) : ℝ → ℂ :=
  deriv (classicalMiuraHillGradient u m)

/-- Theorem 1's flow identity at every order on smooth complex periodic
fields, for the independently constructed scalar Hill / Miura hierarchy. -/
theorem classicalNLSHierarchyVectorField_even_diagonal (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) (m : ℕ) (x : ℝ) :
    classicalNLSHierarchyVectorField u u (2*m+2) x =
      (classicalMiuraHillVectorField u (m+1) x, classicalMiuraHillVectorField u (m+1) x) := by
  have he := classicalHierarchyGradient_diagonal_recurrence u hu hp m x
  have hg : (fun y => (classicalNLSHierarchyGradient u u (2*m+1) y).2) =
      fun y => (classicalNLSHierarchyGradient u u (2*m+1) y).1 := by
    funext y
    exact classicalHierarchyGradient_odd_diagonal_components u hu hp m y
  rw [hg] at he
  have hK := classicalMiuraHillGradient_eq_oddNLS u hu hp m
  apply Prod.ext
  · change -I*(classicalNLSHierarchyGradient u u (2*m+2) x).2 =
      deriv (classicalMiuraHillGradient u (m+1)) x
    rw [hK]
    exact congrArg Prod.snd he
  · change I*(classicalNLSHierarchyGradient u u (2*m+2) x).1 =
      deriv (classicalMiuraHillGradient u (m+1)) x
    rw [hK]
    exact congrArg Prod.fst he

end NLS.MKdV
