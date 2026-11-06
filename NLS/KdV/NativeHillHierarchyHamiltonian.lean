import NLS.KdV.HillRiccatiHierarchy
import NLS.MKdV.NativeMiuraHillHamiltonian
import NLS.ZakharovShabat.SobolevPolynomialEndpointMean
import NLS.ZakharovShabat.SobolevScalarSmoothDensity

/-! # The original scalar KdV hierarchy on its full native domains

H_m is constructed independently from its scalar Hill Riccati density on
complex H^m. Each member is entire analytic and is uniquely determined by
its physical smooth periodic integral. The original printed H0, H1 and H2
are recovered without a change of constants or topology.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier NLS.ZakharovShabat NLS.MKdV NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.KdV

def hillHierarchyNativePolynomial (m : ℕ) : DifferentialPolynomial.Polynomial :=
  Classical.choose (exists_hillHierarchyNativePolynomial m)

theorem hillHierarchyNativePolynomial_order (m : ℕ) :
    JetOrderLE (hillHierarchyNativePolynomial m) m :=
  (Classical.choose_spec (exists_hillHierarchyNativePolynomial m)).1

theorem hillHierarchyNativePolynomial_derivativeOrder (m : ℕ) :
    DerivativeOrderLE (hillHierarchyNativePolynomial m) (2*(m : ℤ)) :=
  (Classical.choose_spec (exists_hillHierarchyNativePolynomial m)).2.1

theorem hillHierarchyNativePolynomial_classical (m : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    classicalHillHierarchyHamiltonian f m =
      ∫ x in (0 : ℝ)..1, evaluate f f (hillHierarchyNativePolynomial m) x :=
  (Classical.choose_spec (exists_hillHierarchyNativePolynomial m)).2.2 f hf hp

/-- The independently defined H_m on the complete original complex H^m space. -/
def nativeHillHierarchyHamiltonian (m : ℕ) (q : ScalarSobolev m) : ℂ :=
  if 1 ≤ m then sobolevPolynomialEndpointMean m (hillHierarchyNativePolynomial m) (q,q)
  else nativeMiuraMass m q

/-- Every member is complex analytic at every native source. -/
theorem analyticAt_nativeHillHierarchyHamiltonian (m : ℕ) (q : ScalarSobolev m) :
    AnalyticAt ℂ (nativeHillHierarchyHamiltonian m) q := by
  unfold nativeHillHierarchyHamiltonian
  split_ifs
  · exact (analyticAt_sobolevPolynomialEndpointMean m (hillHierarchyNativePolynomial m) (q,q)).comp
      (f := hierarchyDiagonal m) ((hierarchyDiagonal m).analyticAt q)
  · exact analyticAt_nativeMiuraMass m q

/-- Exact agreement with the original physical scalar Hill integral on
smooth periodic inputs, at every hierarchy order. -/
theorem nativeHillHierarchyHamiltonian_eq_classical (m : ℕ) (q : ScalarSobolev m)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ n, q.val n = periodOneCoefficient f n) :
    nativeHillHierarchyHamiltonian m q = classicalHillHierarchyHamiltonian f m := by
  unfold nativeHillHierarchyHamiltonian
  split_ifs with hm
  · rw [hillHierarchyNativePolynomial_classical m f hf hp]
    exact sobolevPolynomialEndpointMean_eq_classical m hm _
      (hillHierarchyNativePolynomial_derivativeOrder m) (hillHierarchyNativePolynomial_order m)
      (q,q) f f hf hf hp hp hc hc
  · have hm0 : m = 0 := by omega
    subst m
    rw [nativeMiuraMass_eq_classical 0 q f hf hp hc,classicalMiuraHillHamiltonian_one f hf hp,
      classicalHillHierarchyHamiltonian_zero f hf hp]

/-- Native continuity and physical smooth comparison determine H_m uniquely. -/
theorem nativeHillHierarchyHamiltonian_unique_continuous (m : ℕ) (F : ScalarSobolev m → ℂ)
    (hF : Continuous F)
    (hclassical : ∀ (q : ScalarSobolev m) (f : ℝ → ℂ), ContDiff ℝ ∞ f → Function.Periodic f 1 →
      (∀ n, q.val n = periodOneCoefficient f n) → F q = classicalHillHierarchyHamiltonian f m) :
    F = nativeHillHierarchyHamiltonian m := by
  apply eq_of_continuous_of_smooth_scalarSobolev m F _ hF
    (continuous_iff_continuousAt.mpr fun q => (analyticAt_nativeHillHierarchyHamiltonian m q).continuousAt)
  intro q f hf hp hc
  exact (hclassical q f hf hp hc).trans (nativeHillHierarchyHamiltonian_eq_classical m q f hf hp hc).symm

/-- The full L2 endpoint is the original physical quadratic mass. -/
theorem nativeHillHierarchyHamiltonian_zero (q : ScalarSobolev 0) :
    nativeHillHierarchyHamiltonian 0 q = nativeMiuraMass 0 q := by
  simp only [nativeHillHierarchyHamiltonian,show ¬1 ≤ (0 : ℕ) by omega,↓reduceIte]

/-- The H1 member is exactly the printed native KdV Hamiltonian. -/
theorem nativeHillHierarchyHamiltonian_one (q : ScalarSobolev 1) :
    nativeHillHierarchyHamiltonian 1 q = nativeKdVHamiltonian q := by
  have he := nativeHillHierarchyHamiltonian_unique_continuous 1 nativeKdVHamiltonian
    (continuous_iff_continuousAt.mpr fun v => (analyticAt_nativeKdVHamiltonian v).continuousAt) (by
      intro v f hf hp hc
      rw [nativeKdVHamiltonian_eq_of_coefficients v f hf.continuous hp hc,
        classicalHillHierarchyHamiltonian_one f hf hp])
  exact (congrFun he q).symm

/-- The H2 member is exactly the printed native KdV2 Hamiltonian. -/
theorem nativeHillHierarchyHamiltonian_two (q : ScalarSobolev 2) :
    nativeHillHierarchyHamiltonian 2 q = nativeKdV2Hamiltonian q := by
  have he := nativeHillHierarchyHamiltonian_unique_continuous 2 nativeKdV2Hamiltonian
    (continuous_iff_continuousAt.mpr fun v => (analyticAt_nativeKdV2Hamiltonian v).continuousAt) (by
      intro v f hf hp hc
      rw [nativeKdV2Hamiltonian_eq_of_coefficients v f hf.continuous hp hc,
        classicalHillHierarchyHamiltonian_two f hf hp])
  exact (congrFun he q).symm

end NLS.KdV
