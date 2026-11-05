import NLS.ZakharovShabat.ClassicalNLSHierarchyVariation
import NLS.ZakharovShabat.SobolevPolynomialL2
import NLS.Fourier.CircleUnitCoefficients

/-! # Analytic L² extensions of the physical hierarchy gradients -/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial MvPolynomial Complex
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem nlsHamiltonianPolynomial_derivativeOrder (k : ℕ) :
    DerivativeOrderLE (nlsHamiltonianPolynomial k) (k-1) := by
  cases k with
  | zero => exact DerivativeOrderLE.zero _
  | succ n =>
    simpa [nlsHamiltonianPolynomial] using
      ((DerivativeOrderLE.C ((-I)^(n+2))).mul (DerivativeOrderLE.X (false,0))).mul
        (nlsRiccatiPolynomial_derivativeOrder n)

theorem nlsHierarchyEuler_derivativeOrder (k : ℕ) (field : Bool) :
    DerivativeOrderLE (eulerDerivative field (nlsHamiltonianPolynomial k)) (k-1) :=
  (nlsHamiltonianPolynomial_derivativeOrder k).eulerDerivative field

theorem nlsHamiltonianPolynomial_one :
    nlsHamiltonianPolynomial 1 = X (false,0) * X (true,0) := by
  norm_num [nlsHamiltonianPolynomial, I_sq]

theorem classicalNLSHierarchyGradient_one (a b : ℝ → ℂ) (x : ℝ) :
    classicalNLSHierarchyGradient a b 1 x = (b x,a x) := by
  have hv : (X (false,0) * X (true,0) : DifferentialPolynomial.Polynomial).vars =
      {(false,0),(true,0)} := by
    simp [MvPolynomial.X, MvPolynomial.monomial_mul, MvPolynomial.vars_monomial,
      Finsupp.support_add_eq_union]
  simp [classicalNLSHierarchyGradient, nlsHamiltonianPolynomial_one, eulerDerivative,
    hv, MvPolynomial.pderiv_X, Pi.single_apply]

/-- The gradient coefficients in the original period-one L² space.
The zero-regularity mass endpoint is handled directly. -/
def sobolevNLSHierarchyGradient (s k : ℕ) (ab : SobolevSource s) : Coeff 2 × Coeff 2 :=
  if hs : 1 ≤ s then
    (circleUnitCoefficients (sobolevPolynomialL2 s (eulerDerivative false (nlsHamiltonianPolynomial k)) ab),
      circleUnitCoefficients (sobolevPolynomialL2 s (eulerDerivative true (nlsHamiltonianPolynomial k)) ab))
  else if k = 1 then
    (hierarchySobolevJetL2 s 0 (by omega) ab.2, hierarchySobolevJetL2 s 0 (by omega) ab.1)
  else (0,0)

theorem analyticAt_sobolevNLSHierarchyGradient (s k : ℕ) (ab : SobolevSource s) :
    AnalyticAt ℂ (sobolevNLSHierarchyGradient s k) ab := by
  unfold sobolevNLSHierarchyGradient
  split_ifs
  · exact ((circleUnitCoefficients.analyticAt _).comp
      (analyticAt_sobolevPolynomialL2 s _ ab)).prod
      ((circleUnitCoefficients.analyticAt _).comp (analyticAt_sobolevPolynomialL2 s _ ab))
  · exact (((hierarchySobolevJetL2 s 0 (by omega)).comp
      (ContinuousLinearMap.snd ℂ _ _)).analyticAt ab).prod
      (((hierarchySobolevJetL2 s 0 (by omega)).comp
        (ContinuousLinearMap.fst ℂ _ _)).analyticAt ab)
  · exact analyticAt_const

/-- At every admissible order, these L² coefficients are exactly the Fourier
integrals of the already certified physical gradient on smooth inputs. -/
theorem sobolevNLSHierarchyGradient_eq_classical (s k : ℕ) (hk : k ≤ s+1)
    (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) (j : ℤ) :
    ((sobolevNLSHierarchyGradient s k ab).1 j,
      (sobolevNLSHierarchyGradient s k ab).2 j) =
      (periodOneCoefficient (fun x => (classicalNLSHierarchyGradient a b k x).1) j,
        periodOneCoefficient (fun x => (classicalNLSHierarchyGradient a b k x).2) j) := by
  unfold sobolevNLSHierarchyGradient
  split_ifs with hs hmass
  · have hbound : (k-1 : ℕ) ≤ s := by omega
    apply Prod.ext
    · exact circleUnitCoefficients_eq_classical _ _
        (sobolevPolynomialL2_eq_classical s hs _
          ((nlsHierarchyEuler_derivativeOrder k false).mono (by omega))
          ab a b ha hb hpa hpb haq hbq) j
    · exact circleUnitCoefficients_eq_classical _ _
        (sobolevPolynomialL2_eq_classical s hs _
          ((nlsHierarchyEuler_derivativeOrder k true).mono (by omega))
          ab a b ha hb hpa hpb haq hbq) j
  · subst k
    simpa only [hierarchySobolevJetL2_apply, pow_zero, one_mul,
      classicalNLSHierarchyGradient_one] using Prod.ext (hbq j) (haq j)
  · have hk0 : k = 0 := by omega
    subst k
    have hz : periodOneCoefficient (fun _ : ℝ => (0 : ℂ)) j = 0 := by
      rw [periodOneCoefficient, ← unitFourierCoefficient_eq_fourierCoeffOn]
      simp [unitFourierCoefficient]
    simp [classicalNLSHierarchyGradient, nlsHamiltonianPolynomial, eulerDerivative,
      evaluate, hz]

end NLS.ZakharovShabat
