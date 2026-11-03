import NLS.DifferentialPolynomial.DifferentialRiccati
import NLS.DifferentialPolynomial.LogarithmicDerivative

/-! # Total derivatives of every odd scalar Riccati density

The logarithmic primitive is a finite polynomial at each order.
No convergence or vanishing of integrated coefficients is assumed.
-/

noncomputable section
namespace NLS.DifferentialPolynomial
variable {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]

/-- The scalar logarithm input formed from the two spatial orientations. -/
def scalarRiccatiLogInput (D : Derivation K A A) (q : A) : PowerSeries A :=
  PowerSeries.X * (differentialRiccatiSeries (-D) (-1) (-q) +
    differentialRiccatiSeries D (-1) (-q))

omit [CharZero K] in
theorem scalarRiccati_log_derivative_identity (D : Derivation K A A) (q : A) :
    powerSeriesDerivation D (scalarRiccatiLogInput D q) =
      -(differentialRiccatiSeries (-D) (-1) (-q) -
        differentialRiccatiSeries D (-1) (-q)) *
        (1+PowerSeries.X*scalarRiccatiLogInput D q) := by
  have hs := differentialRiccatiSeries_equation (-D) (-1) (-q)
  have ht := differentialRiccatiSeries_equation D (-1) (-q)
  simp only [powerSeriesDerivation_neg, neg_neg, map_neg, map_one] at hs ht
  simp only [scalarRiccatiLogInput, Derivation.leibniz, powerSeriesDerivation_X,
    smul_eq_mul, mul_zero, add_zero, map_add]
  linear_combination hs - ht

/-- Every odd scalar Riccati coefficient is an explicit total derivative. -/
theorem derivation_scalarRiccati_log_odd (D : Derivation K A A) (q : A) (m : ℕ) :
    D (logarithmicPrimitiveCoefficient (K := K) (scalarRiccatiLogInput D q) (2*m+1)) =
      -2 * differentialRiccatiSequence (-D) (-1) (-q) (2*m+1) := by
  let R := scalarRiccatiLogInput D q
  let V := PowerSeries.invOfUnit (1+PowerSeries.X*R) 1
  have hv : (1+PowerSeries.X*R)*V = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp)
  rw [derivation_logarithmicPrimitiveCoefficient D R V hv,
    scalarRiccati_log_derivative_identity]
  have he : (-(differentialRiccatiSeries (-D) (-1) (-q) -
        differentialRiccatiSeries D (-1) (-q)) * (1+PowerSeries.X*R))*V =
      -(differentialRiccatiSeries (-D) (-1) (-q) -
        differentialRiccatiSeries D (-1) (-q)) := by rw [mul_assoc, hv, mul_one]
  change PowerSeries.coeff (2*m+1) _ = _
  rw [he, map_neg, map_sub, coeff_differentialRiccatiSeries, coeff_differentialRiccatiSeries,
    differentialRiccatiSequence_neg_derivation]
  have hp : (-1 : A)^(2*m+1) = -1 := by
    rw [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
  rw [hp]
  ring

end NLS.DifferentialPolynomial
